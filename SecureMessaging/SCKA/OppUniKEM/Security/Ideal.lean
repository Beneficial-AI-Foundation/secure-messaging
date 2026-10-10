/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Invariant

/-!
# Auxiliary security game

Let `Π := scheme kem onoff hDet ecEk ecCt0 ecCt1 leak` be Opp-UniKEM, and let
`mode : ℕ → Bool` select the epochs whose eligible challenges return uniform keys.

The auxiliary game replaces A's decapsulation result by B's recorded key for A's current
epoch. It retains the protocol's chunk processing, erasure, and exposure rules.
`idealSecurityExp mode adv` returns the adversary's output from this game, starting in the
initial state.

With correct erasure codes, auxiliary correctness queries preserve `reachableInv`.
If the online ciphertext erasure code is correct, real and auxiliary queries with the
same constant challenge mode have equal response/state computations whenever `reachableInv`
and `CurrentKEMCorrect` hold.
-/

open OracleSpec OracleComp KEMScheme ErasureCodePayload

namespace oppUniKemCKA.Security

variable {K PK SK C Sym : Type}

/-- A's auxiliary receive oracle: upon ciphertext completion, record B's encapsulated key
for A's current epoch, using the existing chunk-processing and erasure operations. -/
def oracleRecvAIdeal [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) :
    QueryImpl (ℕ →ₒ Option (ℕ × Option ℕ))
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp) :=
  fun n => do
    let s ← (get : StateT
      (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp
      (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)))
    (SCKAScheme.oracleRecvA (schemeWithDecaps kem onoff hDet ecEk ecCt0 ecCt1 leak
      (fun _ _ => s.keyB s.stA.t)) n)

/-- With correct ciphertext erasure codes, A's auxiliary receive preserves `reachableInv`. -/
theorem oracleRecvAIdeal_preserves_reachableInv [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff) :
    QueryImpl.PreservesInv (oracleRecvAIdeal kem onoff hDet ecEk ecCt0 ecCt1 leak)
      (reachableInv kem onoff ecEk ecCt0 ecCt1) := by
  intro n s hs z hz
  exact oracleRecvA_preserves_reachableInv_of_recv kem onoff ecEk ecCt0 hCt0
    ecCt1 hCt1 ecCt1.ec.nchunk_pos
    (schemeWithDecaps kem onoff hDet ecEk ecCt0 ecCt1 leak (fun _ _ => s.keyB s.stA.t))
    (fun _ _ => s.keyB s.stA.t) rfl n s hs (fun _ _ _ _ _ _ _ hk => hk) z hz

/-- A's auxiliary receive preserves `sendEpochInv`. -/
theorem oracleRecvAIdeal_preserves_sendEpochInv [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) :
    QueryImpl.PreservesInv (oracleRecvAIdeal kem onoff hDet ecEk ecCt0 ecCt1 leak)
      sendEpochInv := by
  intro n s hs z hz
  exact oracleRecvA_preserves_sendEpochInv_of_recv kem onoff ecCt0 ecCt1
    (schemeWithDecaps kem onoff hDet ecEk ecCt0 ecCt1 leak (fun _ _ => s.keyB s.stA.t))
    (fun _ _ => s.keyB s.stA.t) rfl n s hs z hz

/-- Two decapsulation functions give equal A-receive computations on a fixed state and
message if they agree on every decapsulation reached by that receive. -/
theorem recvA_eq_of_decaps_agrees [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (decaps decaps' : SK → C → Option K)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : StA onoff Sym) (msg : Message Sym)
    (hdec : ∀ dk ct0 ch ct1 ack,
      s.dkA = some dk → s.ct0 = some ct0 →
      msg = (some ch, ack, s.t, some 1) →
      ecCt1.decode (insert ch s.lch) = some ct1 →
      decaps dk (onoff.split.symm (ct0, ct1)) = decaps' dk (onoff.split.symm (ct0, ct1))) :
    recvA kem onoff decaps ecCt0 ecCt1 s msg =
      recvA kem onoff decaps' ecCt0 ecCt1 s msg := by
  rcases msg with ⟨ch, ack, t, bit⟩
  by_cases ht : t = s.t
  · subst t
    cases hc : ch with
    | none =>
      cases hct : s.ct0 <;> simp [recvA, hct]
    | some chunk =>
      cases hb : bit with
      | none =>
        cases hct : s.ct0 <;> simp [recvA, hct]
      | some bit =>
        fin_cases bit
        · cases hct : s.ct0 <;> cases hdecode : ecCt0.decode (insert chunk s.lch) <;>
            simp [recvA, hct, hdecode]
        · cases hd : s.dkA with
          | none => cases hct : s.ct0 <;> simp [recvA, hd, hct]
          | some dk =>
            cases hct : s.ct0 with
            | none => simp [recvA, hd, hct]
            | some ct0 =>
              cases hct1 : ecCt1.decode (insert chunk s.lch) with
              | none => simp [recvA, hd, hct, hct1]
              | some ct1 =>
                have heq := hdec dk ct0 chunk ct1 ack hd hct
                  (by simp [hc, hb]) hct1
                simp [recvA, hd, hct, hct1, heq]
  · have ht' : s.t ≠ t := Ne.symm ht
    simp [recvA, ht']

/-- With a correct online ciphertext erasure code, every decapsulation reached by an
honestly sent message returns B's recorded key when `reachableInv` and `CurrentKEMCorrect` hold. -/
theorem honest_recvA_decapsulation_eq_recorded [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (hc : CurrentKEMCorrect kem onoff hDet s)
    (n : ℕ) (msg : Message Sym) (epoch : ℕ) (hentry : s.msgB n = some (msg, epoch))
    (dk : SK) (ct0 : onoff.C₀) (ch : ℕ × Sym) (ct1 : onoff.C₁) (ack : Ack)
    (hdk : s.stA.dkA = some dk) (hct0 : s.stA.ct0 = some ct0)
    (hmsg : msg = (some ch, ack, s.stA.t, some 1))
    (hdecode : ecCt1.decode (insert ch s.stA.lch) = some ct1) :
    hDet.decapsDet dk (onoff.split.symm (ct0, ct1)) = s.keyB s.stA.t := by
  obtain ⟨T, hT⟩ := hs
  subst msg
  have hhon := hT.msgB n _ hentry
  obtain ⟨online, key, i, hon, hch⟩ : ∃ online key i,
      (T s.stA.t).on = some (online, key) ∧ ch = ecCt1.encode online i := by
    simpa [HonestMessageB] using hhon.2
  obtain ⟨_, I, hlch, hcard⟩ :
      (∃ st, (T s.stA.t).off = some (st, ct0)) ∧
      ∃ I, s.stA.lch = payloadChunks ecCt1 online I ∧ I.card < ecCt1.ec.nchunk := by
    simpa [ChunksAConsistent, hct0, hon] using hT.chunksA
  have hstep := decode_insert_honest ecCt1 hCt1 online I i hcard
  have heq : online = ct1 := by
    rw [hch, hlch] at hdecode
    rcases hstep with ⟨_, hn⟩ | ⟨_, hsome⟩
    · simp [hn] at hdecode
    · exact Option.some.inj (hsome.symm.trans hdecode)
  subst ct1
  have htbound := hT.msgBEpoch n _ epoch hentry
  change s.stA.t ≤ s.stB.t at htbound
  have htAB := Nat.le_antisymm htbound hT.epochs.1
  have hct1B : s.stB.ct1 = some online := by
    have h := hT.onB
    rw [← htAB, hon] at h
    exact h.symm
  have hk : s.keyB s.stA.t = some key := by
    rw [hT.keyB]
    simp [EpochTranscript.key, hon]
  exact (hc dk ct0 online key hdk hct0 hct1B hk).trans hk.symm

/-- Assume a correct online-component erasure code. For every state `s`
satisfying `reachableInv` and `CurrentKEMCorrect`, and delivery index `n`,
the real and auxiliary A-receive response/state computations from `s` are equal. -/
theorem oracleRecvA_eq_ideal [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff)
    (n : ℕ) (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (hc : CurrentKEMCorrect kem onoff hDet s) :
    (SCKAScheme.oracleRecvA (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) n).run s =
      (oracleRecvAIdeal kem onoff hDet ecEk ecCt0 ecCt1 leak n).run s := by
  change (SCKAScheme.oracleRecvA _ n).run s =
    (SCKAScheme.oracleRecvA (schemeWithDecaps kem onoff hDet ecEk ecCt0 ecCt1 leak
      (fun _ _ => s.keyB s.stA.t)) n).run s
  cases hentry : s.msgB n with
  | none => simp [SCKAScheme.oracleRecvA, hentry]
  | some entry =>
    rcases entry with ⟨msg, epoch⟩
    have heq := recvA_eq_of_decaps_agrees kem onoff hDet.decapsDet (fun _ _ => s.keyB s.stA.t)
      ecCt0 ecCt1 s.stA msg
      (honest_recvA_decapsulation_eq_recorded kem onoff hDet ecEk ecCt0 ecCt1 hCt1
        s hs hc n msg epoch hentry)
    simp only [SCKAScheme.oracleRecvA, scheme, schemeWithDecaps, StateT.run_bind,
      StateT.run_get, pure_bind, hentry, heq]

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- The correctness oracles of Opp-UniKEM with A's receive replaced by `oracleRecvAIdeal`. -/
def idealCorrectnessImpl
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) :
    QueryImpl (SCKAScheme.sckaCorrectnessSpec (Message Sym))
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp) :=
  let scka := scheme kem onoff hDet ecEk ecCt0 ecCt1 leak
  SCKAScheme.oracleUnif (StA onoff Sym) (StB onoff Sym) K (Message Sym)
    + SCKAScheme.oracleSendA scka + SCKAScheme.oracleSendB scka
    + oracleRecvAIdeal kem onoff hDet ecEk ecCt0 ecCt1 leak + SCKAScheme.oracleRecvB scka

/-- The auxiliary game with challenge mode `mode`: the security oracle family over
`idealCorrectnessImpl`, with Opp-UniKEM's exposure policies. -/
def idealSecurityImpl
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (mode : ℕ → Bool) :
    QueryImpl (securitySpec leak Sym)
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp) :=
  SCKAScheme.securityImplOf (idealCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak)
    (SCKAScheme.challOf mode)
    (exposureA kem onoff leak) (exposureB kem onoff leak)
    (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)

/-- The adversary's Boolean output in the auxiliary game with challenge mode `mode`,
starting from the initial state. -/
def idealSecurityExp
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (mode : ℕ → Bool) (adv : SecurityAdversary leak Sym) : ProbComp Bool :=
  (simulateQ (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode) adv).run'
    (Reduction.Internal.initialGame kem onoff)

omit [SampleableType K] in
/-- Every auxiliary correctness query keeps the exposed and challenged sets. -/
theorem idealCorrectnessImpl_securitySets_eq
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (z : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Range t ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support ((idealCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak t).run s)) :
    z.2.exposed = s.exposed ∧ z.2.challenged = s.challenged := by
  rcases t with ((((n | u) | u) | n) | n)
  all_goals simp only [idealCorrectnessImpl,
    QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hz
  · exact SCKAScheme.correctnessImpl_securitySets_eq
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) (SCKAScheme.sckaCorrectnessSpec.OUnif n) s z hz
  · cases u
    exact SCKAScheme.correctnessImpl_securitySets_eq
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) SCKAScheme.sckaCorrectnessSpec.OSendA s z hz
  · cases u
    exact SCKAScheme.correctnessImpl_securitySets_eq
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) SCKAScheme.sckaCorrectnessSpec.OSendB s z hz
  · exact SCKAScheme.correctnessImpl_securitySets_eq
      (schemeWithDecaps kem onoff hDet ecEk ecCt0 ecCt1 leak (fun _ _ => s.keyB s.stA.t))
      (SCKAScheme.sckaCorrectnessSpec.ORecvA n) s z hz
  · exact SCKAScheme.correctnessImpl_securitySets_eq
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) (SCKAScheme.sckaCorrectnessSpec.ORecvB n) s z hz

omit [SampleableType K] in
/-- Every auxiliary correctness query advances A's send counter by at most one on send
queries and not otherwise. -/
theorem idealCorrectnessImpl_nA_step
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (z : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Range t ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support ((idealCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak t).run s)) :
    z.2.nA ≤ s.nA + if SCKAScheme.isSendQuery t then 1 else 0 := by
  rcases t with ((((n | u) | u) | n) | n)
  all_goals simp only [idealCorrectnessImpl,
    QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hz
  · exact SCKAScheme.correctnessImpl_nA_step
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) (SCKAScheme.sckaCorrectnessSpec.OUnif n) s z hz
  · cases u
    exact SCKAScheme.correctnessImpl_nA_step (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)
      SCKAScheme.sckaCorrectnessSpec.OSendA s z hz
  · cases u
    exact SCKAScheme.correctnessImpl_nA_step (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)
      SCKAScheme.sckaCorrectnessSpec.OSendB s z hz
  · exact SCKAScheme.correctnessImpl_nA_step
      (schemeWithDecaps kem onoff hDet ecEk ecCt0 ecCt1 leak (fun _ _ => s.keyB s.stA.t))
      (SCKAScheme.sckaCorrectnessSpec.ORecvA n) s z hz
  · exact SCKAScheme.correctnessImpl_nA_step
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) (SCKAScheme.sckaCorrectnessSpec.ORecvB n) s z hz

omit [SampleableType K] in
/-- With correct erasure codes, every auxiliary correctness query preserves `reachableInv`. -/
theorem idealCorrectnessImpl_preserves_reachableInv
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff) :
    QueryImpl.PreservesInv (idealCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak)
      (reachableInv kem onoff ecEk ecCt0 ecCt1) := by
  intro t s hs z hz
  rcases t with ((((n | u) | u) | n) | n)
  · exact SCKAScheme.oracleUnif_preservesInv _ n s hs z hz
  · exact oracleSendA_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt1 leak
      ecEk.ec.nchunk_pos u s hs z hz
  · exact oracleSendB_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt0.ec.nchunk_pos
      ecCt1 ecCt1.ec.nchunk_pos leak u s hs z hz
  · exact oracleRecvAIdeal_preserves_reachableInv kem onoff hDet ecEk ecCt0 hCt0 ecCt1 hCt1
      leak n s hs z hz
  · exact oracleRecvB_preserves_reachableInv kem onoff hDet ecEk hEk ecEk.ec.nchunk_pos
      ecCt0 ecCt1 leak n s hs z hz

/-- With a correct online ciphertext erasure code, every real security query from a state
satisfying `reachableInv` and `CurrentKEMCorrect` equals the corresponding auxiliary query
with the same constant challenge mode as a response/state computation. -/
theorem securityImpl_eq_ideal_of_current
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (hc : CurrentKEMCorrect kem onoff hDet s) :
    (SCKAScheme.sckaSecurityImpl b (exposureA (Sym := Sym) kem onoff leak)
      (exposureB (Sym := Sym) kem onoff leak)
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) t).run s =
      (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak (fun _ => b) t).run s := by
  refine SCKAScheme.securityImplOf_run_eq _ _ _ _ _ _ _ s ?_ (fun _ => rfl) t
  intro t
  rcases t with ((((n | u) | u) | n) | n)
  all_goals simp only [idealCorrectnessImpl, SCKAScheme.sckaCorrectnessImpl,
    QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
  exact oracleRecvA_eq_ideal kem onoff hDet ecEk ecCt0 ecCt1 hCt1 leak n s hs hc

end oppUniKemCKA.Security
