/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Invariant

/-!
# Auxiliary security game

Let `Π := scheme kem onoff hDet ecEk ecCt0 ecCt1 leak` be Opp-UniKEM.
For a fixed challenge bit `b`, consider:

- `G_b`: the SCKA game for `Π`. Eligible challenges return real keys when `b = false`
  and independent uniform keys when `b = true`.
- `I_b`: the game `G_b` with A using B's recorded key in place of decapsulation.
  On ciphertext completion, A outputs `Key[B, t_A]`, where `t_A` is its current epoch,
  and erases its current secret material.

`idealSecurityExp … b adv` runs `I_b` against `adv` and returns its output bit.
This replacement lets the later KEM IND-CPA reduction simulate A's receive without
performing decapsulation.

With a correct online ciphertext erasure code, the real and auxiliary oracle computations
agree whenever `reachableInv` and `CurrentKEMCorrect` hold. The module `Endpoints` uses
this agreement to bound the difference between the output probabilities of `G_b` and `I_b`.
-/

open OracleSpec OracleComp KEMScheme ErasureCodePayload

namespace oppUniKemCKA.Security

variable {K PK SK C Sym : Type}

/-- A's receive oracle with `Decaps(dk_A, ct)` replaced by `Key[B, t_A]`, where `t_A`
is A's epoch before the receive. The ordinary receive handles the resulting key lookup. -/
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

/-- Uniform sampling, ordinary sends, and receives, with A's receive using B's recorded key
in place of decapsulation (`oracleRecvAIdeal`). -/
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

/-- Opp-UniKEM's security oracles with A's receive using B's recorded key in place of
decapsulation. Eligible challenges return real keys when `b = false` and independent
uniform keys when `b = true`. -/
def idealSecurityImpl
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (b : Bool) :
    QueryImpl (securitySpec leak Sym)
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp) :=
  SCKAScheme.securityImplOf (idealCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak)
    (SCKAScheme.oracleChall b _ _ _ _)
    (exposureA kem onoff leak) (exposureB kem onoff leak)
    (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)

/-- Run the auxiliary game `I_b` against `adv` from the initial state and return its
Boolean output. -/
def idealSecurityExp
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (b : Bool) (adv : SecurityAdversary leak Sym) : ProbComp Bool :=
  (simulateQ (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b) adv).run'
    (Reduction.Internal.initialGame kem onoff)

/-- With a correct online ciphertext erasure code, every real security query from a state
satisfying `reachableInv` and `CurrentKEMCorrect` equals the corresponding auxiliary query
with the same challenge bit, including its response and resulting state. -/
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
      (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b t).run s := by
  refine SCKAScheme.securityImplOf_run_eq _ _ _ _ _ _ _ s ?_ (fun _ => rfl) t
  intro t
  rcases t with ((((n | u) | u) | n) | n)
  all_goals simp only [idealCorrectnessImpl, SCKAScheme.sckaCorrectnessImpl,
    QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
  exact oracleRecvA_eq_ideal kem onoff hDet ecEk ecCt0 ecCt1 hCt1 leak n s hs hc

end oppUniKemCKA.Security
