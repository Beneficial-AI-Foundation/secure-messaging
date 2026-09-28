/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.IdealGame

/-!
# Unavailable epoch-zero keys

**Assumptions.** Fix deterministic decapsulation, correct erasure codes,
and on/off and leakage witnesses.

**Statement.** For every challenge mode `mode : ℕ → Bool`, adversary `A`,
and supported output/state pair `(g, s)` of the auxiliary execution from
the initial state, `s.keyA 0 = none ∧ s.keyB 0 = none`.

**Proof.** The protocol starts in epoch one. Transcript consistency gives
A's empty entry at zero. B's sends record keys at B's positive current epoch.
The invariant `zeroEpochInv` combines the transcript with `keyB 0 = none`;
each oracle preserves it, with leaking sends handled by their marginals.
Together with `IdealBounds`, this restricts available challenge epochs to
`1, …, q` for an adversary with send budget `q`.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security

variable {K PK SK C Sym : Type}

/-- For every input state `s` and supported successful B-send output
containing an epoch/key pair `(t, k)`, `t = s.t`. -/
theorem sendB_key_epoch
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (s : StB onoff Sym)
    (key : K) (t epoch : ℕ) (msg : Message Sym) (s' : StB onoff Sym)
    (hout : some (some (t, key), msg, epoch, s') ∈
      support (sendB kem onoff ecCt0 ecCt1 s)) : t = s.t := by
  cases hct0 : s.ct0 <;> cases hek : s.ekA <;> cases hct1 : s.ct1 <;>
    cases hst : s.stCt <;> cases hack : s.ack.ctRec <;>
    simp [sendB, hct0, hek, hct1, hst, hack] at hout
  all_goals aesop

/-- B's ordinary send preserves an empty epoch-zero key-table entry if
B's current epoch is positive. -/
theorem oracleSendB_preserves_keyB_zero [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (u : Unit) (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hpos : 0 < s.stB.t) (hzero : s.keyB 0 = none)
    (z : Option (ℕ × Option ℕ × Message Sym) ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support ((SCKAScheme.oracleSendB
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) u).run s)) : z.2.keyB 0 = none := by
  cases u
  simp only [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc] at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨out, hout, hz⟩ := hz
  cases out with
  | none => simpa using (mem_support_pure_iff _ _).mp hz ▸ hzero
  | some out =>
    rcases out with ⟨key, msg, epoch, state⟩
    cases key with
    | none =>
      simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
        mem_support_pure_iff] at hz
      obtain rfl := hz
      exact hzero
    | some key =>
      rcases key with ⟨t, key⟩
      have ht := sendB_key_epoch kem onoff ecCt0 ecCt1 s.stB key t epoch msg state hout
      simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
        mem_support_pure_iff] at hz
      obtain rfl := hz
      have hne : 0 ≠ t := by omega
      simpa [Function.update_of_ne hne] using hzero

/-- For every state with `keyB 0 = none`, ordinary A-send, A-receive,
and B-receive preserve that equality. The first two retain B's key table;
the Opp-UniKEM B-receive algorithm returns `none` as its optional key. -/
theorem nonSendB_preserves_keyB_zero [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) :
    QueryImpl.PreservesInv (SCKAScheme.oracleSendA
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) (fun s => s.keyB 0 = none) ∧
    QueryImpl.PreservesInv (SCKAScheme.oracleRecvA
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) (fun s => s.keyB 0 = none) ∧
    QueryImpl.PreservesInv (SCKAScheme.oracleRecvB
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) (fun s => s.keyB 0 = none) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u s hs z hz
    cases u
    simp only [SCKAScheme.oracleSendA, StateT.run_bind, StateT.run_get, pure_bind,
      StateT.run_monadLift, monadLift_self, bind_assoc, mem_support_bind_iff] at hz
    obtain ⟨out, _, hz⟩ := hz
    cases out with
    | none => simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
    | some out =>
      rcases out with ⟨key, msg, epoch, state⟩
      cases key <;>
        simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
          mem_support_pure_iff] at hz
      all_goals obtain rfl := hz; exact hs
  · intro n s hs z hz
    simp only [SCKAScheme.oracleRecvA, StateT.run_bind, StateT.run_get, pure_bind] at hz
    repeat' split at hz
    all_goals
      simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
        mem_support_pure_iff] at hz
      obtain rfl := hz
      exact hs
  · intro n s hs z hz
    simp only [SCKAScheme.oracleRecvB, scheme, StateT.run_bind, StateT.run_get, pure_bind] at hz
    cases hm : s.msgA n with
    | none =>
      have hz' : z = (none, s) := by simpa [hm] using hz
      obtain rfl := hz'
      exact hs
    | some entry =>
      rcases entry with ⟨msg, epoch⟩
      simp only [hm, recvB, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
        mem_support_pure_iff] at hz
      obtain rfl := hz
      exact hs

/-- The auxiliary correctness transcript together with an empty epoch-zero
entry in B's key table. A's epoch-zero entry is already excluded by the
transcript's characterization of A's key table. -/
def zeroEpochInv (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) : Prop :=
  reachableInv kem onoff ecEk ecCt0 ecCt1 s ∧ s.keyB 0 = none

/-- With correct erasure codes, for every challenge mode, query, and
state `s` satisfying `zeroEpochInv`, every supported auxiliary successor
satisfies it. This retains transcript consistency and `keyB 0 = none`. -/
theorem idealSecurityImpl_preserves_zeroEpochInv
    [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff) (mode : ℕ → Bool) :
    QueryImpl.PreservesInv (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode)
      (zeroEpochInv kem onoff ecEk ecCt0 ecCt1) := by
  have hsendA : QueryImpl.PreservesInv
      (SCKAScheme.oracleSendA (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak))
      (zeroEpochInv kem onoff ecEk ecCt0 ecCt1) := by
    intro u s hs z hz
    exact ⟨oracleSendA_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt1 leak
        ecEk.ec.nchunk_pos u s hs.1 z hz,
      (nonSendB_preserves_keyB_zero kem onoff hDet ecEk ecCt0 ecCt1 leak).1 u s hs.2 z hz⟩
  have hsendB : QueryImpl.PreservesInv
      (SCKAScheme.oracleSendB (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak))
      (zeroEpochInv kem onoff ecEk ecCt0 ecCt1) := by
    intro u s hs z hz
    obtain ⟨T, hT⟩ := hs.1
    exact ⟨oracleSendB_preserves_reachableInv kem onoff hDet ecEk ecCt0 ecCt0.ec.nchunk_pos
        ecCt1 ecCt1.ec.nchunk_pos leak u s ⟨T, hT⟩ z hz,
      oracleSendB_preserves_keyB_zero kem onoff hDet ecEk ecCt0 ecCt1 leak
        u s hT.epochPosB hs.2 z hz⟩
  have hbook : ∀ s exposed, zeroEpochInv kem onoff ecEk ecCt0 ecCt1 s →
      zeroEpochInv kem onoff ecEk ecCt0 ecCt1 { s with exposed := exposed } := by
    intro s exposed hs
    exact ⟨reachableInv_with_security_bookkeeping hs.1 exposed s.challenged, hs.2⟩
  intro t s hs z hz
  refine ⟨idealSecurityImpl_preserves_reachableInv kem onoff hDet ecEk hEk ecCt0 hCt0
    ecCt1 hCt1 leak mode t s hs.1 z hz, ?_⟩
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n)
    · have hz' : ∃ r, (r, s) = z := by
        simpa [idealSecurityImpl, SCKAScheme.oracleUnif] using hz
      obtain ⟨_, rfl⟩ := hz'
      exact hs.2
    · exact (hsendA u s hs z hz).2
    · exact (hsendB u s hs z hz).2
    · exact (nonSendB_preserves_keyB_zero (keyDecapsKEM kem (s.keyB s.stA.t))
        (keyDecapsOnOff kem onoff (s.keyB s.stA.t)) (keyDecapsDet kem (s.keyB s.stA.t))
        ecEk ecCt0 ecCt1 (keyDecapsLeak kem onoff leak (s.keyB s.stA.t))).2.1 n s hs.2 z hz
    · exact (nonSendB_preserves_keyB_zero kem onoff hDet ecEk ecCt0 ecCt1 leak).2.2 n s hs.2 z hz
  · exact (SCKAScheme.oracleSendArleak_preservesInv _ _ (sendArleak_forget kem onoff ecEk leak)
      _ hbook hsendA u s hs z hz).2
  · exact (SCKAScheme.oracleSendBrleak_preservesInv _ _
      (sendBrleak_forget kem onoff ecCt0 ecCt1 leak) _ hbook hsendB u s hs z hz).2
  · exact SCKAScheme.oracleChall_preservesInv (mode t) (fun state => state.keyB 0 = none)
      (fun _ _ h => h) t s hs.2 z hz
  · exact SCKAScheme.oracleCorruptA_preservesInv (vulnA kem onoff)
      (fun state => state.keyB 0 = none) (fun _ _ h => h) u s hs.2 z hz
  · exact SCKAScheme.oracleCorruptB_preservesInv (vulnB kem onoff)
      (fun state => state.keyB 0 = none) (fun _ _ h => h) u s hs.2 z hz

/-- Every supported auxiliary execution has `keyA 0 = none` and
`keyB 0 = none`. Thus `Chall(0)` is unavailable in every hybrid, including after
arbitrary delivery, corruption, and randomness-leaking sends. -/
theorem ideal_run_key_zero
    [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff) (mode : ℕ → Bool)
    {α : Type} (adv : OracleComp (securitySpec leak Sym) α)
    (z : α × SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support ((simulateQ
      (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode) adv).run
        (Reduction.Internal.initialGame kem onoff))) :
    z.2.keyA 0 = none ∧ z.2.keyB 0 = none := by
  have hi : zeroEpochInv kem onoff ecEk ecCt0 ecCt1
      (Reduction.Internal.initialGame kem onoff) := by
    constructor
    · simpa [Reduction.Internal.initialGame, Reduction.Internal.initialA,
        Reduction.Internal.initialB] using
          reachableInv_init kem onoff ecEk ecCt0 ecCt1 ecEk.ec.nchunk_pos ecCt0.ec.nchunk_pos
    · rfl
  have h := simulateQ_run_preservesInv _ _
    (idealSecurityImpl_preserves_zeroEpochInv kem onoff hDet ecEk hEk ecCt0 hCt0
      ecCt1 hCt1 leak mode)
    adv (Reduction.Internal.initialGame kem onoff) hi z hz
  refine ⟨?_, h.2⟩
  obtain ⟨T, hT⟩ := h.1
  simp [hT.keyA]

end oppUniKemCKA.Security
