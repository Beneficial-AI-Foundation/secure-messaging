/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.IdealGame
import SecureMessaging.SCKA.OppUniKEM.Security.CounterBound
import SecureMessaging.SCKA.Security.ExposureMonotone

/-!
# Recorded-epoch bounds in the auxiliary game

**Parameters.** Fix an Opp-UniKEM instance with deterministic decapsulation,
correct erasure codes, and on/off and leakage witnesses. Let
`mode : ℕ → Bool` select real (`false`) or uniform (`true`) challenge keys.
In the auxiliary game, A records B's encapsulated key on ciphertext completion.

**Statement.** For every

* adversary `A : SecurityAdversary leak Sym`,
* budget `q : ℕ` with `SecuritySendQueryBound A q`,
* pair `(g, s)` in the support of A's auxiliary execution from the initial state,
* epoch `t : ℕ`,

if `s.keyA t ≠ none ∨ s.keyB t ≠ none`, then `t ≤ q`.

**Proof.** Each query preserves `sendEpochInv` and increases A's send counter
by at most its cost in the four-send budget. Thus `s.nA ≤ q`.
Auxiliary transcript preservation and `recorded_epoch_le_sends` give
`t ≤ s.nA`.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- For every challenge mode, query, and state `s` satisfying
`sendEpochInv`, every supported auxiliary successor `s'` satisfies
`sendEpochInv s'`. -/
theorem idealSecurityImpl_preserves_sendEpochInv
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (mode : ℕ → Bool) :
    QueryImpl.PreservesInv (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode)
      sendEpochInv := by
  intro t s hs z hz
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n)
    · have hz' : ∃ r, (r, s) = z := by
        simpa [idealSecurityImpl, SCKAScheme.oracleUnif] using hz
      obtain ⟨_, rfl⟩ := hz'
      exact hs
    · exact oracleSendA_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak u s hs z hz
    · exact oracleSendB_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak u s hs z hz
    · exact oracleRecvA_preserves_sendEpochInv (keyDecapsKEM kem (s.keyB s.stA.t))
        (keyDecapsOnOff kem onoff (s.keyB s.stA.t)) (keyDecapsDet kem (s.keyB s.stA.t))
        ecEk ecCt0 ecCt1 (keyDecapsLeak kem onoff leak (s.keyB s.stA.t)) n s hs z hz
    · exact oracleRecvB_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak n s hs z hz
  · exact SCKAScheme.oracleSendArleak_preservesInv _ _ (sendArleak_forget kem onoff ecEk leak)
      sendEpochInv (fun _ _ h => h)
      (oracleSendA_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak) u s hs z hz
  · exact SCKAScheme.oracleSendBrleak_preservesInv _ _
      (sendBrleak_forget kem onoff ecCt0 ecCt1 leak)
      sendEpochInv (fun _ _ h => h)
      (oracleSendB_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak) u s hs z hz
  · exact SCKAScheme.oracleChall_preservesInv (mode t) sendEpochInv (fun _ _ h => h) t s hs z hz
  · exact SCKAScheme.oracleCorruptA_preservesInv (vulnA kem onoff) sendEpochInv
      (fun _ _ h => h) u s hs z hz
  · exact SCKAScheme.oracleCorruptB_preservesInv (vulnB kem onoff) sendEpochInv
      (fun _ _ h => h) u s hs z hz

/-- An auxiliary query increases A's send counter by at most one if it
is one of the four send queries; every other query has increment at most zero. -/
theorem idealSecurityImpl_sendCounter_step
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff)
    (mode : ℕ → Bool) (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (z : (securitySpec leak Sym).Range t ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support ((idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode t).run s)) :
    z.2.nA ≤ s.nA + if isSecuritySendQuery t then 1 else 0 := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n)
    · have hz' : ∃ r, (r, s) = z := by
        simpa [idealSecurityImpl, oracleRecvAIdeal,
          SCKAScheme.oracleUnif] using hz
      obtain ⟨_, rfl⟩ := hz'
      simp [isSecuritySendQuery]
    all_goals
      try change z ∈ support ((SCKAScheme.oracleRecvA
        (scheme (keyDecapsKEM kem (s.keyB s.stA.t))
          (keyDecapsOnOff kem onoff (s.keyB s.stA.t)) (keyDecapsDet kem (s.keyB s.stA.t))
          ecEk ecCt0 ecCt1 (keyDecapsLeak kem onoff leak (s.keyB s.stA.t))) n).run s) at hz
    all_goals
      simp only [idealSecurityImpl,
        QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, SCKAScheme.oracleSendA,
        SCKAScheme.oracleSendB, SCKAScheme.oracleRecvA, SCKAScheme.oracleRecvB,
        StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
        bind_assoc, pure_bind] at hz
    all_goals
      first
      | rw [mem_support_bind_iff] at hz
        obtain ⟨out, _, hz⟩ := hz
      | skip
    all_goals
      try dsimp only at hz
      repeat' split at hz
    all_goals
      simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
        mem_support_pure_iff] at hz
      obtain rfl := hz
      try cases u
      simp [isSecuritySendQuery]
  · cases u
    simp only [idealSecurityImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      SCKAScheme.oracleSendArleak, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      monadLift_self, bind_assoc, pure_bind] at hz
    rw [mem_support_bind_iff] at hz
    obtain ⟨out, _, hz⟩ := hz
    cases out with
    | none =>
      obtain rfl := (mem_support_pure_iff _ _).mp hz
      simp [isSecuritySendQuery]
    | some out =>
      rcases out with ⟨key, msg, epoch, state, coins⟩
      dsimp only at hz
      split at hz
      · obtain rfl := (mem_support_pure_iff _ _).mp hz
        simp [isSecuritySendQuery]
      · cases key <;> simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
          mem_support_pure_iff] at hz
        all_goals obtain rfl := hz; simp [isSecuritySendQuery]
  · cases u
    simp only [idealSecurityImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      SCKAScheme.oracleSendBrleak, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      monadLift_self, bind_assoc, pure_bind] at hz
    rw [mem_support_bind_iff] at hz
    obtain ⟨out, _, hz⟩ := hz
    cases out with
    | none =>
      obtain rfl := (mem_support_pure_iff _ _).mp hz
      simp [isSecuritySendQuery]
    | some out =>
      rcases out with ⟨key, msg, epoch, state, coins⟩
      dsimp only at hz
      split at hz
      · obtain rfl := (mem_support_pure_iff _ _).mp hz
        simp [isSecuritySendQuery]
      · cases key <;> simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
          mem_support_pure_iff] at hz
        all_goals obtain rfl := hz; simp [isSecuritySendQuery]
  all_goals
    simp only [isSecuritySendQuery, Bool.false_eq_true, ↓reduceIte, add_zero]
  · exact SCKAScheme.oracleChall_preservesInv (mode t) (fun state => state.nA ≤ s.nA)
      (fun _ _ h => h) t s (Nat.le_refl _) z hz
  · exact SCKAScheme.oracleCorruptA_preservesInv (vulnA kem onoff) (fun state => state.nA ≤ s.nA)
      (fun _ _ h => h) u s (Nat.le_refl _) z hz
  · exact SCKAScheme.oracleCorruptB_preservesInv (vulnB kem onoff) (fun state => state.nA ≤ s.nA)
      (fun _ _ h => h) u s (Nat.le_refl _) z hz

/-- Assume correct erasure codes. For every challenge mode `mode`,
adversary `adv` with send budget `q`, pair `(g, s)` supported by the auxiliary
execution from the initial state, and epoch `t : ℕ`,
`(s.keyA t).isSome ∨ (s.keyB t).isSome` implies `t ≤ q`. -/
-- ANCHOR: ideal_recorded_epoch_le
theorem ideal_recorded_epoch_le
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff) (mode : ℕ → Bool)
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q)
    (z : Bool × SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support ((simulateQ
      (idealSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak mode) adv).run
        (Reduction.Internal.initialGame kem onoff)))
    (t : ℕ) (hk : (z.2.keyA t).isSome ∨ (z.2.keyB t).isSome) : t ≤ q := by
  have hr := simulateQ_run_preservesInv _ _
    (idealSecurityImpl_preserves_reachableInv kem onoff hDet ecEk hEk ecCt0 hCt0
      ecCt1 hCt1 leak mode)
    adv (Reduction.Internal.initialGame kem onoff)
    (by
      simpa [Reduction.Internal.initialGame, Reduction.Internal.initialA,
        Reduction.Internal.initialB] using
          reachableInv_init kem onoff ecEk ecCt0 ecCt1 ecEk.ec.nchunk_pos ecCt0.ec.nchunk_pos) z hz
  have he := simulateQ_run_preservesInv _ _
    (idealSecurityImpl_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak mode)
    adv (Reduction.Internal.initialGame kem onoff) (sendEpochInv_init kem onoff) z hz
  have hcount := stateCounter_simulateQ_run_le _ (fun s => s.nA)
    (fun t => isSecuritySendQuery t = true)
    (idealSecurityImpl_sendCounter_step kem onoff hDet ecEk ecCt0 ecCt1 leak mode)
    adv q hq (Reduction.Internal.initialGame kem onoff) z hz
  apply (recorded_epoch_le_sends hr he t hk).trans
  simpa [Reduction.Internal.initialGame, SCKAScheme.initGameState] using hcount
-- ANCHOR_END: ideal_recorded_epoch_le

end oppUniKemCKA.Security
