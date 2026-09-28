/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.EpochBound
import SecureMessaging.SCKA.OppUniKEM.Security.Tracked
import ToVCVio.OracleComp.QueryTracking.StateBudget

/-!
# From send-query budgets to epoch bounds

**Counters.** `s.nA` counts successful A sends.
`SecuritySendQueryBound A q` counts calls to all four send oracles, including
rejected calls.

**Results.** For every security query `t` and supported successor `s'`,
`s'.nA ≤ s.nA + cost(t)`, where `cost` is one for sends and zero otherwise.
Consequently, every supported run of an adversary with budget `q` from the
initial state satisfies `nA ≤ q`. With correct erasure codes, every final
tracked state `(s, false)` additionally satisfies
`∀ t : ℕ, (s.keyA t ≠ none ∨ s.keyB t ≠ none) → t ≤ q`.

**Proof.** Apply the generic adaptive-counter bound, then combine
`EpochBound.recorded_epoch_le_sends` with the transcript invariant preserved
while the failure flag is false.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security

open Reduction.Internal

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Any full-security query increases A's successful-send counter by at
most one on a counted send and by zero on every other query. -/
theorem securityImpl_sendCounter_step
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (z : (securitySpec leak Sym).Range t ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support ((SCKAScheme.sckaSecurityImpl b (exposureA kem onoff leak)
      (exposureB kem onoff leak)
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) t).run s)) :
    z.2.nA ≤ s.nA + if isSecuritySendQuery t then 1 else 0 := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n)
    · have hz' : ∃ r, (r, s) = z := by
        simpa [SCKAScheme.sckaSecurityImpl, SCKAScheme.sckaCorrectnessImpl,
          SCKAScheme.oracleUnif] using hz
      obtain ⟨_, rfl⟩ := hz'
      simp [isSecuritySendQuery]
    all_goals
      simp only [SCKAScheme.sckaSecurityImpl, SCKAScheme.sckaCorrectnessImpl,
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
    simp only [SCKAScheme.sckaSecurityImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
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
    simp only [SCKAScheme.sckaSecurityImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
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
  · exact SCKAScheme.oracleChall_preservesInv b (fun state => state.nA ≤ s.nA)
      (fun _ _ h => h) t s (Nat.le_refl _) z hz
  · exact SCKAScheme.oracleCorruptA_preservesInv (vulnA kem onoff) (fun state => state.nA ≤ s.nA)
      (fun _ _ h => h) u s (Nat.le_refl _) z hz
  · exact SCKAScheme.oracleCorruptB_preservesInv (vulnB kem onoff) (fun state => state.nA ≤ s.nA)
      (fun _ _ h => h) u s (Nat.le_refl _) z hz

/-- A full-security execution with at most `q` ordinary or leaking sends
has at most `q` successful A sends on every supported execution path. -/
theorem security_sendCounter_le
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) (b : Bool)
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q)
    (z : Bool × SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support ((simulateQ (SCKAScheme.sckaSecurityImpl b (exposureA kem onoff leak)
      (exposureB kem onoff leak) (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) adv).run
        (initialGame kem onoff))) : z.2.nA ≤ q := by
  have h := stateCounter_simulateQ_run_le _ (fun s => s.nA)
    (fun t => isSecuritySendQuery t = true)
    (securityImpl_sendCounter_step kem onoff hDet ecEk ecCt0 ecCt1 leak b)
    adv q hq (initialGame kem onoff) z hz
  simpa [initialGame, SCKAScheme.initGameState] using h

/-- Assume correct erasure codes. For every fixed bit `b`, adversary
`adv` with send budget `q`, supported final tracked state `(s, false)`, and
epoch `t`, a present entry in `s.keyA t` or `s.keyB t` implies `t ≤ q`.
The false persistent flag certifies that all earlier failure tests were false. -/
-- ANCHOR: security_recorded_epoch_le
theorem security_recorded_epoch_le
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff) (b : Bool)
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q)
    (z : Bool × (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) × Bool))
    (hz : z ∈ support ((simulateQ
      (trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b) adv).run
        (initialGame kem onoff, false)))
    (hgood : z.2.2 = false) (t : ℕ)
    (hk : (z.2.1.keyA t).isSome ∨ (z.2.1.keyB t).isSome) : t ≤ q := by
  have hproj := trackedSecurity_run_project kem onoff hDet ecEk ecCt0 ecCt1 leak b
    adv (initialGame kem onoff, false)
  have hz' : (z.1, z.2.1) ∈ support ((simulateQ
      (SCKAScheme.sckaSecurityImpl b (exposureA kem onoff leak) (exposureB kem onoff leak)
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) adv).run (initialGame kem onoff)) := by
    rw [← hproj, support_map]
    exact ⟨z, hz, rfl⟩
  have hInv := simulateQ_run_preservesInv _ _
    (trackedSecurityImpl_preserves kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1 leak b)
    adv (initialGame kem onoff, false)
    (tracked_initial_inv kem onoff hDet ecEk ecCt0 ecCt1
      ecEk.ec.nchunk_pos ecCt0.ec.nchunk_pos) z hz
  have hr : reachableInv kem onoff ecEk ecCt0 ecCt1 z.2.1 := by
    rcases hInv with hb | ⟨hr, _⟩
    · simp [hgood] at hb
    · exact hr
  have hepoch := simulateQ_run_preservesInv _ _
    (securityImpl_preserves_sendEpochInv kem onoff hDet ecEk ecCt0 ecCt1 leak b)
    adv (initialGame kem onoff) (sendEpochInv_init kem onoff) (z.1, z.2.1) hz'
  exact (recorded_epoch_le_sends hr hepoch t hk).trans
    (security_sendCounter_le kem onoff hDet ecEk ecCt0 ecCt1 leak b adv q hq _ hz')
-- ANCHOR_END: security_recorded_epoch_le

end oppUniKemCKA.Security
