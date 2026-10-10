/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Invariant
import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction.Projection
import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction.Composition
import ToVCVio.OracleComp.SimSemantics.StateT.ExpectedPayoffBound

/-!
# KEM-failure probability in the security game

Let `Π := scheme kem onoff hDet ecEk ecCt0 ecCt1 leak` be Opp-UniKEM with deterministic
decapsulation and correct erasure codes. Let `ε := kem.correctnessError ProbCompRuntime.probComp`
be the probability that an honest KEM encapsulation fails to decapsulate to its shared key.

For each challenge bit `b`, `trackedSecurityImpl b` extends the security game with a flag
`bad`, initially false. A query sets the flag when its successor contains completed KEM
material whose decapsulation disagrees with B's recorded key. Once set, the flag persists
through subsequent queries and erasures. Dropping the flag gives the original security
execution.

Let `V := currentFailurePotential` be the failure potential of unfinished KEM material
from the correctness proof, and let `Φ(s, bad) := if bad then 1 else V(s)` be the tracked
score. The potential is zero when the current epoch has no sampled material or is complete.
From a state satisfying `trackedInv`, each query increases the expected score by at most
`ε` for a send, and by zero otherwise.

For every adversary `adv` with `SecuritySendQueryBound adv q`,
`kem_failure_probability_le` proves `Pr[bad_final = true] ≤ q · ε`.
-/

open OracleSpec OracleComp KEMScheme ENNReal

namespace oppUniKemCKA.Security

open Reduction.Internal

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- The flag update of the tracked games: `bad' = bad || currentKEMFailure s'`. -/
def failureFlagUpdate (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) {leak : kem.OnOffRandLeak onoff}
    (t : (securitySpec leak Sym).Domain)
    (_ : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (_ : (securitySpec leak Sym).Range t)
    (s' : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) (bad : Bool) :
    Bool :=
  bad || currentKEMFailure kem onoff hDet s'

/-- The security game with constant mode `b`, extended by the persistent failure flag. -/
def trackedSecurityImpl
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) (b : Bool) :
    QueryImpl (securitySpec leak Sym)
      (StateT
        (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) × Bool)
        ProbComp) :=
  QueryImpl.extendState
    (SCKAScheme.sckaSecurityImpl b (exposureA kem onoff leak) (exposureB kem onoff leak)
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak))
    (failureFlagUpdate kem onoff hDet)

/-- Dropping the failure flag from a tracked execution gives the execution of the security
game with constant mode `b`. -/
theorem trackedSecurity_run_project
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) (b : Bool)
    {α : Type} (adv : OracleComp (securitySpec leak Sym) α)
    (p : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) × Bool) :
    Prod.map id Prod.fst <$>
        (simulateQ (trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b) adv).run p =
      (simulateQ (SCKAScheme.sckaSecurityImpl b (exposureA kem onoff leak)
        (exposureB kem onoff leak)
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) adv).run p.1 :=
  extendState_run_proj_eq _ _ adv p.1 p.2

/-- Once the failure flag is set, every tracked successor has it set. -/
theorem trackedSecurityImpl_preserves_bad
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : kem.OnOffRandLeak onoff) (b : Bool) :
    QueryImpl.PreservesInv (trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b)
      (fun p => p.2 = true) := by
  intro t p hp z hz
  rw [trackedSecurityImpl, QueryImpl.extendState_apply, mem_support_bind_iff] at hz
  obtain ⟨y, _, hz⟩ := hz
  obtain rfl := (mem_support_pure_iff _ _).mp hz
  simp [failureFlagUpdate, hp]

/-- With correct erasure codes, every tracked security query preserves `trackedInv`: either
a failure has been recorded, or `reachableInv` holds and `currentKEMFailure` is false. -/
theorem trackedSecurityImpl_preserves
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff) (b : Bool) :
    QueryImpl.PreservesInv (trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b)
      (trackedInv kem onoff hDet ecEk ecCt0 ecCt1) := by
  intro t p hp z hz
  change z ∈ support (do
    let y ← (SCKAScheme.sckaSecurityImpl b (exposureA kem onoff leak) (exposureB kem onoff leak)
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) t).run p.1
    pure (y.1, (y.2, p.2 || currentKEMFailure kem onoff hDet y.2))) at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  simp only [mem_support_pure_iff] at hz
  subst z
  rcases hp with hbad | ⟨hreach, hfail⟩
  · left
    simp [hbad]
  have hc := currentKEMFailure_eq_false_implies_current kem onoff hDet ecEk ecCt0 ecCt1
    p.1 hreach hfail
  have hreach' := securityImpl_preserves_reachableInv kem onoff hDet ecEk hEk
    ecCt0 hCt0 ecCt1 hCt1 leak b t p.1 hreach hc y hy
  cases hbad : currentKEMFailure kem onoff hDet y.2
  · exact Or.inr ⟨hreach', hbad⟩
  · exact Or.inl (by simp)

/-- For every fixed bit and state `s` satisfying `reachableInv` and
`currentKEMFailure(s) = false`, A's leaking send from `(s, false)` has
expected tracked failure score at most its initial score plus
`factorCorrectnessError kem onoff`. -/
theorem tracked_sendArleak_score_le
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : kem.OnOffRandLeak onoff) (b : Bool)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (hf : currentKEMFailure kem onoff hDet s = false) :
    expectedPayoff
      ((trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b
        SCKAScheme.sckaSecuritySpec.OSendArleak).run (s, false))
      (fun z => trackedFailureScore kem onoff z.2) ≤
      trackedFailureScore kem onoff (s, false) + factorCorrectnessError kem onoff := by
  change expectedPayoff (do
    let y ← (SCKAScheme.oracleSendArleak vulnRleakA
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s
    pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2))) _ ≤ _
  rw [bind_pure_comp, expectedPayoff_map]
  apply SCKAScheme.oracleSendArleak_expectedPayoff_le
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) vulnRleakA
      (sendArleak_forget kem onoff ecEk leak) s (leakEpochsA s.stA)
      (score := fun state => trackedFailureScore kem onoff
        (state, false || currentKEMFailure kem onoff hDet state))
      (c := trackedFailureScore kem onoff (s, false) + factorCorrectnessError kem onoff)
  · intro key msg epoch state coins hout
    exact sendArleak_exposure kem onoff ecEk leak s.stA
      _ hout key msg epoch state coins rfl
  · intro state exposed
    rfl
  · simp [hf]
  · have h := tracked_sendA_score_le kem onoff hDet ecEk ecCt0 ecCt1 leak s hs hf
    change expectedPayoff (do
      let y ← (SCKAScheme.oracleSendA
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s
      pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2))) _ ≤ _ at h
    simpa only [bind_pure_comp, expectedPayoff_map] using h

/-- For every fixed bit and state `s` satisfying `reachableInv` and
`currentKEMFailure(s) = false`, B's leaking send from `(s, false)` has
expected tracked failure score at most its initial score plus
`factorCorrectnessError kem onoff`. -/
theorem tracked_sendBrleak_score_le
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : kem.OnOffRandLeak onoff) (b : Bool)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (hf : currentKEMFailure kem onoff hDet s = false) :
    expectedPayoff
      ((trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b
        SCKAScheme.sckaSecuritySpec.OSendBrleak).run (s, false))
      (fun z => trackedFailureScore kem onoff z.2) ≤
      trackedFailureScore kem onoff (s, false) + factorCorrectnessError kem onoff := by
  change expectedPayoff (do
    let y ← (SCKAScheme.oracleSendBrleak vulnRleakB
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s
    pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2))) _ ≤ _
  rw [bind_pure_comp, expectedPayoff_map]
  apply SCKAScheme.oracleSendBrleak_expectedPayoff_le
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) vulnRleakB
      (sendBrleak_forget kem onoff ecCt0 ecCt1 leak) s (leakEpochsB s.stB)
      (score := fun state => trackedFailureScore kem onoff
        (state, false || currentKEMFailure kem onoff hDet state))
      (c := trackedFailureScore kem onoff (s, false) + factorCorrectnessError kem onoff)
  · intro key msg epoch state coins hout
    exact sendBrleak_exposure kem onoff ecCt0 ecCt1 leak s.stB
      _ hout key msg epoch state coins rfl
  · intro state exposed
    rfl
  · simp [hf]
  · have h := tracked_sendB_score_le kem onoff hDet ecEk ecCt0 ecCt1 leak s hs hf
    change expectedPayoff (do
      let y ← (SCKAScheme.oracleSendB
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s
      pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2))) _ ≤ _ at h
    simpa only [bind_pure_comp, expectedPayoff_map] using h

/-- For every bit `b`, query `t`, and tracked state `p` satisfying `trackedInv`,
the expected successor score is at most its initial value plus `factorCorrectnessError kem onoff`
for a send, and plus zero otherwise. -/
theorem trackedSecurity_score_step_le
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : kem.OnOffRandLeak onoff) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (p : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) × Bool)
    (hp : trackedInv kem onoff hDet ecEk ecCt0 ecCt1 p) :
    expectedPayoff ((trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b t).run p)
      (fun z => trackedFailureScore kem onoff z.2) ≤
      trackedFailureScore kem onoff p +
        if SCKAScheme.sckaSecuritySpec.isSendQuery t then factorCorrectnessError kem onoff
        else 0 := by
  by_cases hbad : p.2 = true
  · refine (expectedPayoff_le_one _ _ ?_).trans ?_
    · intro z
      exact trackedFailureScore_le_one kem onoff z.2
    · simp [trackedFailureScore, hbad]
  have hfalse : p.2 = false := Bool.eq_false_iff.mpr hbad
  have hgood : reachableInv kem onoff ecEk ecCt0 ecCt1 p.1 ∧
      currentKEMFailure kem onoff hDet p.1 = false := by
    rcases hp with hp | hp
    · exact False.elim (hbad hp)
    · exact hp
  have hpEq : p = (p.1, false) := Prod.ext rfl hfalse
  rw [hpEq]
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rw [SCKAScheme.sckaSecuritySpec.isSendQuery_OCorrectness]
    exact tracked_score_step_le kem onoff hDet ecEk ecCt0 ecCt1 leak t (p.1, false)
      (Or.inr hgood)
  · cases u
    simpa only [SCKAScheme.sckaSecuritySpec.isSendQuery, ↓reduceIte] using
      tracked_sendArleak_score_le kem onoff hDet ecEk ecCt0 ecCt1 leak b p.1 hgood.1 hgood.2
  · cases u
    simpa only [SCKAScheme.sckaSecuritySpec.isSendQuery, ↓reduceIte] using
      tracked_sendBrleak_score_le kem onoff hDet ecEk ecCt0 ecCt1 leak b p.1 hgood.1 hgood.2
  all_goals
    simp only [SCKAScheme.sckaSecuritySpec.isSendQuery, Bool.false_eq_true, ↓reduceIte, add_zero]
    apply expectedPayoff_le_const_of_support _ _ _ probFailure_eq_zero
    intro z hz
    change z ∈ support (do
      let y ← (SCKAScheme.sckaSecurityImpl b (exposureA kem onoff leak) (exposureB kem onoff leak)
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) _).run p.1
      pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2))) at hz
    rw [mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    simp only [mem_support_pure_iff] at hz
    subst z
    let J := fun s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) =>
      currentKEMFailure kem onoff hDet s = false ∧
      currentFailurePotential kem onoff s = currentFailurePotential kem onoff p.1
    have hj : J p.1 := ⟨hgood.2, rfl⟩
    suffices hout : J y.2 by
      exact le_of_eq (by simp [trackedFailureScore, hout.1, hout.2])
  · apply (SCKAScheme.challOf_recordsChallenges (fun _ => b)).preservesInv J ?_ t p.1 hj y hy
    intro state challenged hstate
    exact hstate
  · apply SCKAScheme.oracleCorruptA_preservesInv (vulnCorrA kem onoff) J ?_ u p.1 hj y hy
    intro state exposed hstate
    exact hstate
  · apply SCKAScheme.oracleCorruptB_preservesInv (vulnCorrB kem onoff) J ?_ u p.1 hj y hy
    intro state exposed hstate
    exact hstate

/-- Under the module's assumptions, for every bit `b`, budget `q`, and adversary `adv`
with `SecuritySendQueryBound adv q`, the tracked execution from `(initialGame, false)` satisfies
`Pr[bad_final = true] ≤ q · ε`. -/
theorem kem_failure_probability_le
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff) (b : Bool)
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q) :
    Pr[fun z => z.2.2 = true |
      (simulateQ (trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b) adv).run
        (initialGame (Sym := Sym) kem onoff, false)] ≤
      (q : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp := by
  have hpres := trackedSecurityImpl_preserves kem onoff hDet ecEk hEk ecCt0 hCt0
    ecCt1 hCt1 leak b
  have hinit := tracked_initial_inv kem onoff hDet ecEk ecCt0 ecCt1
    ecEk.ec.nchunk_pos ecCt0.ec.nchunk_pos
  have hscore₀ : trackedFailureScore kem onoff
      (initialGame (Sym := Sym) kem onoff, false) = 0 := by
    simp [trackedFailureScore, currentFailurePotential, initialGame, initialA, initialB,
      SCKAScheme.initGameState, Option.map₂]
  have hscore := expectedPayoff_simulateQ_run_le
    (trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b)
    (trackedInv kem onoff hDet ecEk ecCt0 ecCt1)
    (trackedFailureScore kem onoff) (fun t => SCKAScheme.sckaSecuritySpec.isSendQuery t = true)
    (factorCorrectnessError kem onoff) hpres
    (trackedSecurity_score_step_le kem onoff hDet ecEk ecCt0 ecCt1 leak b)
    adv q hq (initialGame kem onoff, false) hinit
  rw [hscore₀, zero_add, factorCorrectnessError_eq] at hscore
  exact (tracked_bad_probability_le_score kem onoff _).trans hscore

end oppUniKemCKA.Security
