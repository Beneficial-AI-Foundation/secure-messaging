/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Security.Hybrid
import SecureMessaging.SCKA.Security.ExposureMonotone
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Adjacent hybrids after exposure

**Statement.** Fix a scheme and exposure policies. For every index `i : ℕ`,
state `s` with `i + 1 ∈ s.exposed`, output type `α`, and computation
`A : OracleComp sckaSecuritySpec α`, the complete output/state computations
of hybrids `i` and `i + 1` from `s` are equal.

**Proof.** Exposure persists under every query. The challenge modes agree
at each epoch other than `i + 1`; the guard rejects challenges at that
exposed epoch in both hybrids. Query equality on this preserved invariant
lifts to equality of the adaptive computations.

The result identifies equal continuation contributions on exposed paths.
A stopping argument uses this equality when replacing those continuations
by a common fixed output in a signed hybrid difference.
-/

open OracleSpec OracleComp

namespace SCKAScheme

variable {IK StA StB I Rho Rand : Type} [DecidableEq I] [SampleableType I]

/-- Every oracle of epoch hybrid `i` preserves exposure of epoch `e`.
Queries may follow any adaptive delivery or corruption order. -/
theorem epochHybridImpl_preserves_exposed
    (i : ℕ) (exposureA : ExposurePolicy StA Rand) (exposureB : ExposurePolicy StB Rand)
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) (e : ℕ) :
    QueryImpl.PreservesInv (epochHybridImpl i exposureA exposureB scka)
      (fun s => e ∈ s.exposed) := by
  intro t s hs z hz
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n)
    · have hz' : ∃ r, (r, s) = z := by
        simpa [epochHybridImpl, sckaCorrectnessImpl, oracleUnif] using hz
      obtain ⟨_, rfl⟩ := hz'
      exact hs
    · exact oracleSendA_preserves_exposed scka e u s hs z hz
    · exact oracleSendB_preserves_exposed scka e u s hs z hz
    · exact oracleRecvA_preserves_exposed scka e n s hs z hz
    · exact oracleRecvB_preserves_exposed scka e n s hs z hz
  · exact oracleSendArleak_preserves_exposed scka exposureA.send e u s hs z hz
  · exact oracleSendBrleak_preserves_exposed scka exposureB.send e u s hs z hz
  · exact oracleChall_preservesInv (decide (0 < t ∧ t ≤ i)) (fun s => e ∈ s.exposed)
      (fun _ _ h => h) t s hs z hz
  · exact oracleCorruptA_preserves_exposed exposureA.corrupt e u s hs z hz
  · exact oracleCorruptB_preserves_exposed exposureB.corrupt e u s hs z hz

/-- Adjacent hybrids have the same next-query distribution from a state
in which their differing epoch `i + 1` is already exposed. -/
theorem epochHybridImpl_query_eq_of_exposed
    (i : ℕ) (exposureA : ExposurePolicy StA Rand) (exposureB : ExposurePolicy StB Rand)
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain)
    (s : GameState StA StB I Rho) (hs : i + 1 ∈ s.exposed) :
    (epochHybridImpl (i + 1) exposureA exposureB scka t).run s =
      (epochHybridImpl i exposureA exposureB scka t).run s := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  all_goals try rfl
  change (oracleChall (decide (0 < t ∧ t ≤ i + 1)) StA StB I Rho t).run s =
    (oracleChall (decide (0 < t ∧ t ≤ i)) StA StB I Rho t).run s
  by_cases ht : t = i + 1
  · subst t
    rw [oracleChall_rejected _ s _ (Or.inl hs), oracleChall_rejected _ s _ (Or.inl hs)]
  · rw [epochHybrid_challenge_eq_of_ne i t ht]

/-- After epoch `i + 1` is exposed, adjacent hybrids produce exactly the
same complete continuation for every adaptive adversary. Consequently,
these exposed paths contribute zero to their signed distinguishing gap. -/
-- ANCHOR: epochHybrid_run_eq_of_exposed
theorem epochHybrid_run_eq_of_exposed
    (i : ℕ) (exposureA : ExposurePolicy StA Rand) (exposureB : ExposurePolicy StB Rand)
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    {α : Type} (adv : OracleComp (sckaSecuritySpec StA StB I Rho Rand) α)
    (s : GameState StA StB I Rho) (hs : i + 1 ∈ s.exposed) :
    (simulateQ (epochHybridImpl (i + 1) exposureA exposureB scka) adv).run s =
      (simulateQ (epochHybridImpl i exposureA exposureB scka) adv).run s := by
  have h := map_run_simulateQ_eq_of_query_map_eq_inv'
    (epochHybridImpl (i + 1) exposureA exposureB scka) (epochHybridImpl i exposureA exposureB scka)
    (fun state => i + 1 ∈ state.exposed) id
    (epochHybridImpl_preserves_exposed (i + 1) exposureA exposureB scka (i + 1))
    (fun t state hstate => by
      simpa using epochHybridImpl_query_eq_of_exposed i exposureA exposureB scka t state hstate)
    adv s hs
  simpa using h
-- ANCHOR_END: epochHybrid_run_eq_of_exposed

end SCKAScheme
