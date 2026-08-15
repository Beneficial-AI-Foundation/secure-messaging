/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.OracleComp.ExpectedPayoff
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Expected-Payoff Bound for Stateful Simulation
-/

open OracleSpec ENNReal

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {σ α : Type}

/-- Let:

- `impl : QueryImpl spec (StateT σ ProbComp)` be an implementation
  for oracles in `spec : OracleSpec ι`, over a state type `σ`,
- `Inv : σ → Prop` be a predicate on states,
- `score : σ → ℝ≥0∞` be a payoff function on states,
- `p : ι → Prop` be a predicate on the oracles in `spec`,
- `epsilon : ℝ≥0∞` be a fixed error bound,
- for any computation `X : ProbComp (β × σ)`, write
  `E_X[score] := expectedPayoff X (fun z => score z.2)` for the expected
  score of `X`'s final state.

Assume:

(1) `Inv` is preserved by every `impl` query.
(2) For every oracle `t` and every state `s` satisfying `Inv s`:
- if `p t`, then `E_{(impl t).run s}[score] ≤ score s + epsilon`;
- otherwise, `E_{(impl t).run s}[score] ≤ score s`.

Then: for every computation `oa` making
at most `q` queries satisfying `p` and every state `s` satisfying `Inv s`, we have

`E_{run oa from state s}[score] ≤ score s + q · epsilon.` -/
lemma expectedPayoff_simulateQ_run_le
    (impl : QueryImpl spec (StateT σ ProbComp))
    (Inv : σ → Prop) (score : σ → ℝ≥0∞)
    (p : ι → Prop) [DecidablePred p] (epsilon : ℝ≥0∞)
    (hpres : QueryImpl.PreservesInv impl Inv)
    (hstep : ∀ t s, Inv s →
      expectedPayoff ((impl t).run s) (fun z => score z.2) ≤
        score s + if p t then epsilon else 0)
    (oa : OracleComp spec α) (q : ℕ) (hq : oa.IsQueryBoundP p q) :
    ∀ s, Inv s →
      expectedPayoff ((simulateQ impl oa).run s) (fun z => score z.2) ≤
        score s + (q : ℝ≥0∞) * epsilon := by
  induction oa using OracleComp.inductionOn generalizing q with
  | pure x =>
      intro s hs
      simp [simulateQ_pure, StateT.run_pure, expectedPayoff_pure]
  | @query_bind t cont ih =>
      intro s hs
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hq
      obtain ⟨hcan, hcont⟩ := hq
      rw [simulateQ_query_bind, StateT.run_bind, expectedPayoff_bind]
      by_cases ht : p t
      · have hqpos : 0 < q := hcan.resolve_left (not_not_intro ht)
        have htail : ∀ z ∈ support ((impl t).run s),
            expectedPayoff
                ((simulateQ impl (cont z.1)).run z.2)
                (fun w => score w.2) ≤
              score z.2 + (((q - 1 : ℕ) : ℝ≥0∞) * epsilon) := by
          intro z hz
          exact ih z.1 (q - 1) (by simpa [ht] using hcont z.1) z.2
            (hpres t s hs z hz)
        calc
          (Pr[⊥ | (impl t).run s] +
            ∑' z, Pr[= z | (impl t).run s] *
              expectedPayoff ((simulateQ impl (cont z.1)).run z.2)
                (fun w => score w.2)) ≤
              Pr[⊥ | (impl t).run s] +
                ∑' z, Pr[= z | (impl t).run s] *
                (score z.2 + (((q - 1 : ℕ) : ℝ≥0∞) * epsilon)) := by
            exact add_le_add le_rfl (ENNReal.tsum_le_tsum fun z => by
              by_cases hz : z ∈ support ((impl t).run s)
              · exact mul_le_mul' le_rfl (htail z hz)
              · simp [(probOutput_eq_zero_iff _ _).2 hz])
          _ ≤ expectedPayoff ((impl t).run s) (fun z => score z.2) +
                (((q - 1 : ℕ) : ℝ≥0∞) * epsilon) :=
            expectedPayoff_add_const_le _ _ _
          _ ≤ (score s + epsilon) +
                (((q - 1 : ℕ) : ℝ≥0∞) * epsilon) := by
            exact add_le_add (by simpa [ht] using hstep t s hs) le_rfl
          _ = score s + (q : ℝ≥0∞) * epsilon := by
            have hcast : (((q - 1 : ℕ) : ℝ≥0∞) + 1) = (q : ℝ≥0∞) := by
              exact_mod_cast Nat.sub_add_cancel hqpos
            rw [← hcast, add_mul, one_mul]
            ac_rfl
      · have htail : ∀ z ∈ support ((impl t).run s),
            expectedPayoff
                ((simulateQ impl (cont z.1)).run z.2)
                (fun w => score w.2) ≤
              score z.2 + ((q : ℝ≥0∞) * epsilon) := by
          intro z hz
          exact ih z.1 q (by simpa [ht] using hcont z.1) z.2
            (hpres t s hs z hz)
        calc
          (Pr[⊥ | (impl t).run s] +
            ∑' z, Pr[= z | (impl t).run s] *
              expectedPayoff ((simulateQ impl (cont z.1)).run z.2)
                (fun w => score w.2)) ≤
              Pr[⊥ | (impl t).run s] +
                ∑' z, Pr[= z | (impl t).run s] *
                (score z.2 + ((q : ℝ≥0∞) * epsilon)) := by
            exact add_le_add le_rfl (ENNReal.tsum_le_tsum fun z => by
              by_cases hz : z ∈ support ((impl t).run s)
              · exact mul_le_mul' le_rfl (htail z hz)
              · simp [(probOutput_eq_zero_iff _ _).2 hz])
          _ ≤ expectedPayoff ((impl t).run s) (fun z => score z.2) +
                ((q : ℝ≥0∞) * epsilon) :=
            expectedPayoff_add_const_le _ _ _
          _ ≤ score s + ((q : ℝ≥0∞) * epsilon) := by
            simpa [ht] using
              add_le_add (hstep t s hs) (le_refl ((q : ℝ≥0∞) * epsilon))

end OracleComp
