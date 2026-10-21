/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.ProgramLogic.Unary.HoareTriple

/-!
# Expected payoff through `wp`

For `oa : ProbComp A` and `f : A → ℝ≥0∞`, the upstream quantitative weakest precondition
`wp oa f` is the expected value of `f` over the outputs of `oa`. A `ProbComp` never fails,
so `wp oa f = ∑' a, Pr[oa = a] · f a` (`wp_eq_tsum`).

This file adds two facts that VCVio does not state:

* `wp_bind_eq_tsum` writes `wp_bind` as a sum over the outputs of the first computation;
* `prEvent_le_wp` bounds the probability of an event by the expectation of any payoff that
  is at least `1` on the event.
-/

open OracleSpec ENNReal OracleComp.ProgramLogic

namespace OracleComp

/-- The expected payoff of a sequential composition is the average of the expected payoffs
of the continuations. -/
lemma wp_bind_eq_tsum {A B : Type} (oa : ProbComp A) (ob : A → ProbComp B)
    (payoff : B → ℝ≥0∞) :
    wp (oa >>= ob) payoff = ∑' a, Pr{let x ← oa}[x = a] * wp (ob a) payoff := by
  rw [wp_bind, wp_eq_tsum]

/-- An event on which every payoff is at least `1` has probability at most the expected
payoff. -/
lemma prEvent_le_wp {A : Type} (oa : ProbComp A) (p : A → Prop)
    (f : A → ℝ≥0∞) (hf : ∀ a, p a → 1 ≤ f a) :
    Pr{let x ← oa}[p x] ≤ wp oa f := by
  rw [prEvent_eq_wp_propInd]
  refine wp_mono oa fun a => ?_
  by_cases ha : p a
  · simpa only [ha, propInd_true] using hf a ha
  · simp only [ha, propInd_false, zero_le]

end OracleComp
