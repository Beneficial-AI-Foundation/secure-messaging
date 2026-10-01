/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
import VCVio.OracleComp.ProbComp

/-!
# Identical until bad on invariant states

Fix types `ι σ α : Type`, an oracle specification `spec : OracleSpec ι`,
implementations `left right : QueryImpl spec (StateT σ ProbComp)`, and
state predicates `Inv bad : σ → Prop`. Their queries are lossless because
the underlying monad is `ProbComp`.

**Assumptions.** For every query `t : spec.Domain` and state `s : σ`:

* if `Inv s`, then `Inv s'` for every `(a, s')` in the support of `(left t).run s`;
* if `bad s`, then `bad s'` for every `(a, s')` in that same support;
* if `Inv s ∧ ¬bad s`, then `(left t).run s = (right t).run s`.

Here each response `a` has type `spec.Range t`.

**Conclusion.** For every computation `oa : OracleComp spec α`, initial
state `s₀ : σ` satisfying `Inv s₀`, and output event `E : α → Prop`, define
`L := (simulateQ left oa).run s₀` and `R := (simulateQ right oa).run s₀`.
Both computations return `(a, s') : α × σ`. The real-valued probabilities satisfy
`|Pr[E(a) : (a, s') ← L] − Pr[E(a) : (a, s') ← R]| ≤ Pr[bad(s') : (a, s') ← L]`.

**Proof.** Induct on `oa`. Queries from good invariant states share their
response/state computation. From bad states, persistence makes the final
bad probability one, which bounds either event probability.
-/

open OracleSpec ENNReal

namespace OracleComp

variable {ι σ α : Type} {spec : OracleSpec ι}

/-- A lossless stateful simulation started in a persistent bad state ends
in a bad state with probability one. -/
private theorem bad_run_probability_one
    (impl : QueryImpl spec (StateT σ ProbComp)) (bad : σ → Prop)
    (hmono : QueryImpl.PreservesInv impl bad) (oa : OracleComp spec α)
    (s : σ) (hs : bad s) :
    Pr[fun z => bad z.2 | (simulateQ impl oa).run s] = 1 := by
  apply probEvent_eq_one_iff.mpr
  exact ⟨probFailure_eq_zero, simulateQ_run_preservesInv impl bad hmono oa s hs⟩

/-- Probability bounds for two lossless stateful oracle implementations
`left` and `right`, an adaptive computation `oa`, and an output event `event`.

**Assumptions.**

* The initial state `s` satisfies `Inv`.
* Every query under `left` preserves `Inv` and `bad`.
* On any state satisfying `Inv ∧ ¬bad`, each query has the same joint
  distribution of response and next state under `left` and `right`.

**Notation.** Define the computations
`L := (simulateQ left oa).run s` and `R := (simulateQ right oa).run s`,
each returning a pair `(a, s') : α × σ`. Define

* `pL := Pr[fun (a, _) => event a | L]`;
* `pR := Pr[fun (a, _) => event a | R]`;
* `pBad := Pr[fun (_, s') => bad s' | L]`.

**Conclusion.** `pL ≤ pR + pBad` and `pR ≤ pL + pBad`, as inequalities
in `ℝ≥0∞`.

The proof uses persistence of `bad` under `left` and query equality on
good invariant states. -/
theorem probEvent_simulateQ_run_bounds_of_inv
    (left right : QueryImpl spec (StateT σ ProbComp))
    (Inv bad : σ → Prop)
    (hpres : QueryImpl.PreservesInv left Inv)
    (hmono : QueryImpl.PreservesInv left bad)
    (hagree : ∀ t s, Inv s → ¬bad s → (left t).run s = (right t).run s)
    (oa : OracleComp spec α) (event : α → Prop) (s : σ) (hs : Inv s) :
    (Pr[fun z => event z.1 | (simulateQ left oa).run s] ≤
      Pr[fun z => event z.1 | (simulateQ right oa).run s] +
      Pr[fun z => bad z.2 | (simulateQ left oa).run s]) ∧
    (Pr[fun z => event z.1 | (simulateQ right oa).run s] ≤
      Pr[fun z => event z.1 | (simulateQ left oa).run s] +
      Pr[fun z => bad z.2 | (simulateQ left oa).run s]) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t cont ih =>
    by_cases hb : bad s
    · rw [bad_run_probability_one left bad hmono _ s hb]
      constructor <;> exact probEvent_le_one.trans (le_add_left le_rfl)
    · simp only [simulateQ_query_bind, StateT.run_bind, OracleQuery.input_query,
        monadLift_self]
      rw [← hagree t s hs hb]
      simp only [probEvent_bind_eq_tsum]
      dsimp only [OracleSpec.query, OracleQuery.cont, OracleQuery.input]
      constructor
      · rw [← ENNReal.tsum_add]
        apply ENNReal.tsum_le_tsum
        intro y
        by_cases hy : y ∈ support ((left t).run s)
        · have h := (ih y.1 y.2 (hpres t s hs y hy)).1
          simpa only [mul_add, id] using mul_le_mul' (le_refl (Pr[= y | (left t).run s])) h
        · simp only [probOutput_eq_zero_of_not_mem_support hy, zero_mul, add_zero, le_refl]
      · rw [← ENNReal.tsum_add]
        apply ENNReal.tsum_le_tsum
        intro y
        by_cases hy : y ∈ support ((left t).run s)
        · have h := (ih y.1 y.2 (hpres t s hs y hy)).2
          simpa only [mul_add, id] using mul_le_mul' (le_refl (Pr[= y | (left t).run s])) h
        · simp only [probOutput_eq_zero_of_not_mem_support hy, zero_mul, add_zero, le_refl]

/-- Real-valued distinguishing bound for two lossless stateful oracle
implementations `left` and `right` and an adaptive computation `oa`.

**Assumptions.** The initial state `s` satisfies `Inv`; `left` preserves
`Inv` and `bad`; and both implementations give the same joint distribution
of response and next state for each query on states satisfying `Inv ∧ ¬bad`.

**Notation.** Set `L := (simulateQ left oa).run s` and
`R := (simulateQ right oa).run s`. For the output event `event : α → Prop`,
define the real numbers

* `pL := (Pr[fun (a, _) => event a | L]).toReal`;
* `pR := (Pr[fun (a, _) => event a | R]).toReal`;
* `pBad := (Pr[fun (_, s') => bad s' | L]).toReal`.

**Conclusion.** `|pL − pR| ≤ pBad`. -/
theorem abs_probEvent_simulateQ_run_sub_le_bad_of_inv
    (left right : QueryImpl spec (StateT σ ProbComp))
    (Inv bad : σ → Prop)
    (hpres : QueryImpl.PreservesInv left Inv)
    (hmono : QueryImpl.PreservesInv left bad)
    (hagree : ∀ t s, Inv s → ¬bad s → (left t).run s = (right t).run s)
    (oa : OracleComp spec α) (event : α → Prop) (s : σ) (hs : Inv s) :
    |(Pr[fun z => event z.1 | (simulateQ left oa).run s]).toReal -
      (Pr[fun z => event z.1 | (simulateQ right oa).run s]).toReal| ≤
      (Pr[fun z => bad z.2 | (simulateQ left oa).run s]).toReal := by
  obtain ⟨hl, hr⟩ := probEvent_simulateQ_run_bounds_of_inv
    left right Inv bad hpres hmono hagree oa event s hs
  have hl' := ENNReal.toReal_mono (by simp) hl
  have hr' := ENNReal.toReal_mono (by simp) hr
  rw [ENNReal.toReal_add (by simp) (by simp)] at hl' hr'
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

end OracleComp
