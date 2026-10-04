/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
import VCVio.OracleComp.ProbComp

/-!
# Identical until bad on invariant states

**Setting.** Let

- `spec : OracleSpec ι` be a query interface and `σ` a state space;
- `left right : QueryImpl spec (StateT σ ProbComp)` be stateful oracle implementations;
- `Inv bad : σ → Prop` be state predicates;
- `oa : OracleComp spec α` be an oracle computation, `event : α → Prop` an event on its output,
  and `s : σ` an initial state.

**Notation.** `L := (simulateQ left oa).run s` and `R := (simulateQ right oa).run s` return the
output of `oa` together with the final state. Write `pE(X) := Pr[fun z => event z.1 | X]` and
`pBad := Pr[fun z => bad z.2 | L]`.

**Results.** Assume that

- `left` preserves `Inv` and `bad`: for every query `t`, state `u`, and `(a, u')` in the support
  of `(left t).run u`, `Inv u` implies `Inv u'`, and `bad u` implies `bad u'`;
- `(left t).run u = (right t).run u` for every query `t` and state `u` with `Inv u` and `¬bad u`;
- `Inv s`.

Then

- `probEvent_simulateQ_run_bounds_of_inv`: `pE(L) ≤ pE(R) + pBad` and `pE(R) ≤ pE(L) + pBad`;
- `abs_probEvent_simulateQ_run_sub_le_bad_of_inv`: `|pE(L) - pE(R)| ≤ pBad` for the real values
  of these probabilities.
-/

open OracleSpec ENNReal

namespace OracleComp

variable {ι σ α : Type} {spec : OracleSpec ι}

/-- If `impl` preserves `bad` and `bad s`, then `(simulateQ impl oa).run s` ends in a state
satisfying `bad` with probability one. -/
private theorem bad_run_probability_one
    (impl : QueryImpl spec (StateT σ ProbComp)) (bad : σ → Prop)
    (hmono : QueryImpl.PreservesInv impl bad) (oa : OracleComp spec α)
    (s : σ) (hs : bad s) :
    Pr[fun z => bad z.2 | (simulateQ impl oa).run s] = 1 := by
  apply probEvent_eq_one_iff.mpr
  exact ⟨probFailure_eq_zero, simulateQ_run_preservesInv impl bad hmono oa s hs⟩

/-- Let `left` preserve `Inv` and `bad`, and let `(left t).run u = (right t).run u` for every
query `t` and state `u` with `Inv u` and `¬bad u`. Then, for every computation `oa`, event
`event : α → Prop`, and state `s` with `Inv s`, `pE(L) ≤ pE(R) + pBad` and
`pE(R) ≤ pE(L) + pBad`, where `L := (simulateQ left oa).run s`, `R := (simulateQ right oa).run s`,
`pE(X) := Pr[fun z => event z.1 | X]`, and `pBad := Pr[fun z => bad z.2 | L]`. -/
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

/-- Under the hypotheses of `probEvent_simulateQ_run_bounds_of_inv` and with its notation, the
real values satisfy `|pE(L) - pE(R)| ≤ pBad`. -/
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
