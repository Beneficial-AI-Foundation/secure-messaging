/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
import VCVio.OracleComp.ProbComp
import VCVio.EvalDist.Monad.Disagreement

/-!
# Identical until bad on invariant states

**Setting.** Let

- `spec : OracleSpec ι` be a query interface and `σ` a state space;
- `left right : QueryImpl spec (StateT σ ProbComp)` be stateful oracle implementations;
- `Inv bad : σ → Prop` be state predicates;
- `oa : OracleComp spec α` be an oracle computation, `event : α → Prop` an event on its output,
  and `s : σ` an initial state.

**Notation.** `L := (simulateQ left oa).run s` and `R := (simulateQ right oa).run s` return the
output of `oa` together with the final state. Write `pL := Pr[fun z => event z.1 | L]`,
`pR := Pr[fun z => event z.1 | R]`, and `pBad := Pr[fun z => bad z.2 | L]`.

**Results.** Assume that

- `left` preserves `Inv` and `bad`: for every query `t`, state `u`, and `(a, u')` in the support
  of `(left t).run u`, `Inv u` implies `Inv u'`, and `bad u` implies `bad u'`;
- `(left t).run u = (right t).run u` for every query `t` and state `u` with `Inv u` and `¬bad u`.

Then, if the initial state `s` of `L` and `R` satisfies `Inv s`,

- `probEvent_simulateQ_run_bounds_of_inv`: `pL ≤ pR + pBad` and `pR ≤ pL + pBad`;
- `abs_probEvent_simulateQ_run_sub_le_bad_of_inv`: `|pL - pR| ≤ pBad` for the real values
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
`event : α → Prop`, and state `s` with `Inv s`, `pL ≤ pR + pBad` and `pR ≤ pL + pBad`, where
`pL := Pr[fun z => event z.1 | (simulateQ left oa).run s]`,
`pR := Pr[fun z => event z.1 | (simulateQ right oa).run s]`, and
`pBad := Pr[fun z => bad z.2 | (simulateQ left oa).run s]`. -/
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
      -- Both runs now share the query; lift the pointwise induction hypothesis through the
      -- bind with VCVio's disagreement lemma, taking the disagreement set empty.
      have step y (hy : y ∈ support ((left t).run s)) := ih y.1 y.2 (hpres t s hs y hy)
      constructor
      · simpa using probEvent_bind_le_add_bad_of_disagree' (D := fun _ => False) (ε := 0)
          (fun _ _ h => h.elim) fun y hy _ => by simpa using (step y hy).1
      · simpa using probEvent_bind_le_add_bad_of_disagree' (D := fun _ => False) (ε := 0)
          (fun _ _ h => h.elim) fun y hy _ => by simpa using (step y hy).2

/-- Under the hypotheses of `probEvent_simulateQ_run_bounds_of_inv` and with its notation, the
real values satisfy `|pL - pR| ≤ pBad`. -/
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
