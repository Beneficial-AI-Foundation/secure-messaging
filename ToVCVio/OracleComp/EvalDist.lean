/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.ProbCompLift
import ToVCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Sum

/-!
# Support-wise bind sums and the Boolean complement

`prEvent_bind_congr_eq_add` splits an event probability after a common draw, and
`prEvent_eq_false_eq_one_sub` gives `Pr[false] = 1 - Pr[true]` for oracle computations.
-/

open OracleSpec ENNReal

namespace ToVCVio

/-- If, on every possible output of a common `ProbComp` draw, one event probability is
the sum of two others, the same holds after the draw. -/
lemma prEvent_bind_congr_eq_add {α β γ₁ γ₂ : Type} (mx : ProbComp α)
    {f : α → ProbComp β} {g₁ : α → ProbComp γ₁} {g₂ : α → ProbComp γ₂}
    {p : β → Prop} {q₁ : γ₁ → Prop} {q₂ : γ₂ → Prop}
    (h : ∀ x ∈ support mx,
      Pr{let y ← f x}[p y] = Pr{let z ← g₁ x}[q₁ z] + Pr{let z ← g₂ x}[q₂ z]) :
    Pr{let y ← mx >>= f}[p y] =
      Pr{let z ← mx >>= g₁}[q₁ z] + Pr{let z ← mx >>= g₂}[q₂ z] := by
  simp only [OracleComp.prEvent_bind_eq_tsum, ← ENNReal.tsum_add]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ support mx
  · rw [h x hx, left_distrib]
  · simp only [prEvent_eq_zero_of_not_mem_support mx hx, zero_mul, add_zero]

end ToVCVio

namespace OracleComp

/-- An oracle computation returns `false` with the probability it does not return `true`. -/
lemma prEvent_eq_false_eq_one_sub {ι : Type} {spec : OracleSpec ι}
    [OracleSpec.AnswerMeasure spec] (mx : OracleComp spec Bool) :
    Pr{let x ← mx}[x = false] = 1 - Pr{let x ← mx}[x = true] := by
  rw [← prEvent_not_eq_one_sub mx (· = true)]
  simp only [Bool.not_eq_true]

end OracleComp
