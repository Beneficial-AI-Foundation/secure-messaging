/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
module

public import VCVio.EvalDist.ProbabilityNotation
public import ToMathlib.MeasureTheory.Measure.Bool

/-!
# Boolean distance of two experiments in real form

VCVio states distinguishing advantages, such as `prfAdvantage` and `ddhAdvantage`, as the
`ℝ≥0∞`-valued Boolean distance `𝒟[mx].boolDist 𝒟[my]` of two experiments.
`toReal_boolDist_evalDist` rewrites its real value as `|Pr[mx = true] - Pr[my = true]|`.
-/

@[expose] public section

universe v

open ENNReal

namespace ToVCVio

/-- Let `mx` and `my` be two experiments that output a bit. Then the real value of their Boolean
distance is `|Pr[mx = true] - Pr[my = true]|`. -/
theorem toReal_boolDist_evalDist {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] (mx my : m Bool) :
    (𝒟[mx].boolDist 𝒟[my]).toReal =
      |(Pr{let x ← mx}[x = true]).toReal - (Pr{let x ← my}[x = true]).toReal| := by
  rw [MeasureTheory.Measure.toReal_boolDist, prEvent_eq_evalDist_singleton,
    prEvent_eq_evalDist_singleton]

end ToVCVio
