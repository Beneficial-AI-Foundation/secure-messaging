/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
module

public import VCVio.CryptoFoundations.PRF

/-!
# The PRF advantage in real form

`toReal_prfAdvantage` unfolds VCVio's `ℝ≥0∞`-valued `prfAdvantage` to the absolute difference
of the real and ideal success probabilities.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal

namespace PRFScheme

/-- The PRF advantage in real form: `|Pr[real ⇒ true] - Pr[ideal ⇒ true]|`. -/
theorem toReal_prfAdvantage {K D R : Type} [DecidableEq D] [SampleableType R]
    (prf : PRFScheme K D R) (adversary : PRFAdversary D R) :
    (prfAdvantage prf adversary).toReal =
      |(Pr{let x ← prf.prfRealExperiment adversary}[x = true]).toReal -
        (Pr{let x ← prfIdealExperiment adversary}[x = true]).toReal| := by
  rw [prfAdvantage, MeasureTheory.Measure.toReal_boolDist, prEvent_eq_evalDist_singleton,
    prEvent_eq_evalDist_singleton]

end PRFScheme
