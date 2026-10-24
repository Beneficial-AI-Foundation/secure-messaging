/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
module

public import VCVio.CryptoFoundations.PRF
public import ToVCVio.EvalDist.BoolDist

/-!
# The PRF advantage in real form

VCVio defines `prfAdvantage` as the `ℝ≥0∞`-valued Boolean distance of the real and ideal
experiments. `toReal_prfAdvantage` gives its real value as the absolute difference of their
success probabilities, the form that the AEAD security bounds use.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal

namespace PRFScheme

/-- Let `adversary` attack the PRF `prf`. Then the real value of its advantage is
`|Pr[prfRealExperiment = true] - Pr[prfIdealExperiment = true]|`. -/
theorem toReal_prfAdvantage {K D R : Type} [DecidableEq D] [SampleableType R]
    (prf : PRFScheme K D R) (adversary : PRFAdversary D R) :
    (prfAdvantage prf adversary).toReal =
      |(Pr{let x ← prf.prfRealExperiment adversary}[x = true]).toReal -
        (Pr{let x ← prfIdealExperiment adversary}[x = true]).toReal| :=
  ToVCVio.toReal_boolDist_evalDist _ _

end PRFScheme
