/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Ideal
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Certificate.RoundedConvolution

/-! # Exact certificate parameters for the modern FrodoKEM families -/

open scoped ENNReal

namespace FrodoKEM.Certificate

/-- Fixed-point precision used by each parameter family. -/
def precision : ParameterSet → ℕ
  | .FrodoKEM640 | .eFrodoKEM640 => 192
  | .FrodoKEM976 | .eFrodoKEM976 => 256
  | .FrodoKEM1344 | .eFrodoKEM1344 => 320

/-- Retained half-width of each rounded convolution. -/
def window : ParameterSet → ℕ
  | .FrodoKEM640 | .eFrodoKEM640 => 4608
  | .FrodoKEM976 | .eFrodoKEM976 => 4608
  | .FrodoKEM1344 | .eFrodoKEM1344 => 2560

/-- Generic recurrence configured with the exact modern sampler weights. -/
def config (ps : ParameterSet) :
    FailureCertificate.RoundedConvolution.Config :=
  {
    steps := 2 * ps.params.n
    a := ps.errorTable.d
    seedBits := lenChi
    window := window ps
    precision := precision ps
    weight := noiseCount ps
  }

/-- Indicator of the asymmetric decoder failure interval. -/
def badWeight (ps : ParameterSet) (z : ℤ) : ℕ :=
  if Ideal.entryBad ps z then 1 else 0

/-- Exact certified block-bound numerator for each family. -/
def numerator : ParameterSet → ℕ
  | .FrodoKEM640 | .eFrodoKEM640 => 697039582896201685440
  | .FrodoKEM976 | .eFrodoKEM976 => 6219212683815615322880
  | .FrodoKEM1344 | .eFrodoKEM1344 => 12714471512245081199450752

/-- Published failure exponent measured in tenths of a bit. -/
def exponentTenths : ParameterSet → ℕ
  | .FrodoKEM640 | .eFrodoKEM640 => 1387
  | .FrodoKEM976 | .eFrodoKEM976 => 1996
  | .FrodoKEM1344 | .eFrodoKEM1344 => 2525

/-- Exact rational upper bound for the independent-sampling experiment. -/
noncomputable def failureBound (ps : ParameterSet) : ℝ≥0∞ :=
  (numerator ps : ℝ≥0∞) / 2 ^ (precision ps + lenChi)

end FrodoKEM.Certificate
