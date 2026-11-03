/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.IndepNoise
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Certificate.RoundedConvolution

/-! # Certificate parameters for each FrodoKEM family -/

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

/-- The rounded-convolution settings for one family, weighted by the exact error-sampler counts. -/
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

/-- `1` outside the decoding interval `[-threshold, threshold)` and `0` inside it. -/
def badWeight (ps : ParameterSet) (z : ℤ) : ℕ :=
  if IndepNoise.entryBad ps z then 1 else 0

/-- Numerator of `failureBound`, the certified bound on decryption failure. -/
def numerator : ParameterSet → ℕ
  | .FrodoKEM640 | .eFrodoKEM640 => 697039582896201685440
  | .FrodoKEM976 | .eFrodoKEM976 => 6219212683815615322880
  | .FrodoKEM1344 | .eFrodoKEM1344 => 12714471512245081199450752

/-- Published failure exponent measured in tenths of a bit. -/
def exponentTenths : ParameterSet → ℕ
  | .FrodoKEM640 | .eFrodoKEM640 => 1387
  | .FrodoKEM976 | .eFrodoKEM976 => 1996
  | .FrodoKEM1344 | .eFrodoKEM1344 => 2525

/-- Certified bound on decryption failure when the errors are sampled independently. -/
noncomputable def failureBound (ps : ParameterSet) : ℝ≥0∞ :=
  (numerator ps : ℝ≥0∞) / 2 ^ (precision ps + lenChi)

end FrodoKEM.Certificate
