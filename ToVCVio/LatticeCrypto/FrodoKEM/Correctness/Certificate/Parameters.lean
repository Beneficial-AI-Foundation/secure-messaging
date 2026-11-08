/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.IndepNoise
public import ToVCVio.Probability.RoundedConvolution

/-!
# Certificate parameters for each FrodoKEM size

The parameters depend only on the size: 640, 976 or 1344. FrodoKEM and eFrodoKEM of the same size
share them.

## References

* `[CiC25]`, Glabush, Longa, Naehrig, Peikert, Stebila and Virdia, *FrodoKEM: A
  CCA-Secure Learning With Errors Key Encapsulation Mechanism*, IACR
  Communications in Cryptology 2:3, <https://cic.iacr.org/p/2/3/25>.
-/

@[expose] public section

open scoped ENNReal

namespace FrodoKEM.Certificate

/-- Fixed-point precision for each size. -/
def precision : ParameterSet → ℕ
  | .FrodoKEM640 | .eFrodoKEM640 => 192
  | .FrodoKEM976 | .eFrodoKEM976 => 256
  | .FrodoKEM1344 | .eFrodoKEM1344 => 320

/-- Retained half-width of each rounded convolution. -/
def window : ParameterSet → ℕ
  | .FrodoKEM640 | .eFrodoKEM640 => 4608
  | .FrodoKEM976 | .eFrodoKEM976 => 4608
  | .FrodoKEM1344 | .eFrodoKEM1344 => 2560

/-- The rounded-convolution settings for one size, weighted by the exact error-sampler counts. -/
def config (ps : ParameterSet) :
    ToVCVio.RoundedConvolution.Config :=
  {
    steps := 2 * ps.params.n
    a := ps.errorTable.d
    seedBits := lenChi
    window := window ps
    precision := precision ps
    weight := noiseCount ps
  }

/-- `1` outside the decoding interval `[-noiseRadius, noiseRadius)` and `0` inside it. -/
def badWeight (ps : ParameterSet) (z : ℤ) : ℕ :=
  if IndepNoise.entryBad ps z then 1 else 0

/-- Numerator of `failureBound`, the bound on decryption failure from the certificates. -/
def numerator : ParameterSet → ℕ
  | .FrodoKEM640 | .eFrodoKEM640 => 697039582896201685440
  | .FrodoKEM976 | .eFrodoKEM976 => 6219212683815615322880
  | .FrodoKEM1344 | .eFrodoKEM1344 => 12714471512245081199450752

/-- The failure exponent of Table 4 of `[CiC25]`, in tenths of a bit. -/
def exponentTenths : ParameterSet → ℕ
  | .FrodoKEM640 | .eFrodoKEM640 => 1387
  | .FrodoKEM976 | .eFrodoKEM976 => 1996
  | .FrodoKEM1344 | .eFrodoKEM1344 => 2525

/-- The bound from the certificates on decryption failure, when the errors are sampled
independently. -/
noncomputable def failureBound (ps : ParameterSet) : ℝ≥0∞ :=
  (numerator ps : ℝ≥0∞) / 2 ^ (precision ps + lenChi)

end FrodoKEM.Certificate
