/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

-- Import the previous per-set arithmetic check only to serialize the heavy kernel
-- checks: lake builds imports first, so at most one such module
-- elaborates at a time.
import SecureMessaging.KEM.MLKEM.Correctness.FailureCertificate.MLKEM768

/-!
# The ML-KEM-1024 failure-bound arithmetic check

This module proves the ML-KEM-1024 instance of the finite-measure arithmetic
bound. The FIPS 203 Table 2 parameters are `k = 4`, `η₁ = 2`, `η₂ = 2`,
`d_u = 11`, and `d_v = 5`.

Those parameters determine the one-coordinate coefficient-noise measure used in
the proof: `η₁ = 2` gives the key-side centered-binomial `CBD₂` samples,
`η₂ = 2` gives the encryption-error samples, `d_u = 11` gives the
`u`-compression error table,
`d_v = 5` gives the `v`-compression error table, and `k = 4` gives `4 * 256`
coefficient products for each dot product.

The theorem below proves the exact integer inequality

`256·decodeFailureMass/(2·noiseDenominator)≤2^-174.8`

for this finite measure.  The coefficient-distribution comparison needed to apply this
number to the honest sampler is stated in `NoiseModel.lean`.

This module imports the ML-KEM-768 arithmetic check to serialize the heavy
closed arithmetic proofs in lake order.
-/

open ToVCVio LatticeCrypto
open scoped ENNReal

namespace MLKEM

set_option exponentiation.threshold 30000 in
/-- The ML-KEM-1024 fifth-power Table 1 arithmetic check. It is the natural-number
form of

`256 * decodeFailureMass / (2 * noiseDenominator) ≤ 2^-174.8`.

The exponent is represented as `scaledFailureExponent .MLKEM1024 = 874`, i.e.
`5 * 174.8`, so the comparison can be checked with integer arithmetic. -/
theorem decodeFailureMass_pow_five_le_mlkem1024 :
    (ringDegree * decodeFailureMass .MLKEM1024) ^ 5 * 2 ^ scaledFailureExponent .MLKEM1024 ≤
      (2 * noiseDenominator .MLKEM1024) ^ 5 := by
  have hR : (2 : ℕ) ≤ 2 ^ 28416 := Nat.le_self_pow (by norm_num) 2
  have hwin : MeasureWindow (coefficientNoiseMeasure .MLKEM1024) (-10294)
      (-10294 + ((modulus * 7 : ℕ) : ℤ) - 1) :=
    measureWindow_coefficientNoiseMeasure_mlkem1024.mono (le_refl _) (by norm_num [modulus])
  have hden : 2 * totalMass (coefficientNoiseMeasure .MLKEM1024) < 2 ^ 28416 := by
    have h : totalMass (coefficientNoiseMeasure .MLKEM1024) = 2 ^ 16388 * 3329 ^ 1025 :=
      noiseDenominator_mlkem1024
    rw [h]; decide +kernel
  rw [decodeFailureMass_eq .MLKEM1024 hR hwin hden, measurePack_coefficientNoiseMeasure_mlkem1024,
    weightPack_blocked, noiseDenominator_mlkem1024, scaledFailureExponent, ringDegree]
  decide +kernel

end MLKEM
