/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.MLKEM.Correctness.FailureCertificate.PackedMeasures

/-!
# The ML-KEM-512 failure-bound arithmetic check

This module proves the ML-KEM-512 instance of the finite-measure arithmetic
bound. The FIPS 203 Table 2 parameters are `k = 2`, `η₁ = 3`, `η₂ = 2`,
`d_u = 10`, and `d_v = 4`.

Those parameters determine the one-coordinate coefficient-noise measure used in
the proof: `η₁ = 3` gives the centered-binomial `CBD₃` samples for the key-side
products `eᵀy` and `sᵀ(e₁ + ε_u)`, `η₂ = 2` gives the centered-binomial `CBD₂`
encryption-error samples,
`d_u = 10` gives the `u`-compression error table, `d_v = 4` gives the
`v`-compression error table, and `k = 2` gives `2 * 256` coefficient products
for each dot product.

The theorem below proves the exact integer inequality

`256·decodeFailureMass/(2·noiseDenominator)≤2^-138.8`

for this finite measure.  The coefficient-distribution comparison needed to apply this
number to the honest sampler is stated in `NoiseModel.lean`.

The approved parameter sets are split into separate modules so that lake
checks one large closed arithmetic proof at a time.
-/

open LatticeCrypto
open scoped ENNReal

namespace MLKEM

-- Raise the threshold so `whnf` does not warn on the closed `2 ^ W` bases (W ≤ 28416),
-- which are bounded by monotonicity, never evaluated; nested `(2 ^ W) ^ q` stays kernel-only.
set_option exponentiation.threshold 30000 in
/-- The ML-KEM-512 fifth-power Table 1 arithmetic check. It is the natural-number
form of

`256 * decodeFailureMass / (2 * noiseDenominator) ≤ 2^-138.8`.

The exponent is represented as `scaledFailureExponent .MLKEM512 = 694`, i.e.
`5 * 138.8`, so the comparison can be checked with integer arithmetic. -/
theorem decodeFailureMass_pow_five_le_mlkem512 :
    (ringDegree * decodeFailureMass .MLKEM512) ^ 5 * 2 ^ scaledFailureExponent .MLKEM512 ≤
      (2 * noiseDenominator .MLKEM512) ^ 5 := by
  have hR : (2 : ℕ) ≤ 2 ^ 17280 := Nat.le_self_pow (by norm_num) 2
  have hwin : MeasureWindow (coefficientNoiseMeasure .MLKEM512) (-10858)
      (-10858 + ((modulus * 7 : ℕ) : ℤ) - 1) :=
    measureWindow_coefficientNoiseMeasure_mlkem512.mono (le_refl _) (by norm_num [modulus])
  have hden : 2 * totalMass (coefficientNoiseMeasure .MLKEM512) < 2 ^ 17280 := by
    have h : totalMass (coefficientNoiseMeasure .MLKEM512) = 2 ^ 11268 * 3329 ^ 513 :=
      noiseDenominator_mlkem512
    rw [h]; decide +kernel
  rw [decodeFailureMass_eq .MLKEM512 hR hwin hden, measurePack_coefficientNoiseMeasure_mlkem512,
    weightPack_blocked, noiseDenominator_mlkem512, scaledFailureExponent, ringDegree]
  decide +kernel

end MLKEM
