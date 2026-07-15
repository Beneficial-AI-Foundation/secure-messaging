/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.MLKEM.Correctness.FailureCertificate.MLKEM1024
import SecureMessaging.KEM.MLKEM.Correctness.FailureRates

/-!
# Exact certificate for the independent-model numerical inequality

## Mathematical statement

Fix a parameter set `p`.  Let `M_p : ℤ → ℕ` be
`coefficientNoiseMeasure p`, let `D_p=∑_x M_p(x)`, and push this measure
forward along the reduction map `π : ℤ→ℤ/qℤ`, where `q=3329`:

`M̄_p(r)=∑_{x≡r (mod q)} M_p(x)`.

For `b∈{0,1}` define

`Fail(b,r) :⇔ Compress₁(Decompress₁(b)+r) ≠ b`

and put

```
W(r) = ∑_{b∈{0,1}} 1_{Fail(b,r)},
F_p  = ∑_{r∈ℤ/qℤ} M̄_p(r) W(r).
```

In Lean, `D_p`, `W`, and `F_p` are `noiseDenominator p`,
`decodeFailureWeight`, and `decodeFailureMass p`.  Normalizing the counting
measure and averaging over the two bits gives the auxiliary one-coordinate mass
`F_p/(2D_p)`.  The theorem proved by this certificate is

`256 F_p/(2D_p) ≤ 2^{-e_p}`,                              (1)

where `e_p∈{138.8,164.8,174.8}` is the FIPS 203 Table 1 exponent.  The factor
`256` is the number of coefficient events in the later union bound.  Equation
(1) is an exact inequality for the independent finite measure `M_p`; the
comparison between this measure and the honest sampler is formulated
separately in `NoiseModel.lean`.

## Certificate representation

For any finitely supported `F:ℤ→ℕ` with support in `[lo,hi]`, define

`P_{F,lo}(X)=∑_{v=lo}^{hi} F(v)X^{v-lo}`

and encode all its coefficients in the single natural number

`measurePack R lo F = P_{F,lo}(R)`.

The chosen radix `R` exceeds every coefficient that is extracted.  Hence there
is no carry between base-`R` digits and

`F(lo+t) = (measurePack R lo F / R^t) % R`.               (2)

Additive convolution satisfies

`P_{F*G,lo_F+lo_G}=P_{F,lo_F}P_{G,lo_G}`,                 (3)

so convolution and convolution powers can be evaluated by natural-number
multiplication and exponentiation.  Periodization modulo `q`, namely summing
the masses in each congruence class, corresponds to reducing the generating
polynomial modulo `X^q-1`; after evaluation at `R`, this becomes reduction
modulo the repunit `R^q-1`.  Finally, `F_p` is extracted as the coefficient of
degree `q-1` in the product of the periodized mass polynomial with the reversed
weight polynomial.  The code-level names in `FailureCertificate/Radix.lean`
use `fold` for this periodization operation and prove (2)--(3), the repunit
identity, and the coefficient-extraction formula.

## Exact comparison

Taking fifth powers removes the single decimal place in `e_p`:

`5e_p ∈ {694,824,874}`.

Thus each per-parameter module checks the natural-number inequality

`(256F_p)^5 · 2^{5e_p} ≤ (2D_p)^5`                       (4)

using `decide +kernel`.  `decodeFailureMass_pow_five_le` collects the three
instances of (4), and `decodeFailureMass_le_fips203Bound` transports (4) to
(1) in `ℝ≥0∞`.  The heavy checks are import-chained across the per-parameter
modules so that only one large kernel computation is elaborated at a time.
-/

open LatticeCrypto
open scoped ENNReal

namespace MLKEM

private theorem decapsulationFailureExponent_mul_five (p : ParameterSet) :
    decapsulationFailureExponent p * 5 = (scaledFailureExponent p : ℚ) := by
  cases p <;> norm_num [decapsulationFailureExponent, scaledFailureExponent]

/-- The exact fifth-power arithmetic check. It proves the natural-number form of

`256 * decodeFailureMass p / (2 * noiseDenominator p) ≤ 2^(-e_p)`,

where `e_p` is the FIPS 203 Table 1 exponent. The fifth powers clear the single
decimal place in `e_p`, so the proof reduces to integer arithmetic. -/
theorem decodeFailureMass_pow_five_le (p : ParameterSet) :
    (ringDegree * decodeFailureMass p) ^ 5 * 2 ^ scaledFailureExponent p ≤
      (2 * noiseDenominator p) ^ 5 := by
  cases p
  · exact decodeFailureMass_pow_five_le_mlkem512
  · exact decodeFailureMass_pow_five_le_mlkem768
  · exact decodeFailureMass_pow_five_le_mlkem1024

private theorem ennreal_div_le_two_rpow {a b E : ℕ} {e : ℚ} (hb : b ≠ 0)
    (h5 : (e : ℝ) * 5 = (E : ℝ)) (h : a ^ 5 * 2 ^ E ≤ b ^ 5) :
    (a : ℝ≥0∞) / b ≤ 2 ^ (-(e : ℝ)) := by
  have cast5 : ∀ x : ℝ≥0∞, x ^ (5 : ℝ) = x ^ (5 : ℕ) := fun x => by
    rw [← ENNReal.rpow_natCast x 5]; norm_num
  rw [← ENNReal.rpow_le_rpow_iff (z := 5) (by norm_num)]
  have hLHS : ((a : ℝ≥0∞) / b) ^ (5 : ℝ) =
      (↑(a ^ 5) : ℝ≥0∞) / (↑(b ^ 5) : ℝ≥0∞) := by
    rw [ENNReal.div_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 5), cast5, cast5]
    norm_cast
  have hRHS : ((2 : ℝ≥0∞) ^ (-(e : ℝ))) ^ (5 : ℝ) =
      ((2 ^ E : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [← ENNReal.rpow_mul, neg_mul, h5, ENNReal.rpow_neg, ENNReal.rpow_natCast]
    norm_cast
  rw [hLHS, hRHS,
    ENNReal.div_le_iff (by exact_mod_cast pow_ne_zero 5 hb) (ENNReal.natCast_ne_top _),
    ← ENNReal.mul_le_iff_le_inv (by exact_mod_cast pow_ne_zero E (by norm_num : (2 : ℕ) ≠ 0))
      (ENNReal.natCast_ne_top _), ← Nat.cast_mul, Nat.cast_le, mul_comm (2 ^ E) (a ^ 5)]
  exact h

/-- The auxiliary coefficient measure satisfies the Table 1 numerical inequality:
its `256`-coordinate union-bound expression is at most `2^(-e_p)`. -/
theorem decodeFailureMass_le_fips203Bound (p : ParameterSet) :
    (ringDegree : ℝ≥0∞) * decodeFailureMass p / (2 * noiseDenominator p) ≤
      fips203DecapsulationFailureBound p := by
  have hne : 2 * noiseDenominator p ≠ 0 := by
    cases p <;>
      simp only [noiseDenominator_mlkem512, noiseDenominator_mlkem768,
        noiseDenominator_mlkem1024] <;> positivity
  rw [fips203DecapsulationFailureBound]
  have hcast : (ringDegree : ℝ≥0∞) * decodeFailureMass p / (2 * noiseDenominator p) =
      ((ringDegree * decodeFailureMass p : ℕ) : ℝ≥0∞) /
        ((2 * noiseDenominator p : ℕ) : ℝ≥0∞) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat]
  rw [hcast]
  exact ennreal_div_le_two_rpow hne
    (by exact_mod_cast decapsulationFailureExponent_mul_five p)
    (decodeFailureMass_pow_five_le p)

end MLKEM
