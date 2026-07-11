/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.MLKEM.Correctness.FailureCertificate.MLKEM1024
import SecureMessaging.KEM.MLKEM.Correctness.FailureRates

/-!
# The FIPS 203 Table 1 decode-failure bound

This file proves the arithmetic part of the FIPS 203 Table 1 failure-rate bound.
The surrounding correctness chain reduces honest ML-KEM decapsulation failure to
K-PKE recovery failure, then to the event that at least one of the `256`
coefficients decodes to the wrong message bit.

For one coefficient the exact question is:

`Compress₁ (Decompress₁ b + r) ≠ b`,

where `b ∈ {0,1}` is the message bit and `r` is the decryption-noise residue
modulo `q = 3329`. `decodeFailureWeight r` counts how many of the two bits fail
for that residue. `decodeFailureMass p` folds the integer coefficient-noise
counting measure modulo `q`, weights it by `decodeFailureWeight`, and sums. Thus

`decodeFailureMass p / (2 * noiseDenominator p)`

is the bit-averaged one-coordinate failure probability obtained by normalizing
the finite counting measure. Multiplying by `ringDegree = 256` gives the
union-bound estimate for any coefficient failing.

The arithmetic proof uses the following precise encoding of a finite counting
measure. Let `F : ℤ →₀ ℕ` be supported in `[lo, hi]`, i.e.

`F(v) ≠ 0 → lo ≤ v ∧ v ≤ hi`.

On the discrete measurable space `ℤ`, this finitely supported function is the
finite measure

`μ_F(A) = ∑_{v ∈ A} F(v)`

for finite/countable subsets `A ⊆ ℤ`; in particular the mass of the singleton
`{v}` is `μ_F({v}) = F(v)`. Its total mass is

`|F| = μ_F(ℤ) = ∑_v F(v)`.

This is not yet a probability measure unless `|F| = 1`. In this development the
coefficient-noise measures are deliberately kept as natural-number counts. When
`|F| ≠ 0`, the associated probability is obtained by normalization:

`Pr_F(A) = μ_F(A) / |F|`.

For the ML-KEM coefficient-noise measure, `|F| = noiseDenominator p`; the
extra factor `2` in `2 * noiseDenominator p` comes from averaging over the two
message bits.

Define the mass-generating polynomial

`P_{F,lo}(X) = ∑_{v=lo}^{hi} F(v) X^(v - lo) ∈ ℕ[X]`

This polynomial is not itself the measure or a probability distribution. It is
an algebraic encoding of the singleton masses: the coefficient of `X^(v - lo)`
is exactly `μ_F({v}) = F(v)`. Evaluating it at a natural number `R` gives

`measurePack R lo F = P_{F,lo}(R) = ∑_{v=lo}^{hi} F(v) R^(v - lo)`.

The radix `R` is chosen so that every coefficient extracted during the proof is
strictly less than `R`; hence if `0 ≤ t ≤ hi - lo`, then

`F(lo + t) = (measurePack R lo F / R^t) % R`.

This is ordinary polynomial evaluation plus a no-carry bound.

For the additive convolution

`(F * G)(v) = ∑_{a+b=v} F(a) G(b)`,

the generating polynomials satisfy

`P_{F*G,lo₁+lo₂}(X) = P_{F,lo₁}(X) P_{G,lo₂}(X)`,

so `measurePack_mul` turns convolution into multiplication after evaluation at
`R`, and `measurePack_pow` turns iterated convolution into exponentiation.

For reduction modulo `q`, if the support is contained in `lo .. lo + q*m - 1`,
the folded mass at residue `t` is

`F_q(t) = ∑_{j=0}^{m-1} F(lo + q*j + t)`.

Since `X^q = 1` in the quotient `ℕ[X]/(X^q - 1)`, evaluating at `R` makes this
folding a reduction modulo `R^q - 1` (`sum_mul_pow_mod_repunit`). Finally,
`decodeFailureMass_eq` computes

`∑_{t=0}^{q-1} F_q(t) * decodeFailureWeight(lo + t)`

as the middle coefficient of the product with the reversed weight polynomial.
The per-parameter modules instantiate this arithmetic at `R = 2 ^ W`.

FIPS 203 writes the Table 1 exponents with one decimal place:
`2^-138.8`, `2^-164.8`, and `2^-174.8`. Taking fifth powers clears those decimal
exponents because `5 * 138.8 = 694`, `5 * 164.8 = 824`, and
`5 * 174.8 = 874`. Lean first checks the resulting natural-number inequality
(`decodeFailureMass_pow_five_le`), then `decodeFailureMass_le_fips203Bound`
casts it to the `ℝ≥0∞` probability bound `fips203DecapsulationFailureBound`.

The evaluation is split across the `FailureCertificate/` modules so no single
elaboration process holds more than one heavy kernel check.
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

/-- The coefficient-noise finite-measure computation satisfies the FIPS 203 Table 1 bound:
the union-bound estimate for the `256` coordinate decode-failure events is at
most the advertised decapsulation-failure probability for the parameter set. -/
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
