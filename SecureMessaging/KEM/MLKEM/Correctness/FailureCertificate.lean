/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.MLKEM.Correctness.FailureCertificate.MLKEM1024
import SecureMessaging.KEM.MLKEM.Correctness.FailureRates

/-!
# The FIPS 203 Table 1 decode-failure certificate

This file evaluates the decode-failure mass of the folded coefficient-noise law
and proves the FIPS 203 Table 1 decapsulation-failure bounds for the three
approved parameter sets.

The evaluation packs a windowed law into one natural number in base `R`
(Kronecker substitution): convolution becomes multiplication (`lawPack_mul`),
iterated convolution becomes a power (`lawPack_pow`), reduction modulo `q`
becomes reduction modulo the repunit `R ^ q - 1` (`sum_mul_pow_mod_repunit`),
and the weighted decode-failure mass becomes one base-`R` digit of one product
(`decodeFailureMass_eq`). The kernel checks each parameter set by evaluating
the packed arithmetic at `R = 2 ^ W`.

The Table 1 exponents have exact fifth parts, so each comparison against
`2 ^ (-e_p)` is decided by an exact integer test on fifth powers
(`decodeFailureMass_pow_five_le`); `decodeFailureMass_le_fips203Bound` casts it
to the `ℝ≥0∞` bound `fips203DecapsulationFailureBound`.

The evaluation is split across the `FailureCertificate/` modules so no single
elaboration process holds more than one heavy kernel check.
-/

open LatticeCrypto
open scoped ENNReal

namespace MLKEM

private theorem decapsulationFailureExponent_mul_five (p : ParameterSet) :
    decapsulationFailureExponent p * 5 = (scaledFailureExponent p : ℚ) := by
  cases p <;> norm_num [decapsulationFailureExponent, scaledFailureExponent]

/-- The exact fifth-power certificate: the bit-summed decode-failure mass of the
folded coefficient-noise law, summed over the `256` coefficients against twice
the total mass, is at most the FIPS 203 Table 1 rate. -/
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
  have hLHS : ((a : ℝ≥0∞) / b) ^ (5 : ℝ) = (↑(a ^ 5) : ℝ≥0∞) / (↑(b ^ 5) : ℝ≥0∞) := by
    rw [ENNReal.div_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 5), cast5, cast5]
    norm_cast
  have hRHS : ((2 : ℝ≥0∞) ^ (-(e : ℝ))) ^ (5 : ℝ) = ((2 ^ E : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [← ENNReal.rpow_mul, neg_mul, h5, ENNReal.rpow_neg, ENNReal.rpow_natCast]
    norm_cast
  rw [hLHS, hRHS,
    ENNReal.div_le_iff (by exact_mod_cast pow_ne_zero 5 hb) (ENNReal.natCast_ne_top _),
    ← ENNReal.mul_le_iff_le_inv (by exact_mod_cast pow_ne_zero E (by norm_num : (2 : ℕ) ≠ 0))
      (ENNReal.natCast_ne_top _), ← Nat.cast_mul, Nat.cast_le, mul_comm (2 ^ E) (a ^ 5)]
  exact h

/-- The certificate laws satisfy the FIPS 203 Table 1 bound: the `256`-fold
bit-averaged decode-failure mass of the folded coefficient-noise law is at most
the decapsulation-failure bound of the parameter set. -/
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
