/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Counts
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Certificate.Frodo640
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Certificate.Frodo976
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Certificate.Frodo1344

/-!
# Numerical correctness bounds for independently sampled FrodoKEM errors

The three kernel certificates bound the actual PKE decryption experiment with independent error
streams. Tenth powers express the published fractional-bit exponents using exact integer arithmetic.
No numerical claim about an arbitrary seeded SHAKE operation is made here.
-/

namespace FrodoKEM.Certificate

open OracleComp
open scoped ENNReal

set_option maxRecDepth 8192 in
set_option exponentiation.threshold 4096 in
/-- Each rational certificate meets its exact fractional-bit target. -/
theorem numerator_tenth_power_le (ps : ParameterSet) :
    numerator ps ^ 10 * 2 ^ exponentTenths ps ≤
      2 ^ (10 * (precision ps + lenChi)) := by
  cases ps <;> decide

/-- The certificate bounds satisfy the fractional-bit inequalities as extended probabilities. -/
theorem failureBound_tenth_power_le (ps : ParameterSet) :
    failureBound ps ^ 10 * 2 ^ exponentTenths ps ≤ 1 := by
  have h : (numerator ps : ℝ≥0∞) ^ 10 * 2 ^ exponentTenths ps ≤
      2 ^ (10 * (precision ps + lenChi)) := by
    exact_mod_cast numerator_tenth_power_le ps
  rw [failureBound, div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow, mul_right_comm,
    ENNReal.mul_inv_le_iff (by positivity) (by simp), one_mul]
  simpa only [← pow_mul, Nat.mul_comm] using h

private theorem blockBound_eq (a b P : ℕ) :
    64 * ((a : ℝ≥0∞) / 2 ^ (P + 16) + (b : ℝ≥0∞) / 2 ^ P) =
      ((64 * (a + 65536 * b) : ℕ) : ℝ≥0∞) / 2 ^ (P + 16) := by
  simp only [pow_add]
  rw [← ENNReal.mul_div_mul_right (b : ℝ≥0∞) (2 ^ P)
    (c := 2 ^ 16) (by norm_num) (by simp)]
  rw [ENNReal.div_add_div_same, ← mul_div_assoc]
  congr 1
  norm_num [Nat.cast_mul, Nat.cast_add, mul_comm]

private theorem matrixBound_eq (ps : ParameterSet) :
    64 *
      (((FailureCertificate.RoundedConvolution.certificateValues
          (config ps) (badWeight ps)).1 : ℝ≥0∞) / 2 ^ (precision ps + lenChi) +
        ((FailureCertificate.RoundedConvolution.certificateValues
          (config ps) (badWeight ps)).2 : ℝ≥0∞) / 2 ^ precision ps) =
      failureBound ps := by
  have he640 : FailureCertificate.RoundedConvolution.certificateValues
      (config .eFrodoKEM640) (badWeight .eFrodoKEM640) =
        (10891243206164296039, 4220411) := certificate640
  have he976 : FailureCertificate.RoundedConvolution.certificateValues
      (config .eFrodoKEM976) (badWeight .eFrodoKEM976) =
        (97175197777440479084, 6213051) := certificate976
  have he1344 : FailureCertificate.RoundedConvolution.certificateValues
      (config .eFrodoKEM1344) (badWeight .eFrodoKEM1344) =
        (198663617378549905966698, 4264645) := certificate1344
  cases ps <;>
    first | rw [certificate640] | rw [certificate976] | rw [certificate1344]
          | rw [he640] | rw [he976] | rw [he1344]
  all_goals first
    | exact blockBound_eq 10891243206164296039 4220411 192
    | exact blockBound_eq 97175197777440479084 6213051 256
    | exact blockBound_eq 198663617378549905966698 4264645 320

/-- The residual matrix bad event is bounded by the corresponding checked certificate. -/
theorem noiseBadProb_le_failureBound (ps : ParameterSet) :
    Ideal.noiseBadProb ps ≤ failureBound ps := by
  have hbits : 0 < (config ps).seedBits := by cases ps <;> decide
  have hlaw (z : ℤ) :
      Pr{let x ← Ideal.entryNoiseExp ps}[x = z] =
        (((ToVCVio.productMeasure
            (FailureCertificate.RoundedConvolution.counts (config ps))
            (FailureCertificate.RoundedConvolution.counts (config ps))) ^
            (config ps).steps *
          FailureCertificate.RoundedConvolution.counts (config ps)) z : ℝ≥0∞) /
          (2 ^ (config ps).seedBits) ^ (2 * (config ps).steps + 1) := by
    simpa only [config, ← Nat.mul_assoc] using probOutput_entryNoiseExp ps z
  have hentry := FailureCertificate.RoundedConvolution.probEvent_le_certificate
    (config ps) (Ideal.entryNoiseExp ps) (Ideal.entryBad ps)
    hbits (counts_totalMass ps) hlaw
  calc
    Ideal.noiseBadProb ps ≤ 64 * Ideal.entryFailureProb ps := Ideal.noiseBadProb_le ps
    _ ≤ 64 *
        (((FailureCertificate.RoundedConvolution.certificateValues
            (config ps) (badWeight ps)).1 : ℝ≥0∞) / 2 ^ (precision ps + lenChi) +
          ((FailureCertificate.RoundedConvolution.certificateValues
            (config ps) (badWeight ps)).2 : ℝ≥0∞) / 2 ^ precision ps) :=
      mul_le_mul' le_rfl hentry
    _ = failureBound ps := matrixBound_eq ps

/-- Ideal independent-error PKE decryption meets the checked rational bound for every message. -/
theorem pkeFailureProb_le_failureBound (ps : ParameterSet)
    (A : FrodoMatrix ps.params ps.params.n ps.params.n)
    (message : MessageBits ps) :
    Ideal.pkeFailureProb ps A message ≤ failureBound ps :=
  (Ideal.pkeFailureProb_le_noiseBadProb ps A message).trans (noiseBadProb_le_failureBound ps)

/-- Ideal independent-error PKE decryption meets all three exact fractional-bit targets. -/
theorem pkeFailureProb_tenth_power_le (ps : ParameterSet)
    (A : FrodoMatrix ps.params ps.params.n ps.params.n)
    (message : MessageBits ps) :
    Ideal.pkeFailureProb ps A message ^ 10 *
      2 ^ exponentTenths ps ≤ 1 :=
  (mul_le_mul' (pow_le_pow_left' (pkeFailureProb_le_failureBound ps A message) 10)
    le_rfl).trans (failureBound_tenth_power_le ps)

end FrodoKEM.Certificate
