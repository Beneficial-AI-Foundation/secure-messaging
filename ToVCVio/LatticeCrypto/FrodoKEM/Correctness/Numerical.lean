/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Counts
public import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Certificate.Frodo640
public import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Certificate.Frodo976
public import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Certificate.Frodo1344

/-!
# Numerical correctness bounds for independently sampled FrodoKEM errors

This file turns the three certificates into failure bounds for FrodoPKE with independently
sampled errors. The comparison raises both sides to the tenth power. Thus an exponent `e` of
Table 4 of `[CiC25]`, such as `138.7`, gives a comparison of whole numbers, since `10 * e` is
whole. This file makes no claim about SHAKE.

## References

* `[CiC25]`, Glabush, Longa, Naehrig, Peikert, Stebila and Virdia, *FrodoKEM: A
  CCA-Secure Learning With Errors Key Encapsulation Mechanism*, IACR
  Communications in Cryptology 2:3, <https://cic.iacr.org/p/2/3/25>.
-/

@[expose] public section

namespace FrodoKEM.Certificate

open OracleComp
open scoped ENNReal

set_option maxRecDepth 8192 in
set_option exponentiation.threshold 4096 in
/-- For each size, the bound meets the exponent of Table 4 of `[CiC25]`. The comparison raises
both sides to the tenth power. -/
theorem numerator_tenth_power_le (ps : ParameterSet) :
    numerator ps ^ 10 * 2 ^ exponentTenths ps ≤
      2 ^ (10 * (precision ps + lenChi)) := by
  cases ps <;> decide

/-- `numerator_tenth_power_le`, stated for `failureBound` as a probability. -/
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

/-- The salted parameter set of the same size. Each eFrodoKEM set has the same certificate
parameters as its salted twin, so one certificate covers both. -/
private def salted : ParameterSet → ParameterSet
  | .FrodoKEM640 | .eFrodoKEM640 => .FrodoKEM640
  | .FrodoKEM976 | .eFrodoKEM976 => .FrodoKEM976
  | .FrodoKEM1344 | .eFrodoKEM1344 => .FrodoKEM1344

private theorem certificateValues_salted (ps : ParameterSet) :
    FailureCertificate.RoundedConvolution.certificateValues (config ps) (badWeight ps) =
      FailureCertificate.RoundedConvolution.certificateValues
        (config (salted ps)) (badWeight (salted ps)) := by
  cases ps <;> rfl

private theorem matrixBound_eq (ps : ParameterSet) :
    64 *
      (((FailureCertificate.RoundedConvolution.certificateValues
          (config ps) (badWeight ps)).1 : ℝ≥0∞) / 2 ^ (precision ps + lenChi) +
        ((FailureCertificate.RoundedConvolution.certificateValues
          (config ps) (badWeight ps)).2 : ℝ≥0∞) / 2 ^ precision ps) =
      failureBound ps := by
  rw [certificateValues_salted]
  cases ps <;> dsimp only [salted] <;>
    first | rw [certificate640] | rw [certificate976] | rw [certificate1344]
  all_goals exact blockBound_eq _ _ _

/-- With independent noise, large decryption noise has probability at most `failureBound`. -/
-- ANCHOR: frodoKEM_certificate
theorem noiseBadProb_le_failureBound (ps : ParameterSet) :
    IndepNoise.noiseBadProb ps ≤ failureBound ps
-- ANCHOR_END: frodoKEM_certificate
    := by
  have hbits : 0 < (config ps).seedBits := by cases ps <;> decide
  have hlaw (z : ℤ) :
      Pr{let x ← IndepNoise.entryNoiseExp ps}[x = z] =
        (((ToVCVio.productMeasure
            (FailureCertificate.RoundedConvolution.counts (config ps))
            (FailureCertificate.RoundedConvolution.counts (config ps))) ^
            (config ps).steps *
          FailureCertificate.RoundedConvolution.counts (config ps)) z : ℝ≥0∞) /
          (2 ^ (config ps).seedBits) ^ (2 * (config ps).steps + 1) := by
    simpa only [config, ← Nat.mul_assoc] using probOutput_entryNoiseExp ps z
  have hentry := FailureCertificate.RoundedConvolution.probEvent_le_certificate
    (config ps) (IndepNoise.entryNoiseExp ps) (IndepNoise.entryBad ps)
    hbits (counts_totalMass ps) hlaw
  calc
    IndepNoise.noiseBadProb ps ≤ 64 * IndepNoise.entryFailureProb ps :=
        IndepNoise.noiseBadProb_le ps
    _ ≤ 64 *
        (((FailureCertificate.RoundedConvolution.certificateValues
            (config ps) (badWeight ps)).1 : ℝ≥0∞) / 2 ^ (precision ps + lenChi) +
          ((FailureCertificate.RoundedConvolution.certificateValues
            (config ps) (badWeight ps)).2 : ℝ≥0∞) / 2 ^ precision ps) :=
      mul_le_mul' le_rfl hentry
    _ = failureBound ps := matrixBound_eq ps

/-- With independent errors, the PKE failure probability is at most `failureBound`, for every
message. -/
theorem pkeFailureProb_le_failureBound (ps : ParameterSet)
    (A : FrodoMatrix ps.params ps.params.n ps.params.n)
    (message : MessageBits ps) :
    IndepNoise.pkeFailureProb ps A message ≤ failureBound ps :=
  (IndepNoise.pkeFailureProb_le_noiseBadProb ps A message).trans (noiseBadProb_le_failureBound ps)

/-- With independent errors, the PKE failure probability `p` satisfies
`p ^ 10 * 2 ^ exponentTenths ps ≤ 1`, that is, `p ≤ 2 ^ (-exponentTenths ps / 10)`. -/
theorem pkeFailureProb_tenth_power_le (ps : ParameterSet)
    (A : FrodoMatrix ps.params ps.params.n ps.params.n)
    (message : MessageBits ps) :
    IndepNoise.pkeFailureProb ps A message ^ 10 *
      2 ^ exponentTenths ps ≤ 1 :=
  (mul_le_mul' (pow_le_pow_left' (pkeFailureProb_le_failureBound ps A message) 10)
    le_rfl).trans (failureBound_tenth_power_le ps)

end FrodoKEM.Certificate
