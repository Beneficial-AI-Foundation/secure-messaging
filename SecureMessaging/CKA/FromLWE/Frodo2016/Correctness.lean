/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Classical.Values
import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Recommended.Values
import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Paranoid.Values
import SecureMessaging.CKA.FromLWE.Frodo2016.Recommended.MomentBound

/-!
# Sharp correctness bounds for the historical Frodo parameter sets

The shared phase theorem and the three kernel-checked certificates give direct first-exchange
bounds for the Classical, Recommended, and Paranoid rows.  The exceptional all-even secret
vectors remain explicit in every bound.
-/

open OracleComp OracleComp.EvalDist
open scoped BigOperators ENNReal

namespace lweCKA

open Frodo2016.Certificate

private theorem totalMass_counts_classical :
    ToVCVio.totalMass (counts classicalConfig) = 2 ^ classicalConfig.seedBits := by
  rw [counts]
  change ToVCVio.totalMassHom
      (∑ z ∈ Finset.Icc (-4 : ℤ) 4,
        AddMonoidAlgebra.single z (d2Weight z)) = 4096
  rw [map_sum]
  have hsingle (z : ℤ) (m : ℕ) :
      ToVCVio.totalMassHom (AddMonoidAlgebra.single z m) = m :=
    ToVCVio.totalMass_single z m
  simp_rw [hsingle]
  have hIcc : Finset.Icc (-4 : ℤ) 4 =
      {-4, -3, -2, -1, 0, 1, 2, 3, 4} := by decide
  rw [hIcc]
  norm_num [d2Weight]

private theorem totalMass_counts_recommended :
    ToVCVio.totalMass (counts recommendedConfig) = 2 ^ recommendedConfig.seedBits := by
  rw [counts]
  change ToVCVio.totalMassHom
      (∑ z ∈ Finset.Icc (-5 : ℤ) 5,
        AddMonoidAlgebra.single z (d3Weight z)) = 4096
  rw [map_sum]
  have hsingle (z : ℤ) (m : ℕ) :
      ToVCVio.totalMassHom (AddMonoidAlgebra.single z m) = m :=
    ToVCVio.totalMass_single z m
  simp_rw [hsingle]
  exact sum_d3Weight

private theorem totalMass_counts_paranoid :
    ToVCVio.totalMass (counts paranoidConfig) = 2 ^ paranoidConfig.seedBits := by
  rw [counts]
  change ToVCVio.totalMassHom
      (∑ z ∈ Finset.Icc (-6 : ℤ) 6,
        AddMonoidAlgebra.single z (d4Weight z)) = 65536
  rw [map_sum]
  have hsingle (z : ℤ) (m : ℕ) :
      ToVCVio.totalMassHom (AddMonoidAlgebra.single z m) = m :=
    ToVCVio.totalMass_single z m
  simp_rw [hsingle]
  have hIcc : Finset.Icc (-6 : ℤ) 6 =
      {-6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6} := by decide
  rw [hIcc]
  norm_num [d4Weight]

private theorem counts_apply_eq_weight
    (c : Config) (z : ℤ)
    (hzero : z ∉ Finset.Icc (-(c.a : ℤ)) (c.a : ℤ) → c.weight z = 0) :
    counts c z = c.weight z := by
  classical
  by_cases hz : z ∈ Finset.Icc (-(c.a : ℤ)) (c.a : ℤ)
  · rw [counts, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
      Finset.sum_eq_single z]
    · simp
    · intro y hy hne
      simp [hne]
    · exact fun h => (h hz).elim
  · rw [hzero hz, counts, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro y hy
    have hne : y ≠ z := fun h => hz (h ▸ hy)
    simp [hne]

private theorem probOutput_d2IntSampler_counts (z : ℤ) :
    Pr[= z | d2IntSampler] =
      (counts classicalConfig z : ℝ≥0∞) / 2 ^ classicalConfig.seedBits := by
  rw [counts_apply_eq_weight classicalConfig z]
  · change Pr[= z | d2IntSampler] = (d2Weight z : ℝ≥0∞) / 2 ^ 12
    convert probOutput_d2IntSampler z using 1
    norm_num
  · intro hz
    change d2Weight z = 0
    have hzsupport : z ∉ support d2IntSampler := by
      rw [support_d2IntSampler]
      simpa [classicalConfig, Set.mem_Icc] using hz
    have hprob := probOutput_eq_zero_of_not_mem_support hzsupport
    rw [probOutput_d2IntSampler] at hprob
    simpa using hprob

private theorem probOutput_d3IntSampler_counts (z : ℤ) :
    Pr[= z | d3IntSampler] =
      (counts recommendedConfig z : ℝ≥0∞) / 2 ^ recommendedConfig.seedBits := by
  rw [counts_apply_eq_weight recommendedConfig z]
  · change Pr[= z | d3IntSampler] = (d3Weight z : ℝ≥0∞) / 2 ^ 12
    convert probOutput_d3IntSampler z using 1
    norm_num
  · intro hz
    change d3Weight z = 0
    have hzsupport : z ∉ support d3IntSampler := by
      rw [support_d3IntSampler]
      simpa [recommendedConfig, Set.mem_Icc] using hz
    have hprob := probOutput_eq_zero_of_not_mem_support hzsupport
    rw [probOutput_d3IntSampler] at hprob
    simpa using hprob

private theorem probOutput_d4IntSampler_counts (z : ℤ) :
    Pr[= z | d4IntSampler] =
      (counts paranoidConfig z : ℝ≥0∞) / 2 ^ paranoidConfig.seedBits := by
  rw [counts_apply_eq_weight paranoidConfig z]
  · change Pr[= z | d4IntSampler] = (d4Weight z : ℝ≥0∞) / 2 ^ 16
    convert probOutput_d4IntSampler z using 1
    norm_num
  · intro hz
    change d4Weight z = 0
    have hzsupport : z ∉ support d4IntSampler := by
      rw [support_d4IntSampler]
      simpa [paranoidConfig, Set.mem_Icc] using hz
    have hprob := probOutput_eq_zero_of_not_mem_support hzsupport
    rw [probOutput_d4IntSampler] at hprob
    simpa using hprob

private theorem probFailure_d2IntSampler : Pr[⊥ | d2IntSampler] = 0 := by
  simp [d2IntSampler]

private theorem probFailure_d4IntSampler : Pr[⊥ | d4IntSampler] = 0 := by
  simp [d4IntSampler]

private theorem d2Weight_neg (z : ℤ) : d2Weight (-z) = d2Weight z := by
  simp [d2Weight]

private theorem d3Weight_neg (z : ℤ) : d3Weight (-z) = d3Weight z := by
  simp [d3Weight]

private theorem d4Weight_neg (z : ℤ) : d4Weight (-z) = d4Weight z := by
  simp [d4Weight]

/-- The D2 sampler assigns exact even mass `2068 / 4096`. -/
theorem probEvent_even_d2IntSampler :
    Pr[fun z : ℤ => Even z | d2IntSampler] = (2068 : ℝ≥0∞) / 4096 := by
  rw [probEvent_eq_tsum_ite, tsum_eq_sum (s := Finset.Icc (-4 : ℤ) 4)]
  · have hIcc : Finset.Icc (-4 : ℤ) 4 =
        {-4, -3, -2, -1, 0, 1, 2, 3, 4} := by decide
    rw [hIcc]
    norm_num [probOutput_d2IntSampler, d2Weight, Int.even_iff]
    have hinv : (4096 : ℝ≥0∞)⁻¹ = 1 / 4096 := by rw [one_div]
    simp only [hinv]
    repeat' rw [ENNReal.div_add_div_same]
    norm_num
  · intro z hz
    have hz' : z ∉ support d2IntSampler := by
      rw [support_d2IntSampler]
      simpa [Set.mem_Icc] using hz
    rw [probOutput_eq_zero_of_not_mem_support hz']
    split <;> simp

/-- The D3 sampler assigns exact even mass `2048 / 4096`. -/
theorem probEvent_even_d3IntSampler :
    Pr[fun z : ℤ => Even z | d3IntSampler] = (2048 : ℝ≥0∞) / 4096 := by
  rw [probEvent_eq_tsum_ite, tsum_eq_sum (s := Finset.Icc (-5 : ℤ) 5)]
  · have hIcc : Finset.Icc (-5 : ℤ) 5 =
        {-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5} := by decide
    rw [hIcc]
    norm_num [probOutput_d3IntSampler, d3Weight, Int.even_iff]
    repeat' rw [ENNReal.div_add_div_same]
    norm_num
  · intro z hz
    have hz' : z ∉ support d3IntSampler := by
      rw [support_d3IntSampler]
      simpa [Set.mem_Icc] using hz
    rw [probOutput_eq_zero_of_not_mem_support hz']
    split <;> simp

/-- The D4 sampler assigns exact even mass `32776 / 65536`. -/
theorem probEvent_even_d4IntSampler :
    Pr[fun z : ℤ => Even z | d4IntSampler] = (32776 : ℝ≥0∞) / 65536 := by
  rw [probEvent_eq_tsum_ite, tsum_eq_sum (s := Finset.Icc (-6 : ℤ) 6)]
  · have hIcc : Finset.Icc (-6 : ℤ) 6 =
        {-6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6} := by decide
    rw [hIcc]
    norm_num [probOutput_d4IntSampler, d4Weight, Int.even_iff]
    have hinv : (65536 : ℝ≥0∞)⁻¹ = 1 / 65536 := by rw [one_div]
    simp only [hinv]
    repeat' rw [ENNReal.div_add_div_same]
    norm_num
  · intro z hz
    have hz' : z ∉ support d4IntSampler := by
      rw [support_d4IntSampler]
      simpa [Set.mem_Icc] using hz
    rw [probOutput_eq_zero_of_not_mem_support hz']
    split <;> simp

/-- Certified first-exchange upper bound for the historical Classical row. -/
noncomputable def classicalFailureBound : ℝ≥0∞ :=
  (7484474965163 : ℝ≥0∞) / 2 ^ 80

/-- Certified first-exchange upper bound for the historical Recommended row. -/
noncomputable def recommendedSharpFailureBound : ℝ≥0∞ :=
  (571563876524 : ℝ≥0∞) / 2 ^ 80

/-- Certified first-exchange upper bound for the historical Paranoid row. -/
noncomputable def paranoidFailureBound : ℝ≥0∞ :=
  (20431578738799 : ℝ≥0∞) / 2 ^ 80

private theorem scaled_even_power_le_dyadic
    (x : ℝ≥0∞) (m k : ℕ)
    (hx : x ≤ (33 : ℝ≥0∞) / 64)
    (hdyadic :
      128 * ((1 : ℝ≥0∞) / 2) ^ m ≤ 1 / (2 : ℝ≥0∞) ^ k) :
    128 * x ^ (2 * m) ≤ 1 / (2 : ℝ≥0∞) ^ k := by
  have hsq : ((33 : ℝ≥0∞) / 64) ^ 2 ≤ (1 : ℝ≥0∞) / 2 := by
    rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_pow, ENNReal.toReal_div]
    norm_num
  calc
    128 * x ^ (2 * m) = 128 * (x ^ 2) ^ m := by rw [pow_mul]
    _ ≤ 128 * (((33 : ℝ≥0∞) / 64) ^ 2) ^ m :=
      mul_le_mul' le_rfl (pow_le_pow_left' (pow_le_pow_left' hx 2) m)
    _ ≤ 128 * ((1 : ℝ≥0∞) / 2) ^ m :=
      mul_le_mul' le_rfl (pow_le_pow_left' hsq m)
    _ ≤ 1 / (2 : ℝ≥0∞) ^ k := hdyadic

private theorem classical_numerical_bound :
    64 *
        (((69032097099755389459452237865466 : ℝ≥0∞) /
            (2 ^ 128 * 2 ^ 12 * (2 * 256)) +
          (2128885962681258 : ℝ≥0∞) / 2 ^ 128) +
          2 * ((2068 : ℝ≥0∞) / 4096) ^ 592) ≤ classicalFailureBound := by
  have hbase : (2068 : ℝ≥0∞) / 4096 ≤ 33 / 64 := by
    rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
    norm_num
  have hdyadic :
      128 * ((1 : ℝ≥0∞) / 2) ^ 296 ≤ 1 / (2 : ℝ≥0∞) ^ 82 := by
    have hpow : (2 : ℝ≥0∞) ^ (82 + 7) ≤ 2 ^ 296 :=
      pow_le_pow_right₀ (by norm_num) (by norm_num)
    have hfrac : (1 : ℝ≥0∞) / 2 ^ 296 ≤ 1 / 2 ^ (82 + 7) :=
      ENNReal.div_le_div_left hpow 1
    have hpowfrac : ((1 : ℝ≥0∞) / 2) ^ 296 ≤ 1 / 2 ^ (82 + 7) := by
      simpa only [one_div, ENNReal.inv_pow] using hfrac
    calc
      _ ≤ 128 * (1 / (2 : ℝ≥0∞) ^ (82 + 7)) :=
        mul_le_mul' le_rfl hpowfrac
      _ ≤ 1 / (2 : ℝ≥0∞) ^ 82 := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow]
        norm_num
  have htail :
      64 * (2 * ((2068 : ℝ≥0∞) / 4096) ^ 592) ≤
        1 / (2 : ℝ≥0∞) ^ 82 := by
    calc
      64 * (2 * ((2068 : ℝ≥0∞) / 4096) ^ 592) =
          128 * ((2068 : ℝ≥0∞) / 4096) ^ (2 * 296) := by ring
      _ ≤ 1 / (2 : ℝ≥0∞) ^ 82 :=
        scaled_even_power_le_dyadic _ 296 82 hbase hdyadic
  unfold classicalFailureBound
  calc
    _ = 64 *
          ((69032097099755389459452237865466 : ℝ≥0∞) /
              (2 ^ 128 * 2 ^ 12 * (2 * 256)) +
            (2128885962681258 : ℝ≥0∞) / 2 ^ 128) +
        64 * (2 * ((2068 : ℝ≥0∞) / 4096) ^ 592) := by
      rw [mul_add]
    _ ≤ 64 *
          ((69032097099755389459452237865466 : ℝ≥0∞) /
              (2 ^ 128 * 2 ^ 12 * (2 * 256)) +
            (2128885962681258 : ℝ≥0∞) / 2 ^ 128) +
        1 / (2 : ℝ≥0∞) ^ 82 := add_le_add le_rfl htail
    _ ≤ (7484474965163 : ℝ≥0∞) / 2 ^ 80 := by
      rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
      rw [ENNReal.toReal_add (by finiteness) (by finiteness),
        ENNReal.toReal_mul,
        ENNReal.toReal_add (by finiteness) (by finiteness)]
      simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_mul]
      norm_num

private theorem recommended_numerical_bound :
    64 *
        (((10543492551966859497706958378128 : ℝ≥0∞) /
            (2 ^ 128 * 2 ^ 12 * (2 * 512)) +
          (8988175038920 : ℝ≥0∞) / 2 ^ 128) +
          2 * ((2048 : ℝ≥0∞) / 4096) ^ 752) ≤
      recommendedSharpFailureBound := by
  have hbase : (2048 : ℝ≥0∞) / 4096 ≤ 33 / 64 := by
    rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
    norm_num
  have hdyadic :
      128 * ((1 : ℝ≥0∞) / 2) ^ 376 ≤ 1 / (2 : ℝ≥0∞) ^ 81 := by
    have hpow : (2 : ℝ≥0∞) ^ (81 + 7) ≤ 2 ^ 376 :=
      pow_le_pow_right₀ (by norm_num) (by norm_num)
    have hfrac : (1 : ℝ≥0∞) / 2 ^ 376 ≤ 1 / 2 ^ (81 + 7) :=
      ENNReal.div_le_div_left hpow 1
    have hpowfrac : ((1 : ℝ≥0∞) / 2) ^ 376 ≤ 1 / 2 ^ (81 + 7) := by
      simpa only [one_div, ENNReal.inv_pow] using hfrac
    calc
      _ ≤ 128 * (1 / (2 : ℝ≥0∞) ^ (81 + 7)) :=
        mul_le_mul' le_rfl hpowfrac
      _ ≤ 1 / (2 : ℝ≥0∞) ^ 81 := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow]
        norm_num
  have htail :
      64 * (2 * ((2048 : ℝ≥0∞) / 4096) ^ 752) ≤
        1 / (2 : ℝ≥0∞) ^ 81 := by
    calc
      64 * (2 * ((2048 : ℝ≥0∞) / 4096) ^ 752) =
          128 * ((2048 : ℝ≥0∞) / 4096) ^ (2 * 376) := by ring
      _ ≤ 1 / (2 : ℝ≥0∞) ^ 81 :=
        scaled_even_power_le_dyadic _ 376 81 hbase hdyadic
  unfold recommendedSharpFailureBound
  calc
    _ = 64 *
          ((10543492551966859497706958378128 : ℝ≥0∞) /
              (2 ^ 128 * 2 ^ 12 * (2 * 512)) +
            (8988175038920 : ℝ≥0∞) / 2 ^ 128) +
        64 * (2 * ((2048 : ℝ≥0∞) / 4096) ^ 752) := by
      rw [mul_add]
    _ ≤ 64 *
          ((10543492551966859497706958378128 : ℝ≥0∞) /
              (2 ^ 128 * 2 ^ 12 * (2 * 512)) +
            (8988175038920 : ℝ≥0∞) / 2 ^ 128) +
        1 / (2 : ℝ≥0∞) ^ 81 := add_le_add le_rfl htail
    _ ≤ (571563876524 : ℝ≥0∞) / 2 ^ 80 := by
      rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
      rw [ENNReal.toReal_add (by finiteness) (by finiteness),
        ENNReal.toReal_mul,
        ENNReal.toReal_add (by finiteness) (by finiteness)]
      simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_mul]
      norm_num

private theorem paranoid_numerical_bound :
    64 *
        (((6030337663305705867094998372466972 : ℝ≥0∞) /
            (2 ^ 128 * 2 ^ 16 * (2 * 512)) +
          (14272300219351570 : ℝ≥0∞) / 2 ^ 128) +
          2 * ((32776 : ℝ≥0∞) / 65536) ^ 864) ≤ paranoidFailureBound := by
  have hbase : (32776 : ℝ≥0∞) / 65536 ≤ 33 / 64 := by
    rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
    norm_num
  have hdyadic :
      128 * ((1 : ℝ≥0∞) / 2) ^ 432 ≤ 1 / (2 : ℝ≥0∞) ^ 84 := by
    have hpow : (2 : ℝ≥0∞) ^ (84 + 7) ≤ 2 ^ 432 :=
      pow_le_pow_right₀ (by norm_num) (by norm_num)
    have hfrac : (1 : ℝ≥0∞) / 2 ^ 432 ≤ 1 / 2 ^ (84 + 7) :=
      ENNReal.div_le_div_left hpow 1
    have hpowfrac : ((1 : ℝ≥0∞) / 2) ^ 432 ≤ 1 / 2 ^ (84 + 7) := by
      simpa only [one_div, ENNReal.inv_pow] using hfrac
    calc
      _ ≤ 128 * (1 / (2 : ℝ≥0∞) ^ (84 + 7)) :=
        mul_le_mul' le_rfl hpowfrac
      _ ≤ 1 / (2 : ℝ≥0∞) ^ 84 := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow]
        norm_num
  have htail :
      64 * (2 * ((32776 : ℝ≥0∞) / 65536) ^ 864) ≤
        1 / (2 : ℝ≥0∞) ^ 84 := by
    calc
      64 * (2 * ((32776 : ℝ≥0∞) / 65536) ^ 864) =
          128 * ((32776 : ℝ≥0∞) / 65536) ^ (2 * 432) := by ring
      _ ≤ 1 / (2 : ℝ≥0∞) ^ 84 :=
        scaled_even_power_le_dyadic _ 432 84 hbase hdyadic
  unfold paranoidFailureBound
  calc
    _ = 64 *
          ((6030337663305705867094998372466972 : ℝ≥0∞) /
              (2 ^ 128 * 2 ^ 16 * (2 * 512)) +
            (14272300219351570 : ℝ≥0∞) / 2 ^ 128) +
        64 * (2 * ((32776 : ℝ≥0∞) / 65536) ^ 864) := by
      rw [mul_add]
    _ ≤ 64 *
          ((6030337663305705867094998372466972 : ℝ≥0∞) /
              (2 ^ 128 * 2 ^ 16 * (2 * 512)) +
            (14272300219351570 : ℝ≥0∞) / 2 ^ 128) +
        1 / (2 : ℝ≥0∞) ^ 84 := add_le_add le_rfl htail
    _ ≤ (20431578738799 : ℝ≥0∞) / 2 ^ 80 := by
      rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
      rw [ENNReal.toReal_add (by finiteness) (by finiteness),
        ENNReal.toReal_mul,
        ENNReal.toReal_add (by finiteness) (by finiteness)]
      simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_mul]
      norm_num

/-- The Classical first exchange obeys the sharp historical certificate bound. -/
theorem firstExchangeFailureProb_classical_le :
    firstExchangeFailureProb classicalParams d2Sampler ≤ classicalFailureBound := by
  have hramp := expectedValue_ramp_le_certificate
    classicalConfig classicalParams classicalParams_wellFormed d2IntSampler
    probFailure_d2IntSampler (by norm_num [classicalParams, classicalConfig])
    (by norm_num [classicalParams, classicalConfig, Params.discardBits])
    (by norm_num [classicalConfig]) totalMass_counts_classical
    probOutput_d2IntSampler_counts
    (by simpa [classicalConfig] using d2Weight_neg)
    (by norm_num [classicalParams, classicalConfig, Params.q])
    (by norm_num [classicalConfig])
  rw [classical_certificateValues] at hramp
  calc
    firstExchangeFailureProb classicalParams d2Sampler ≤
        (64 : ℕ) *
          (expectedValue (entryNoiseIntExp classicalParams.n d2IntSampler)
              (reconciliationFailureRamp classicalParams) +
            2 * Pr[fun z : ℤ => Even z | d2IntSampler] ^ classicalParams.n) := by
      simpa [d2Sampler, classicalParams] using
        firstExchangeFailureProb_le_ramp classicalParams classicalParams_wellFormed
          d2IntSampler probFailure_d2IntSampler
    _ ≤ 64 *
        (((69032097099755389459452237865466 : ℝ≥0∞) /
            (2 ^ 128 * 2 ^ 12 * (2 * 256)) +
          (2128885962681258 : ℝ≥0∞) / 2 ^ 128) +
          2 * ((2068 : ℝ≥0∞) / 4096) ^ 592) := by
      rw [probEvent_even_d2IntSampler]
      exact mul_le_mul' le_rfl (add_le_add hramp le_rfl)
    _ ≤ classicalFailureBound := by
      exact classical_numerical_bound

/-- The Recommended first exchange obeys the improved sharp certificate bound. -/
theorem firstExchangeFailureProb_recommended_sharp_le :
    firstExchangeFailureProb recommendedParams d3Sampler ≤
      recommendedSharpFailureBound := by
  have hramp := expectedValue_ramp_le_certificate
    recommendedConfig recommendedParams recommendedParams_wellFormed d3IntSampler
    probFailure_d3IntSampler (by norm_num [recommendedParams, recommendedConfig])
    (by norm_num [recommendedParams, recommendedConfig, Params.discardBits])
    (by norm_num [recommendedConfig]) totalMass_counts_recommended
    probOutput_d3IntSampler_counts
    (by simpa [recommendedConfig] using d3Weight_neg)
    (by norm_num [recommendedParams, recommendedConfig, Params.q])
    (by norm_num [recommendedConfig])
  rw [recommended_certificateValues] at hramp
  calc
    firstExchangeFailureProb recommendedParams d3Sampler ≤
        (64 : ℕ) *
          (expectedValue (entryNoiseIntExp recommendedParams.n d3IntSampler)
              (reconciliationFailureRamp recommendedParams) +
            2 * Pr[fun z : ℤ => Even z | d3IntSampler] ^ recommendedParams.n) := by
      simpa [d3Sampler, recommendedParams] using
        firstExchangeFailureProb_le_ramp recommendedParams recommendedParams_wellFormed
          d3IntSampler probFailure_d3IntSampler
    _ ≤ 64 *
        (((10543492551966859497706958378128 : ℝ≥0∞) /
            (2 ^ 128 * 2 ^ 12 * (2 * 512)) +
          (8988175038920 : ℝ≥0∞) / 2 ^ 128) +
          2 * ((2048 : ℝ≥0∞) / 4096) ^ 752) := by
      rw [probEvent_even_d3IntSampler]
      exact mul_le_mul' le_rfl (add_le_add hramp le_rfl)
    _ ≤ recommendedSharpFailureBound := by
      exact recommended_numerical_bound

/-- The Paranoid first exchange obeys the sharp historical certificate bound. -/
theorem firstExchangeFailureProb_paranoid_le :
    firstExchangeFailureProb paranoidParams d4Sampler ≤ paranoidFailureBound := by
  have hramp := expectedValue_ramp_le_certificate
    paranoidConfig paranoidParams paranoidParams_wellFormed d4IntSampler
    probFailure_d4IntSampler (by norm_num [paranoidParams, paranoidConfig])
    (by norm_num [paranoidParams, paranoidConfig, Params.discardBits])
    (by norm_num [paranoidConfig]) totalMass_counts_paranoid
    probOutput_d4IntSampler_counts
    (by simpa [paranoidConfig] using d4Weight_neg)
    (by norm_num [paranoidParams, paranoidConfig, Params.q])
    (by norm_num [paranoidConfig])
  rw [paranoid_certificateValues] at hramp
  calc
    firstExchangeFailureProb paranoidParams d4Sampler ≤
        (64 : ℕ) *
          (expectedValue (entryNoiseIntExp paranoidParams.n d4IntSampler)
              (reconciliationFailureRamp paranoidParams) +
            2 * Pr[fun z : ℤ => Even z | d4IntSampler] ^ paranoidParams.n) := by
      simpa [d4Sampler, paranoidParams] using
        firstExchangeFailureProb_le_ramp paranoidParams paranoidParams_wellFormed
          d4IntSampler probFailure_d4IntSampler
    _ ≤ 64 *
        (((6030337663305705867094998372466972 : ℝ≥0∞) /
            (2 ^ 128 * 2 ^ 16 * (2 * 512)) +
          (14272300219351570 : ℝ≥0∞) / 2 ^ 128) +
          2 * ((32776 : ℝ≥0∞) / 65536) ^ 864) := by
      rw [probEvent_even_d4IntSampler]
      exact mul_le_mul' le_rfl (add_le_add hramp le_rfl)
    _ ≤ paranoidFailureBound := by
      exact paranoid_numerical_bound

/-- The new Recommended endpoint strictly improves the preserved conservative endpoint. -/
theorem recommendedSharpFailureBound_lt_recommendedFailureBound :
    recommendedSharpFailureBound < recommendedFailureBound := by
  unfold recommendedSharpFailureBound recommendedFailureBound
  rw [ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  rw [show (2 : ℝ≥0∞) ^ 80 = 562949953421312 * 2147483648 by norm_num,
    ← mul_assoc, ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
  norm_num

/-- Correctness failure for at most `T` Classical exchanges. -/
theorem correctness_failure_classical_le
    (adv : CKAScheme.CKACorrectnessAdversary
      (Message classicalParams) (Key classicalParams))
    (T : ℕ)
    (hT : HasExchangeBound classicalParams
      classicalParams_wellFormed d2Sampler adv T) :
    Pr[= false |
      CKAScheme.correctnessExp
        (scheme classicalParams classicalParams_wellFormed d2Sampler) adv] ≤
      min 1 ((T : ℝ≥0∞) * classicalFailureBound) := by
  refine le_trans (correctness_failure_le classicalParams
    classicalParams_wellFormed d2Sampler adv T hT) ?_
  exact min_le_min le_rfl (mul_le_mul' le_rfl firstExchangeFailureProb_classical_le)

/-- Correctness failure for at most `T` Recommended exchanges at the sharp endpoint. -/
theorem correctness_failure_recommended_sharp_le
    (adv : CKAScheme.CKACorrectnessAdversary
      (Message recommendedParams) (Key recommendedParams))
    (T : ℕ)
    (hT : HasExchangeBound recommendedParams
      recommendedParams_wellFormed d3Sampler adv T) :
    Pr[= false |
      CKAScheme.correctnessExp
        (scheme recommendedParams recommendedParams_wellFormed d3Sampler) adv] ≤
      min 1 ((T : ℝ≥0∞) * recommendedSharpFailureBound) := by
  refine le_trans (correctness_failure_le recommendedParams
    recommendedParams_wellFormed d3Sampler adv T hT) ?_
  exact min_le_min le_rfl
    (mul_le_mul' le_rfl firstExchangeFailureProb_recommended_sharp_le)

/-- Correctness failure for at most `T` Paranoid exchanges. -/
theorem correctness_failure_paranoid_le
    (adv : CKAScheme.CKACorrectnessAdversary
      (Message paranoidParams) (Key paranoidParams))
    (T : ℕ)
    (hT : HasExchangeBound paranoidParams
      paranoidParams_wellFormed d4Sampler adv T) :
    Pr[= false |
      CKAScheme.correctnessExp
        (scheme paranoidParams paranoidParams_wellFormed d4Sampler) adv] ≤
      min 1 ((T : ℝ≥0∞) * paranoidFailureBound) := by
  refine le_trans (correctness_failure_le paranoidParams
    paranoidParams_wellFormed d4Sampler adv T hT) ?_
  exact min_le_min le_rfl (mul_le_mul' le_rfl firstExchangeFailureProb_paranoid_le)

end lweCKA
