/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Sampling
import SecureMessaging.KEM.MLKEM.Correctness.FailureCertificate.Radix
import VCVio.ProgramLogic.Unary.HoareTriple
import VCVio.EvalDist.Monad.Seq

/-!
# Discrete count model for the Frodo Challenge certificate

This unit defines the exact one-dimensional and product counting measures,
proves their sampling laws, and connects the concrete product pack to the
semantic measure pack.
-/

open OracleComp
open scoped BigOperators ENNReal

namespace lweCKA.ChallengeCertificateModel

namespace ChallengeModelInternal
end ChallengeModelInternal

open ChallengeModelInternal

set_option Elab.async false in
section

/-- The exact integer scaling factor used by the rounded counting measure. -/
def scale : Nat := 2 ^ 128

/-- The radix used to pack all coefficients of the rounded measure. -/
def radix : Nat := 2 ^ 145

/-- The packed coefficient vector of the one-step product distribution. -/
def productPack : Nat :=
  18 + 240 * radix ^ 3 + 800 * radix ^ 5 + 732 * radix ^ 6 +
  4880 * radix ^ 7 + 7442 * radix ^ 8 + 37312 * radix ^ 9 +
  7442 * radix ^ 10 + 4880 * radix ^ 11 + 732 * radix ^ 12 +
  800 * radix ^ 13 + 240 * radix ^ 15 + 18 * radix ^ 18

/-- The packed coefficient vector of the final additive error distribution. -/
def extraPack : Nat :=
  3 + 20 * radix + 61 * radix ^ 2 + 88 * radix ^ 3 +
  61 * radix ^ 4 + 20 * radix ^ 5 + 3 * radix ^ 6

/-- The exact integer counting measure for one centered one-dimensional sample. -/
noncomputable def d1Counts : ToVCVio.IntMeasure :=
  ∑ z ∈ Finset.Icc (-3 : ℤ) 3,
    AddMonoidAlgebra.single z (d1Weight z)

/-- The convolution counting measure for one product of two samples. -/
noncomputable def productCounts : ToVCVio.IntMeasure :=
  ToVCVio.productMeasure d1Counts d1Counts

/-- The recursively rounded lower counting measure after each convolution step. -/
noncomputable def lowerCounts : Nat → ToVCVio.IntMeasure
  | 0 => AddMonoidAlgebra.single 0 scale
  | n + 1 => ∑ z ∈ Finset.Icc (-384 : ℤ) 384,
      AddMonoidAlgebra.single z
        (((lowerCounts n * productCounts) z) / 65536)

private def productWeight (z : ℤ) : Nat :=
  match z.natAbs with
  | 0 => 37312
  | 1 => 7442
  | 2 => 4880
  | 3 => 732
  | 4 => 800
  | 6 => 240
  | 9 => 18
  | _ => 0

private theorem intIcc_neg3_3 :
    Finset.Icc (-3 : ℤ) 3 = {-3, -2, -1, 0, 1, 2, 3} := by
  ext z
  simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  omega

theorem ChallengeModelInternal.d1Counts_apply (z : ℤ) :
    d1Counts z = d1Weight z := by
  classical
  rw [d1Counts, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  by_cases hz : z ∈ Finset.Icc (-3 : ℤ) 3
  · rw [Finset.sum_eq_single z]
    · simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
    · intro b hb hne
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hne, ite_false]
    · exact fun h => (h hz).elim
  · have hweight : d1Weight z = 0 := by
      have hnot : z ∉ Set.Icc (-3 : ℤ) 3 := by simpa using hz
      rw [← support_d1IntSampler] at hnot
      rw [mem_support_iff, probOutput_d1IntSampler] at hnot
      simpa using hnot
    rw [hweight]
    apply Finset.sum_eq_zero
    intro b hb
    have hne : b ≠ z := by
      intro h
      exact hz (h ▸ hb)
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hne, ite_false]

private theorem d1Weight_ne_zero_iff (z : ℤ) :
    d1Weight z ≠ 0 ↔ z ∈ Finset.Icc (-3 : ℤ) 3 := by
  constructor
  · intro hw
    have hp : Pr{let x ← d1IntSampler}[x = z] ≠ 0 := by
      rw [probOutput_d1IntSampler]
      exact ENNReal.div_ne_zero.mpr ⟨Nat.cast_ne_zero.mpr hw, by norm_num⟩
    have hs : z ∈ support d1IntSampler :=
      (mem_support_iff d1IntSampler z).mpr hp
    simpa only [support_d1IntSampler, Set.mem_Icc, Finset.mem_Icc] using hs
  · intro hz hw
    have hs : z ∈ support d1IntSampler := by
      rw [support_d1IntSampler]
      simpa only [Set.mem_Icc, Finset.mem_Icc] using hz
    have hp := (mem_support_iff d1IntSampler z).mp hs
    rw [probOutput_d1IntSampler, hw] at hp
    simp at hp

private theorem support_d1Counts :
    d1Counts.coeff.support = Finset.Icc (-3 : ℤ) 3 := by
  ext z
  rw [Finsupp.mem_support_iff, d1Counts_apply, d1Weight_ne_zero_iff]

theorem ChallengeModelInternal.measureWindow_d1Counts :
    ToVCVio.MeasureWindow d1Counts (-3) 3 := by
  intro z hz
  rw [d1Counts_apply] at hz
  have hp : 0 < Pr{let x ← d1IntSampler}[x = z] := by
    rw [probOutput_d1IntSampler]
    exact ENNReal.div_pos (Nat.cast_ne_zero.mpr hz) (by norm_num)
  have hs : z ∈ support d1IntSampler :=
    (mem_support_iff d1IntSampler z).mpr (ne_of_gt hp)
  simpa only [support_d1IntSampler, Set.mem_Icc] using hs

theorem ChallengeModelInternal.extraPack_eq_measurePack :
    MLKEM.measurePack radix (-3) d1Counts = extraPack := by
  rw [MLKEM.measurePack_eq_range_sum
    (show ToVCVio.MeasureWindow d1Counts (-3) (-3 + (7 : ℤ) - 1) by
      norm_num
      exact measureWindow_d1Counts)]
  rw [extraPack]
  generalize radix = R
  norm_num [d1Counts_apply, d1Weight, Finset.sum_range_succ]

theorem ChallengeModelInternal.totalMass_d1Counts :
    ToVCVio.totalMass d1Counts = 256 := by
  rw [MLKEM.totalMass_eq_range_sum
    (show ToVCVio.MeasureWindow d1Counts (-3) (-3 + (7 : ℤ) - 1) by
      norm_num
      exact measureWindow_d1Counts)]
  norm_num [d1Counts_apply, d1Weight, Finset.sum_range_succ]

/-- The product counting measure is supported on the interval from minus nine to nine. -/
theorem measureWindow_productCounts :
    ToVCVio.MeasureWindow productCounts (-9) 9 := by
  simpa [productCounts] using
    ToVCVio.measureWindow_productMeasure measureWindow_d1Counts measureWindow_d1Counts

theorem ChallengeModelInternal.totalMass_productCounts :
    ToVCVio.totalMass productCounts = 65536 := by
  rw [productCounts, ToVCVio.totalMass_productMeasure, totalMass_d1Counts]

private theorem productCounts_apply_sum (z : ℤ) :
    productCounts z =
      ∑ x ∈ Finset.Icc (-3 : ℤ) 3,
        ∑ y ∈ Finset.Icc (-3 : ℤ) 3,
          if x * y = z then d1Weight x * d1Weight y else 0 := by
  rw [productCounts, ToVCVio.productMeasure_apply]
  simp only [Finsupp.sum, support_d1Counts, d1Counts_apply]

private theorem productCounts_apply (z : ℤ) :
    productCounts z = productWeight z := by
  by_cases hz : z ∈ Set.Icc (-9 : ℤ) 9
  · rcases hz with ⟨hzlo, hzhi⟩
    interval_cases z <;>
      rw [productCounts_apply_sum, intIcc_neg3_3] <;>
      decide +kernel
  · have hcounts : productCounts z = 0 := by
      apply measureWindow_productCounts.apply_eq_zero
      simp only [Set.mem_Icc, not_and_or] at hz
      omega
    have hweight : productWeight z = 0 := by
      simp only [Set.mem_Icc] at hz
      obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
      all_goals
        simp only [productWeight, Int.natAbs_neg, Int.natAbs_natCast]
        split <;> simp_all
    rw [hcounts, hweight]

private theorem productCounts_neg (z : ℤ) :
    productCounts (-z) = productCounts z := by
  rw [productCounts_apply, productCounts_apply]
  simp only [productWeight, Int.natAbs_neg]

private def d1ProductExp : ProbComp ℤ := do
  let x ← d1IntSampler
  let y ← d1IntSampler
  return x * y

private theorem probOutput_d1ProductExp (z : ℤ) :
    Pr{let x ← d1ProductExp}[x = z] = (productCounts z : ℝ≥0∞) / 65536 := by
  rw [show d1ProductExp = (fun x y : ℤ => x * y) <$> d1IntSampler <*>
      d1IntSampler from rfl,
    probOutput_seq_map_eq_tsum_ite]
  rw [tsum_eq_sum (s := Finset.Icc (-3 : ℤ) 3)]
  · calc
      (∑ x ∈ Finset.Icc (-3 : ℤ) 3,
          ∑' y : ℤ,
            if z = x * y then
              Pr{let y ← d1IntSampler}[y = x] * Pr{let x ← d1IntSampler}[x = y]
            else 0) =
          ∑ x ∈ Finset.Icc (-3 : ℤ) 3,
            ∑ y ∈ Finset.Icc (-3 : ℤ) 3,
              if z = x * y then
                Pr{let y ← d1IntSampler}[y = x] * Pr{let x ← d1IntSampler}[x = y]
              else 0 := by
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [tsum_eq_sum (s := Finset.Icc (-3 : ℤ) 3)]
        intro y hy
        have hzero : d1Weight y = 0 := by
          by_contra hne
          exact hy ((d1Weight_ne_zero_iff y).mp hne)
        simp [probOutput_d1IntSampler, hzero]
      _ = (productCounts z : ℝ≥0∞) / 65536 := by
        simp_rw [probOutput_d1IntSampler]
        rw [productCounts_apply_sum]
        push_cast
        simp only [div_eq_mul_inv]
        have hinv : (65536 : ℝ≥0∞)⁻¹ =
            (256 : ℝ≥0∞)⁻¹ * (256 : ℝ≥0∞)⁻¹ := by
          rw [show (65536 : ℝ≥0∞) = 256 * 256 by norm_num,
            ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun y hy => ?_
        split_ifs with h₁ h₂ <;> simp_all
        ac_rfl
  · intro x hx
    have hzero : d1Weight x = 0 := by
      by_contra hne
      exact hx ((d1Weight_ne_zero_iff x).mp hne)
    simp [probOutput_d1IntSampler, hzero]

private def d1NegProductExp : ProbComp ℤ :=
  (-·) <$> d1ProductExp

private theorem probOutput_d1NegProductExp (z : ℤ) :
    Pr{let x ← d1NegProductExp}[x = z] = (productCounts z : ℝ≥0∞) / 65536 := by
  calc
    Pr{let x ← d1NegProductExp}[x = z] = Pr{let x ← d1ProductExp}[x = -z] := by
      unfold d1NegProductExp
      convert prEvent_map_injective d1ProductExp
        (fun _ _ h => neg_inj.mp h) (-z) using 1
      all_goals simp
    _ = (productCounts (-z) : ℝ≥0∞) / 65536 := probOutput_d1ProductExp (-z)
    _ = (productCounts z : ℝ≥0∞) / 65536 := by rw [productCounts_neg]

private theorem productWindow_eq_rangeImage :
    Finset.Icc (-9 : ℤ) 9 =
      (Finset.range 19).image (fun i : Nat => (-9 : ℤ) + i) := by
  ext z
  simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
  constructor
  · intro hz
    exact ⟨(z + 9).toNat, by omega, by omega⟩
  · rintro ⟨i, hi, rfl⟩
    omega

private theorem probOutput_add_productCounts
    (mx my : ProbComp ℤ)
    (hmx : ∀ z, Pr{let x ← mx}[x = z] = (productCounts z : ℝ≥0∞) / 65536)
    (hmy : ∀ z, Pr{let x ← my}[x = z] = (productCounts z : ℝ≥0∞) / 65536)
    (z : ℤ) :
    Pr{let w ← (fun x y : ℤ => x + y) <$> mx <*> my}[w = z] =
      ((productCounts * productCounts) z : ℝ≥0∞) / 65536 ^ 2 := by
  rw [probOutput_seq_map_eq_tsum_ite]
  have hinner (x : ℤ) :
      (∑' y : ℤ,
        if z = x + y then Pr{let y ← mx}[y = x] * Pr{let x ← my}[x = y] else 0) =
        Pr{let y ← mx}[y = x] * Pr{let y ← my}[y = z - x] := by
    refine (tsum_eq_single (z - x) (fun y hy => ?_)).trans ?_
    · rw [ite_eq_right]
      intro h
      apply hy
      omega
    · rw [ite_eq_left (by omega)]
  simp_rw [hinner]
  rw [tsum_eq_sum (s := Finset.Icc (-9 : ℤ) 9)]
  · simp_rw [hmx, hmy]
    rw [ToVCVio.mul_apply_window
      (show ToVCVio.MeasureWindow productCounts (-9) (-9 + (19 : ℤ) - 1) by
        norm_num
        exact measureWindow_productCounts) z]
    rw [productWindow_eq_rangeImage,
      Finset.sum_image (fun i _ j _ h => by omega)]
    push_cast
    simp only [div_eq_mul_inv, pow_two]
    have hinv : ((65536 : ℝ≥0∞) * 65536)⁻¹ =
        (65536 : ℝ≥0∞)⁻¹ * (65536 : ℝ≥0∞)⁻¹ := by
      exact ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))
    rw [hinv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    ac_rfl
  · intro x hx
    have hzero : productCounts x = 0 := by
      apply measureWindow_productCounts.apply_eq_zero
      simp only [Finset.mem_Icc] at hx
      omega
    simp [hmx, hzero]

/-- The four-product difference block used by the exact challenge entry-noise recurrence. -/
def ChallengeModelInternal.d1DifferenceBlock : ProbComp ℤ := do
  let s0 ← d1IntSampler
  let e0 ← d1IntSampler
  let s1 ← d1IntSampler
  let e1 ← d1IntSampler
  return s1 * e0 - e1 * s0

private theorem evalDist_d1DifferenceBlock_grouped :
    finiteLaw d1DifferenceBlock =
      finiteLaw ((fun x y : ℤ => x + y) <$> d1ProductExp <*> d1NegProductExp) := by
  simp only [d1DifferenceBlock, d1ProductExp, d1NegProductExp,
    map_eq_bind_pure_comp, seq_eq_bind_map, Function.comp_apply, bind_assoc, pure_bind]
  calc
    _ = finiteLaw (do
          let e0 ← d1IntSampler
          let s0 ← d1IntSampler
          let s1 ← d1IntSampler
          let e1 ← d1IntSampler
          return s1 * e0 - e1 * s0) := evalDist_bind_bind_swap _ _ _
    _ = finiteLaw (do
          let e0 ← d1IntSampler
          let s1 ← d1IntSampler
          let s0 ← d1IntSampler
          let e1 ← d1IntSampler
          return s1 * e0 - e1 * s0) := by
        refine evalDist_bind_congr' d1IntSampler fun e0 => ?_
        exact evalDist_bind_bind_swap _ _ _
    _ = finiteLaw (do
          let s1 ← d1IntSampler
          let e0 ← d1IntSampler
          let s0 ← d1IntSampler
          let e1 ← d1IntSampler
          return s1 * e0 - e1 * s0) := evalDist_bind_bind_swap _ _ _
    _ = finiteLaw (do
          let s1 ← d1IntSampler
          let e0 ← d1IntSampler
          let e1 ← d1IntSampler
          let s0 ← d1IntSampler
          return s1 * e0 - e1 * s0) := by
        refine evalDist_bind_congr' d1IntSampler fun s1 => ?_
        refine evalDist_bind_congr' d1IntSampler fun e0 => ?_
        exact evalDist_bind_bind_swap _ _ _
    _ = _ := by
      congr 1

theorem ChallengeModelInternal.probOutput_d1DifferenceBlock (z : ℤ) :
    Pr{let x ← d1DifferenceBlock}[x = z] =
      ((productCounts ^ 2) z : ℝ≥0∞) / 65536 ^ 2 := by
  rw [(evalDist_ext_iff.mp evalDist_d1DifferenceBlock_grouped) z]
  simpa only [pow_two] using
    probOutput_add_productCounts d1ProductExp d1NegProductExp
      probOutput_d1ProductExp probOutput_d1NegProductExp z

theorem ChallengeModelInternal.probOutput_add_counts
    (mx my : ProbComp ℤ) (F G : ToVCVio.IntMeasure) (D E : Nat)
    (hmx : ∀ z, Pr{let x ← mx}[x = z] = (F z : ℝ≥0∞) / D)
    (hmy : ∀ z, Pr{let x ← my}[x = z] = (G z : ℝ≥0∞) / E)
    (z : ℤ) :
    Pr{let w ← (fun x y : ℤ => x + y) <$> mx <*> my}[w = z] =
      ((F * G) z : ℝ≥0∞) / (D * E) := by
  rw [probOutput_seq_map_eq_tsum_ite]
  have hinner (x : ℤ) :
      (∑' y : ℤ,
        if z = x + y then Pr{let y ← mx}[y = x] * Pr{let x ← my}[x = y] else 0) =
        Pr{let y ← mx}[y = x] * Pr{let y ← my}[y = z - x] := by
    refine (tsum_eq_single (z - x) (fun y hy => ?_)).trans ?_
    · rw [ite_eq_right]
      intro h
      apply hy
      omega
    · rw [ite_eq_left (by omega)]
  simp_rw [hinner]
  rw [tsum_eq_sum (s := F.coeff.support)]
  · simp_rw [hmx, hmy]
    rw [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum]
    push_cast
    simp only [div_eq_mul_inv]
    have hinv : ((D : ℝ≥0∞) * E)⁻¹ =
        (D : ℝ≥0∞)⁻¹ * (E : ℝ≥0∞)⁻¹ := by
      exact ENNReal.mul_inv (Or.inr ENNReal.coe_ne_top) (Or.inl ENNReal.coe_ne_top)
    rw [hinv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [show -x + z = z - x by ring]
    ac_rfl
  · intro x hx
    have hzero : F x = 0 := Finsupp.notMem_support_iff.mp hx
    simp [hmx, hzero]

/-- The concrete product pack equals the generic measure pack of the product distribution. -/
theorem productPack_eq_measurePack :
    MLKEM.measurePack radix (-9) productCounts = productPack := by
  rw [MLKEM.measurePack_eq_range_sum
    (show ToVCVio.MeasureWindow productCounts (-9) (-9 + (19 : ℤ) - 1) by
      norm_num
      exact measureWindow_productCounts)]
  rw [productPack]
  generalize radix = R
  norm_num [productCounts_apply, productWeight, Finset.sum_range_succ]

end

end lweCKA.ChallengeCertificateModel
