/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.ChallengeExperimentLaw
import SecureMessaging.KEM.MLKEM.Correctness.FailureCertificate.Radix
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Counting-measure model for the Frodo Challenge certificate

This internal module proves the exact counting-measure model, its support and
mass bounds, and the semantic missing-mass enclosure used by the numerical
certificate.
-/

open OracleComp OracleComp.EvalDist
open scoped BigOperators ENNReal

namespace lweCKA.ChallengeCertificateModel

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

private def entryNoiseIntExpAux (n : Nat) : ProbComp ℤ := do
  let s0 ← ProbComp.sampleIID n d1IntSampler
  let e0 ← ProbComp.sampleIID n d1IntSampler
  let s1 ← ProbComp.sampleIID n d1IntSampler
  let e1 ← ProbComp.sampleIID n d1IntSampler
  let extra ← d1IntSampler
  return (∑ k : Fin n, s1 k * e0 k) -
    (∑ k : Fin n, e1 k * s0 k) + extra

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

private theorem d1Counts_apply (z : ℤ) :
    d1Counts z = d1Weight z := by
  classical
  rw [d1Counts, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  by_cases hz : z ∈ Finset.Icc (-3 : ℤ) 3
  · rw [Finset.sum_eq_single z]
    · simp
    · intro b hb hne
      simp [hne]
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
    simp [hne]

private theorem d1Weight_ne_zero_iff (z : ℤ) :
    d1Weight z ≠ 0 ↔ z ∈ Finset.Icc (-3 : ℤ) 3 := by
  constructor
  · intro hw
    have hp : Pr[= z | d1IntSampler] ≠ 0 := by
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

private theorem measureWindow_d1Counts :
    ToVCVio.MeasureWindow d1Counts (-3) 3 := by
  intro z hz
  rw [d1Counts_apply] at hz
  have hp : 0 < Pr[= z | d1IntSampler] := by
    rw [probOutput_d1IntSampler]
    exact ENNReal.div_pos (Nat.cast_ne_zero.mpr hz) (by norm_num)
  have hs : z ∈ support d1IntSampler :=
    (mem_support_iff d1IntSampler z).mpr (ne_of_gt hp)
  simpa only [support_d1IntSampler, Set.mem_Icc] using hs

private theorem extraPack_eq_measurePack :
    MLKEM.measurePack radix (-3) d1Counts = extraPack := by
  rw [MLKEM.measurePack_eq_range_sum
    (show ToVCVio.MeasureWindow d1Counts (-3) (-3 + (7 : ℤ) - 1) by
      norm_num
      exact measureWindow_d1Counts)]
  rw [extraPack]
  generalize radix = R
  norm_num [d1Counts_apply, d1Weight, Finset.sum_range_succ]

private theorem totalMass_d1Counts :
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

private theorem totalMass_productCounts :
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
    Pr[= z | d1ProductExp] = (productCounts z : ℝ≥0∞) / 65536 := by
  rw [show d1ProductExp = (fun x y : ℤ => x * y) <$> d1IntSampler <*>
      d1IntSampler from rfl,
    probOutput_seq_map_eq_tsum_ite]
  rw [tsum_eq_sum (s := Finset.Icc (-3 : ℤ) 3)]
  · calc
      (∑ x ∈ Finset.Icc (-3 : ℤ) 3,
          ∑' y : ℤ,
            if z = x * y then
              Pr[= x | d1IntSampler] * Pr[= y | d1IntSampler]
            else 0) =
          ∑ x ∈ Finset.Icc (-3 : ℤ) 3,
            ∑ y ∈ Finset.Icc (-3 : ℤ) 3,
              if z = x * y then
                Pr[= x | d1IntSampler] * Pr[= y | d1IntSampler]
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
    Pr[= z | d1NegProductExp] = (productCounts z : ℝ≥0∞) / 65536 := by
  calc
    Pr[= z | d1NegProductExp] = Pr[= -z | d1ProductExp] := by
      unfold d1NegProductExp
      convert probOutput_map_injective d1ProductExp
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
    (hmx : ∀ z, Pr[= z | mx] = (productCounts z : ℝ≥0∞) / 65536)
    (hmy : ∀ z, Pr[= z | my] = (productCounts z : ℝ≥0∞) / 65536)
    (z : ℤ) :
    Pr[= z | (fun x y : ℤ => x + y) <$> mx <*> my] =
      ((productCounts * productCounts) z : ℝ≥0∞) / 65536 ^ 2 := by
  rw [probOutput_seq_map_eq_tsum_ite]
  have hinner (x : ℤ) :
      (∑' y : ℤ,
        if z = x + y then Pr[= x | mx] * Pr[= y | my] else 0) =
        Pr[= x | mx] * Pr[= z - x | my] := by
    refine (tsum_eq_single (z - x) (fun y hy => ?_)).trans ?_
    · rw [if_neg]
      intro h
      apply hy
      omega
    · rw [if_pos (by omega)]
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

private def d1DifferenceBlock : ProbComp ℤ := do
  let s0 ← d1IntSampler
  let e0 ← d1IntSampler
  let s1 ← d1IntSampler
  let e1 ← d1IntSampler
  return s1 * e0 - e1 * s0

private theorem evalDist_d1DifferenceBlock_grouped :
    evalDist d1DifferenceBlock =
      evalDist ((fun x y : ℤ => x + y) <$> d1ProductExp <*> d1NegProductExp) := by
  simp only [d1DifferenceBlock, d1ProductExp, d1NegProductExp,
    map_eq_bind_pure_comp, seq_eq_bind_map, Function.comp_apply, bind_assoc, pure_bind]
  calc
    _ = evalDist (do
          let e0 ← d1IntSampler
          let s0 ← d1IntSampler
          let s1 ← d1IntSampler
          let e1 ← d1IntSampler
          return s1 * e0 - e1 * s0) := evalDist_bind_bind_swap _ _ _
    _ = evalDist (do
          let e0 ← d1IntSampler
          let s1 ← d1IntSampler
          let s0 ← d1IntSampler
          let e1 ← d1IntSampler
          return s1 * e0 - e1 * s0) := by
        refine evalDist_bind_congr' d1IntSampler fun e0 => ?_
        exact evalDist_bind_bind_swap _ _ _
    _ = evalDist (do
          let s1 ← d1IntSampler
          let e0 ← d1IntSampler
          let s0 ← d1IntSampler
          let e1 ← d1IntSampler
          return s1 * e0 - e1 * s0) := evalDist_bind_bind_swap _ _ _
    _ = evalDist (do
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

private theorem probOutput_d1DifferenceBlock (z : ℤ) :
    Pr[= z | d1DifferenceBlock] =
      ((productCounts ^ 2) z : ℝ≥0∞) / 65536 ^ 2 := by
  rw [(evalDist_ext_iff.mp evalDist_d1DifferenceBlock_grouped) z]
  simpa only [pow_two] using
    probOutput_add_productCounts d1ProductExp d1NegProductExp
      probOutput_d1ProductExp probOutput_d1NegProductExp z

private theorem probOutput_add_counts
    (mx my : ProbComp ℤ) (F G : ToVCVio.IntMeasure) (D E : Nat)
    (hmx : ∀ z, Pr[= z | mx] = (F z : ℝ≥0∞) / D)
    (hmy : ∀ z, Pr[= z | my] = (G z : ℝ≥0∞) / E)
    (z : ℤ) :
    Pr[= z | (fun x y : ℤ => x + y) <$> mx <*> my] =
      ((F * G) z : ℝ≥0∞) / (D * E) := by
  rw [probOutput_seq_map_eq_tsum_ite]
  have hinner (x : ℤ) :
      (∑' y : ℤ,
        if z = x + y then Pr[= x | mx] * Pr[= y | my] else 0) =
        Pr[= x | mx] * Pr[= z - x | my] := by
    refine (tsum_eq_single (z - x) (fun y hy => ?_)).trans ?_
    · rw [if_neg]
      intro h
      apply hy
      omega
    · rw [if_pos (by omega)]
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

private theorem evalDist_bind_move_after_two
    {A B C D : Type} (ma : ProbComp A) (mb : ProbComp B) (mc : ProbComp C)
    (f : A → B → C → ProbComp D) :
    evalDist (do
      let a ← ma
      let b ← mb
      let c ← mc
      f a b c) =
    evalDist (do
      let b ← mb
      let c ← mc
      let a ← ma
      f a b c) := by
  calc
    _ = evalDist (do
          let b ← mb
          let a ← ma
          let c ← mc
          f a b c) := evalDist_bind_bind_swap ma mb _
    _ = _ := evalDist_bind_congr' mb fun b =>
      evalDist_bind_bind_swap ma mc (fun a c => f a b c)

private theorem evalDist_bind_move_after_three
    {A B C D E : Type} (ma : ProbComp A) (mb : ProbComp B) (mc : ProbComp C)
    (md : ProbComp D) (f : A → B → C → D → ProbComp E) :
    evalDist (do
      let a ← ma
      let b ← mb
      let c ← mc
      let d ← md
      f a b c d) =
    evalDist (do
      let b ← mb
      let c ← mc
      let d ← md
      let a ← ma
      f a b c d) := by
  calc
    _ = evalDist (do
          let b ← mb
          let a ← ma
          let c ← mc
          let d ← md
          f a b c d) := evalDist_bind_bind_swap ma mb _
    _ = _ := evalDist_bind_congr' mb fun b =>
      evalDist_bind_move_after_two ma mc md (fun a c d => f a b c d)

private theorem evalDist_bind_move_after_four
    {A B C D E F : Type} (ma : ProbComp A) (mb : ProbComp B) (mc : ProbComp C)
    (md : ProbComp D) (me : ProbComp E)
    (f : A → B → C → D → E → ProbComp F) :
    evalDist (do
      let a ← ma
      let b ← mb
      let c ← mc
      let d ← md
      let e ← me
      f a b c d e) =
    evalDist (do
      let b ← mb
      let c ← mc
      let d ← md
      let e ← me
      let a ← ma
      f a b c d e) := by
  calc
    _ = evalDist (do
          let b ← mb
          let a ← ma
          let c ← mc
          let d ← md
          let e ← me
          f a b c d e) := evalDist_bind_bind_swap ma mb _
    _ = _ := evalDist_bind_congr' mb fun b =>
      evalDist_bind_move_after_three ma mc md me (fun a c d e => f a b c d e)

private theorem evalDist_bind_rotate_four_heads
    {H0 T0 H1 T1 H2 T2 H3 T3 X R : Type}
    (h0 : ProbComp H0) (t0 : ProbComp T0) (h1 : ProbComp H1) (t1 : ProbComp T1)
    (h2 : ProbComp H2) (t2 : ProbComp T2) (h3 : ProbComp H3) (t3 : ProbComp T3)
    (mx : ProbComp X)
    (f : H0 → T0 → H1 → T1 → H2 → T2 → H3 → T3 → X → ProbComp R) :
    evalDist (do
      let a0 ← h0
      let b0 ← t0
      let a1 ← h1
      let b1 ← t1
      let a2 ← h2
      let b2 ← t2
      let a3 ← h3
      let b3 ← t3
      let x ← mx
      f a0 b0 a1 b1 a2 b2 a3 b3 x) =
    evalDist (do
      let b0 ← t0
      let b1 ← t1
      let b2 ← t2
      let b3 ← t3
      let x ← mx
      let a0 ← h0
      let a1 ← h1
      let a2 ← h2
      let a3 ← h3
      f a0 b0 a1 b1 a2 b2 a3 b3 x) := by
  calc
    _ = evalDist (do
          let b0 ← t0
          let a0 ← h0
          let a1 ← h1
          let b1 ← t1
          let a2 ← h2
          let b2 ← t2
          let a3 ← h3
          let b3 ← t3
          let x ← mx
          f a0 b0 a1 b1 a2 b2 a3 b3 x) := evalDist_bind_bind_swap h0 t0 _
    _ = evalDist (do
          let b0 ← t0
          let b1 ← t1
          let a0 ← h0
          let a1 ← h1
          let a2 ← h2
          let b2 ← t2
          let a3 ← h3
          let b3 ← t3
          let x ← mx
          f a0 b0 a1 b1 a2 b2 a3 b3 x) := by
        refine evalDist_bind_congr' t0 fun b0 => ?_
        exact (evalDist_bind_move_after_two t1 h0 h1
          (fun b1 a0 a1 => do
            let a2 ← h2
            let b2 ← t2
            let a3 ← h3
            let b3 ← t3
            let x ← mx
            f a0 b0 a1 b1 a2 b2 a3 b3 x)).symm
    _ = evalDist (do
          let b0 ← t0
          let b1 ← t1
          let b2 ← t2
          let a0 ← h0
          let a1 ← h1
          let a2 ← h2
          let a3 ← h3
          let b3 ← t3
          let x ← mx
          f a0 b0 a1 b1 a2 b2 a3 b3 x) := by
        refine evalDist_bind_congr' t0 fun b0 => ?_
        refine evalDist_bind_congr' t1 fun b1 => ?_
        exact (evalDist_bind_move_after_three t2 h0 h1 h2
          (fun b2 a0 a1 a2 => do
            let a3 ← h3
            let b3 ← t3
            let x ← mx
            f a0 b0 a1 b1 a2 b2 a3 b3 x)).symm
    _ = evalDist (do
          let b0 ← t0
          let b1 ← t1
          let b2 ← t2
          let b3 ← t3
          let a0 ← h0
          let a1 ← h1
          let a2 ← h2
          let a3 ← h3
          let x ← mx
          f a0 b0 a1 b1 a2 b2 a3 b3 x) := by
        refine evalDist_bind_congr' t0 fun b0 => ?_
        refine evalDist_bind_congr' t1 fun b1 => ?_
        refine evalDist_bind_congr' t2 fun b2 => ?_
        exact (evalDist_bind_move_after_four t3 h0 h1 h2 h3
          (fun b3 a0 a1 a2 a3 => do
            let x ← mx
            f a0 b0 a1 b1 a2 b2 a3 b3 x)).symm
    _ = _ := by
        refine evalDist_bind_congr' t0 fun b0 => ?_
        refine evalDist_bind_congr' t1 fun b1 => ?_
        refine evalDist_bind_congr' t2 fun b2 => ?_
        refine evalDist_bind_congr' t3 fun b3 => ?_
        exact (evalDist_bind_move_after_four mx h0 h1 h2 h3
          (fun x a0 a1 a2 a3 => f a0 b0 a1 b1 a2 b2 a3 b3 x)).symm

private theorem evalDist_entryNoiseIntExpAux_succ (n : Nat) :
    evalDist (entryNoiseIntExpAux (n + 1)) =
      evalDist (do
        let rest ← entryNoiseIntExpAux n
        let step ← d1DifferenceBlock
        return rest + step) := by
  let tail : ProbComp (Fin n → ℤ) := Fin.mOfFn n fun _ => d1IntSampler
  let finish (s0 : ℤ) (s0s : Fin n → ℤ) (e0 : ℤ) (e0s : Fin n → ℤ)
      (s1 : ℤ) (s1s : Fin n → ℤ) (e1 : ℤ) (e1s : Fin n → ℤ)
      (extra : ℤ) : ProbComp ℤ :=
    pure ((∑ k, Fin.cons s1 s1s k * Fin.cons e0 e0s k) -
      (∑ k, Fin.cons e1 e1s k * Fin.cons s0 s0s k) + extra)
  simp only [entryNoiseIntExpAux, d1DifferenceBlock, ProbComp.sampleIID,
    Fin.mOfFn, bind_assoc, pure_bind]
  change evalDist (do
      let s0 ← d1IntSampler
      let s0s ← tail
      let e0 ← d1IntSampler
      let e0s ← tail
      let s1 ← d1IntSampler
      let s1s ← tail
      let e1 ← d1IntSampler
      let e1s ← tail
      let extra ← d1IntSampler
      finish s0 s0s e0 e0s s1 s1s e1 e1s extra) = _
  calc
    _ = evalDist (do
          let s0s ← tail
          let e0s ← tail
          let s1s ← tail
          let e1s ← tail
          let extra ← d1IntSampler
          let s0 ← d1IntSampler
          let e0 ← d1IntSampler
          let s1 ← d1IntSampler
          let e1 ← d1IntSampler
          finish s0 s0s e0 e0s s1 s1s e1 e1s extra) :=
        evalDist_bind_rotate_four_heads
          d1IntSampler tail d1IntSampler tail d1IntSampler tail
          d1IntSampler tail d1IntSampler finish
    _ = _ := by
        refine evalDist_bind_congr' tail fun s0s => ?_
        refine evalDist_bind_congr' tail fun e0s => ?_
        refine evalDist_bind_congr' tail fun s1s => ?_
        refine evalDist_bind_congr' tail fun e1s => ?_
        refine evalDist_bind_congr' d1IntSampler fun extra => ?_
        refine evalDist_bind_congr' d1IntSampler fun s0 => ?_
        refine evalDist_bind_congr' d1IntSampler fun e0 => ?_
        refine evalDist_bind_congr' d1IntSampler fun s1 => ?_
        refine evalDist_bind_congr' d1IntSampler fun e1 => ?_
        simp only [finish, evalDist_pure]
        congr 1
        simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
        ring

private theorem probOutput_entryNoiseIntExpAux (n : Nat) (z : ℤ) :
    Pr[= z | entryNoiseIntExpAux n] =
      (((productCounts ^ (2 * n)) * d1Counts) z : ℝ≥0∞) /
        256 ^ (4 * n + 1) := by
  induction n generalizing z with
  | zero =>
      simp [entryNoiseIntExpAux, ProbComp.sampleIID, Fin.mOfFn,
        probOutput_d1IntSampler, d1Counts_apply]
  | succ n ih =>
      rw [(evalDist_ext_iff.mp (evalDist_entryNoiseIntExpAux_succ n)) z]
      rw [show (do
          let rest ← entryNoiseIntExpAux n
          let step ← d1DifferenceBlock
          return rest + step) =
          (fun x y : ℤ => x + y) <$> entryNoiseIntExpAux n <*>
            d1DifferenceBlock by
        simp only [map_eq_bind_pure_comp, seq_eq_bind_map,
          Function.comp_def, bind_assoc, pure_bind]]
      have ihNat (u : ℤ) :
          Pr[= u | entryNoiseIntExpAux n] =
            (((productCounts ^ (2 * n)) * d1Counts) u : ℝ≥0∞) /
              ((256 ^ (4 * n + 1) : Nat) : ℝ≥0∞) := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using ih u
      have hstepNat (u : ℤ) :
          Pr[= u | d1DifferenceBlock] =
            ((productCounts ^ 2) u : ℝ≥0∞) /
              ((65536 ^ 2 : Nat) : ℝ≥0∞) := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using
          probOutput_d1DifferenceBlock u
      calc
        _ = (((productCounts ^ (2 * n) * d1Counts) * productCounts ^ 2) z :
              ℝ≥0∞) /
            (((256 ^ (4 * n + 1)) * 65536 ^ 2 : Nat) : ℝ≥0∞) := by
          simpa only [Nat.cast_mul] using probOutput_add_counts
            (entryNoiseIntExpAux n) d1DifferenceBlock
            (productCounts ^ (2 * n) * d1Counts) (productCounts ^ 2)
            (256 ^ (4 * n + 1)) (65536 ^ 2) ihNat hstepNat z
        _ = (((productCounts ^ (2 * (n + 1))) * d1Counts) z : ℝ≥0∞) /
            256 ^ (4 * (n + 1) + 1) := by
          have hmeasure :
              (productCounts ^ (2 * n) * d1Counts) * productCounts ^ 2 =
                productCounts ^ (2 * (n + 1)) * d1Counts := by
            rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
            ring
          rw [hmeasure]
          simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
          have hden :
              (256 : ℝ≥0∞) ^ (4 * n + 1) * 65536 ^ 2 =
                256 ^ (4 * (n + 1) + 1) := by
            rw [show (65536 : ℝ≥0∞) = 256 ^ 2 by norm_num,
              ← pow_mul, ← pow_add]
            congr 1
          rw [hden]

private theorem challengeEntryNoiseIntExp_eq_aux :
    challengeEntryNoiseIntExp = entryNoiseIntExpAux 352 := by
  rfl

private theorem probOutput_challengeEntryNoiseIntExp_counts (z : ℤ) :
    Pr[= z | challengeEntryNoiseIntExp] =
      (((productCounts ^ 704) * d1Counts) z : ℝ≥0∞) / 256 ^ 1409 := by
  rw [challengeEntryNoiseIntExp_eq_aux, probOutput_entryNoiseIntExpAux]

/-- One coefficient of the successor lower measure equals the rounded convolution coefficient. -/
theorem lowerCounts_succ_apply (n : Nat) (z : ℤ) :
    lowerCounts (n + 1) z =
      if z ∈ Finset.Icc (-384 : ℤ) 384 then
        ((lowerCounts n * productCounts) z) / 65536
      else 0 := by
  classical
  rw [lowerCounts, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  by_cases hz : z ∈ Finset.Icc (-384 : ℤ) 384
  · rw [if_pos hz, Finset.sum_eq_single z]
    · simp
    · intro y hy hne
      simp [hne]
    · exact fun h => (h hz).elim
  · rw [if_neg hz]
    apply Finset.sum_eq_zero
    intro y hy
    have hne : y ≠ z := fun h => hz (h ▸ hy)
    simp [hne]

/-- Every lower counting measure is supported on the prescribed 769-point window. -/
theorem measureWindow_lowerCounts (n : Nat) :
    ToVCVio.MeasureWindow (lowerCounts n) (-384) 384 := by
  cases n with
  | zero =>
      intro z hz
      simp only [lowerCounts, AddMonoidAlgebra.coeff_single,
        Finsupp.single_apply] at hz
      split at hz
      · omega
      · simp at hz
  | succ n =>
      intro z hz
      rw [lowerCounts_succ_apply n z] at hz
      split at hz
      · simpa only [Finset.mem_Icc] using ‹z ∈ Finset.Icc (-384 : ℤ) 384›
      · simp at hz

private theorem finsetSum_apply_le_totalMass
    (F : ToVCVio.IntMeasure) (s : Finset ℤ) :
    ∑ z ∈ s, F z ≤ ToVCVio.totalMass F := by
  classical
  calc
    ∑ z ∈ s, F z = ∑ z ∈ s ∩ F.coeff.support, F z := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro z hzs hz
      have hnot : z ∉ F.coeff.support := by
        intro hsupport
        exact hz (Finset.mem_inter.mpr ⟨hzs, hsupport⟩)
      exact Finsupp.notMem_support_iff.mp hnot
    _ ≤ ∑ z ∈ F.coeff.support, F z :=
      Finset.sum_le_sum_of_subset Finset.inter_subset_right
    _ = ToVCVio.totalMass F := by rfl

/-- The total mass of every lower counting measure is at most the exact scale. -/
theorem totalMass_lowerCounts_le (n : Nat) :
    ToVCVio.totalMass (lowerCounts n) ≤ scale := by
  induction n with
  | zero =>
      rw [lowerCounts, ToVCVio.totalMass_single]
  | succ n ih =>
      have hwindow :
          ToVCVio.MeasureWindow (lowerCounts (n + 1))
            (-384) (-384 + (769 : ℤ) - 1) := by
        norm_num
        exact measureWindow_lowerCounts (n + 1)
      have hscaled :
          65536 * ToVCVio.totalMass (lowerCounts (n + 1)) ≤
            65536 * scale := by
        calc
          65536 * ToVCVio.totalMass (lowerCounts (n + 1)) =
              ∑ i ∈ Finset.range 769,
                65536 * ((lowerCounts n * productCounts) ((-384 : ℤ) + i) / 65536) := by
            rw [MLKEM.totalMass_eq_range_sum hwindow, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [lowerCounts_succ_apply]
            simp only [Finset.mem_Icc]
            rw [if_pos (by have hi := Finset.mem_range.mp hi; omega)]
          _ ≤ ∑ i ∈ Finset.range 769,
                (lowerCounts n * productCounts) ((-384 : ℤ) + i) := by
            exact Finset.sum_le_sum fun i hi => by
              simpa [Nat.mul_comm] using
                Nat.div_mul_le_self
                  ((lowerCounts n * productCounts) ((-384 : ℤ) + i)) 65536
          _ ≤ ToVCVio.totalMass (lowerCounts n * productCounts) := by
            let s : Finset ℤ :=
              (Finset.range 769).image (fun i : Nat => (-384 : ℤ) + i)
            have hinj : Function.Injective (fun i : Nat => (-384 : ℤ) + i) := by
              intro i j h
              exact_mod_cast (Int.add_left_cancel h)
            rw [show (∑ i ∈ Finset.range 769,
                (lowerCounts n * productCounts) ((-384 : ℤ) + i)) =
                ∑ z ∈ s, (lowerCounts n * productCounts) z by
                  unfold s
                  rw [Finset.sum_image hinj.injOn]]
            exact finsetSum_apply_le_totalMass _ _
          _ = ToVCVio.totalMass (lowerCounts n) * 65536 := by
            rw [ToVCVio.totalMass_mul, totalMass_productCounts]
          _ ≤ 65536 * scale := by
            simpa [Nat.mul_comm] using Nat.mul_le_mul_right 65536 ih
      omega

private theorem finsetSum_mul_apply_le
    (F G : ToVCVio.IntMeasure) (s : Finset ℤ) (z : ℤ) :
    ∑ x ∈ s, F x * G (z - x) ≤ (F * G) z := by
  classical
  calc
    ∑ x ∈ s, F x * G (z - x) =
        ∑ x ∈ s ∩ F.coeff.support, F x * G (z - x) := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro x hxs hx
      have hnot : x ∉ F.coeff.support := by
        intro hsupport
        exact hx (Finset.mem_inter.mpr ⟨hxs, hsupport⟩)
      rw [Finsupp.notMem_support_iff.mp hnot, zero_mul]
    _ ≤ ∑ x ∈ F.coeff.support, F x * G (z - x) :=
      Finset.sum_le_sum_of_subset Finset.inter_subset_right
    _ = (F * G) z := by
      rw [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum]
      congr 1
      funext x
      rw [show -x + z = z - x by ring]

private theorem lowerCounts_domination (n : Nat) (z : ℤ) :
    65536 ^ n * lowerCounts n z ≤
      scale * (productCounts ^ n) z := by
  induction n generalizing z with
  | zero =>
      by_cases hz : z = 0 <;> simp [lowerCounts, AddMonoidAlgebra.one_def, hz]
  | succ n ih =>
      by_cases hz : z ∈ Finset.Icc (-384 : ℤ) 384
      · rw [lowerCounts_succ_apply, if_pos hz]
        have hdiv :
            65536 * ((lowerCounts n * productCounts) z / 65536) ≤
              (lowerCounts n * productCounts) z := by
          simpa [Nat.mul_comm] using
            Nat.div_mul_le_self ((lowerCounts n * productCounts) z) 65536
        calc
          65536 ^ (n + 1) * ((lowerCounts n * productCounts) z / 65536) =
              65536 ^ n *
                (65536 * ((lowerCounts n * productCounts) z / 65536)) := by
            rw [pow_succ]
            ring
          _ ≤ 65536 ^ n * (lowerCounts n * productCounts) z :=
            Nat.mul_le_mul_left _ hdiv
          _ = ∑ i ∈ Finset.range 769,
                (65536 ^ n * lowerCounts n ((-384 : ℤ) + i)) *
                  productCounts (z - ((-384 : ℤ) + i)) := by
            rw [ToVCVio.mul_apply_window
              (show ToVCVio.MeasureWindow (lowerCounts n)
                  (-384) (-384 + (769 : ℤ) - 1) by
                norm_num
                exact measureWindow_lowerCounts n) z,
              Finset.mul_sum]
            refine Finset.sum_congr rfl fun i hi => ?_
            ring
          _ ≤ ∑ i ∈ Finset.range 769,
                (scale * (productCounts ^ n) ((-384 : ℤ) + i)) *
                  productCounts (z - ((-384 : ℤ) + i)) := by
            exact Finset.sum_le_sum fun i hi =>
              Nat.mul_le_mul_right _ (ih ((-384 : ℤ) + i))
          _ = scale * ∑ i ∈ Finset.range 769,
                (productCounts ^ n) ((-384 : ℤ) + i) *
                  productCounts (z - ((-384 : ℤ) + i)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i hi => ?_
            ring
          _ ≤ scale * ((productCounts ^ n) * productCounts) z := by
            apply Nat.mul_le_mul_left
            let s : Finset ℤ :=
              (Finset.range 769).image (fun i : Nat => (-384 : ℤ) + i)
            have hinj : Function.Injective (fun i : Nat => (-384 : ℤ) + i) := by
              intro i j h
              exact_mod_cast (Int.add_left_cancel h)
            rw [show (∑ i ∈ Finset.range 769,
                (productCounts ^ n) ((-384 : ℤ) + i) *
                  productCounts (z - ((-384 : ℤ) + i))) =
                ∑ x ∈ s, (productCounts ^ n) x * productCounts (z - x) by
                  unfold s
                  rw [Finset.sum_image hinj.injOn]]
            exact finsetSum_mul_apply_le _ _ _ _
          _ = scale * (productCounts ^ (n + 1)) z := by rw [pow_succ]
      · rw [lowerCounts_succ_apply, if_neg hz]
        simp

private theorem lowerCounts_mul_d1_domination (n : Nat) (z : ℤ) :
    65536 ^ n * (lowerCounts n * d1Counts) z ≤
      scale * ((productCounts ^ n) * d1Counts) z := by
  calc
    65536 ^ n * (lowerCounts n * d1Counts) z =
        ∑ i ∈ Finset.range 769,
          (65536 ^ n * lowerCounts n ((-384 : ℤ) + i)) *
            d1Counts (z - ((-384 : ℤ) + i)) := by
      rw [ToVCVio.mul_apply_window
        (show ToVCVio.MeasureWindow (lowerCounts n)
            (-384) (-384 + (769 : ℤ) - 1) by
          norm_num
          exact measureWindow_lowerCounts n) z,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      ring
    _ ≤ ∑ i ∈ Finset.range 769,
          (scale * (productCounts ^ n) ((-384 : ℤ) + i)) *
            d1Counts (z - ((-384 : ℤ) + i)) := by
      exact Finset.sum_le_sum fun i hi =>
        Nat.mul_le_mul_right _ (lowerCounts_domination n ((-384 : ℤ) + i))
    _ = scale * ∑ i ∈ Finset.range 769,
          (productCounts ^ n) ((-384 : ℤ) + i) *
            d1Counts (z - ((-384 : ℤ) + i)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      ring
    _ ≤ scale * ((productCounts ^ n) * d1Counts) z := by
      apply Nat.mul_le_mul_left
      let s : Finset ℤ :=
        (Finset.range 769).image (fun i : Nat => (-384 : ℤ) + i)
      have hinj : Function.Injective (fun i : Nat => (-384 : ℤ) + i) := by
        intro i j h
        exact_mod_cast (Int.add_left_cancel h)
      rw [show (∑ i ∈ Finset.range 769,
          (productCounts ^ n) ((-384 : ℤ) + i) *
            d1Counts (z - ((-384 : ℤ) + i))) =
          ∑ x ∈ s, (productCounts ^ n) x * d1Counts (z - x) by
            unfold s
            rw [Finset.sum_image hinj.injOn]]
      exact finsetSum_mul_apply_le _ _ _ _

private theorem totalMass_fullCounts :
    ToVCVio.totalMass ((productCounts ^ 704) * d1Counts) = 256 ^ 1409 := by
  rw [ToVCVio.totalMass_mul, ToVCVio.totalMass_pow,
    totalMass_productCounts, totalMass_d1Counts,
    show (65536 : Nat) = 256 ^ 2 by norm_num, ← pow_mul, ← pow_succ]

/-- The approximate final measure has total mass 256 times the lower measure mass. -/
theorem totalMass_approxCounts :
    ToVCVio.totalMass (lowerCounts 704 * d1Counts) =
      256 * ToVCVio.totalMass (lowerCounts 704) := by
  rw [ToVCVio.totalMass_mul, totalMass_d1Counts, Nat.mul_comm]

private theorem approxCounts_domination (z : ℤ) :
    256 ^ 1409 * (lowerCounts 704 * d1Counts) z ≤
      (256 * scale) * ((productCounts ^ 704) * d1Counts) z := by
  have h := lowerCounts_mul_d1_domination 704 z
  rw [show (65536 : Nat) = 256 ^ 2 by norm_num, ← pow_mul] at h
  have hmul := Nat.mul_le_mul_left 256 h
  calc
    256 ^ 1409 * (lowerCounts 704 * d1Counts) z =
        256 * (256 ^ (2 * 704) * (lowerCounts 704 * d1Counts) z) := by
      rw [show 1409 = 2 * 704 + 1 by norm_num, pow_succ]
      rw [Nat.mul_comm (256 ^ (2 * 704)) 256, Nat.mul_assoc]
    _ ≤ 256 * (scale * ((productCounts ^ 704) * d1Counts) z) := hmul
    _ = (256 * scale) * ((productCounts ^ 704) * d1Counts) z :=
      (Nat.mul_assoc 256 scale (((productCounts ^ 704) * d1Counts) z)).symm

/-- Packing the approximate final measure factors through the final lower-measure pack. -/
theorem measurePack_approxCounts :
    MLKEM.measurePack radix (-387) (lowerCounts 704 * d1Counts) =
      MLKEM.measurePack radix (-384) (lowerCounts 704) * extraPack := by
  calc
    MLKEM.measurePack radix (-387) (lowerCounts 704 * d1Counts) =
        MLKEM.measurePack radix (-384) (lowerCounts 704) *
          MLKEM.measurePack radix (-3) d1Counts := by
      have hmul := MLKEM.measurePack_mul (R := radix)
        (measureWindow_lowerCounts 704) measureWindow_d1Counts
      norm_num only at hmul
      exact hmul
    _ = MLKEM.measurePack radix (-384) (lowerCounts 704) * extraPack := by
      rw [extraPack_eq_measurePack]

/-- The approximate final measure is supported on the interval from minus 387 to 387. -/
theorem measureWindow_approxCounts :
    ToVCVio.MeasureWindow (lowerCounts 704 * d1Counts) (-387) 387 := by
  simpa using
    ToVCVio.measureWindow_mul (measureWindow_lowerCounts 704) measureWindow_d1Counts

private theorem challengeFailureRamp_le_one_local (z : ℤ) :
    challengeFailureRamp z ≤ 1 := by
  unfold challengeFailureRamp
  apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
  simpa only [one_mul] using
    (min_le_left (512 : ℝ≥0∞)
      ((modularDistance challengeParams (z : Scalar challengeParams) 0 : ℝ≥0∞) - 256))

private theorem modularDistance_eq_natAbs_valMinAbs_local
    (p : Params) (u v : Scalar p) :
    modularDistance p u v = (u - v).valMinAbs.natAbs := by
  by_cases h : u = v
  · subst v
    simp [modularDistance]
  · have hsub : u - v ≠ 0 := sub_ne_zero.mpr h
    have hneg : v - u = -(u - v) := by simp
    have hnegval : (v - u).val = p.q - (u - v).val := by
      rw [hneg, ZMod.neg_val, if_neg hsub]
    rw [modularDistance, hnegval, ZMod.valMinAbs_natAbs_eq_min]

private theorem valMinAbs_intCast_eq_of_natAbs_le_387
    (z : ℤ) (hz : z.natAbs ≤ 387) :
    ((z : Scalar challengeParams).valMinAbs) = z := by
  have hzrange : (-387 : ℤ) ≤ z ∧ z ≤ 387 := by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z <;>
      simp_all
  apply (ZMod.valMinAbs_spec (z : Scalar challengeParams) z).2
  constructor
  · rfl
  · change z * 2 ∈ Set.Ioc (-(challengeParams.q : ℤ)) challengeParams.q
    simp only [Set.mem_Ioc, challengeParams, Params.q]
    omega

private theorem modularDistance_intCast_zero_eq_natAbs_of_le_387
    (z : ℤ) (hz : z.natAbs ≤ 387) :
    modularDistance challengeParams (z : Scalar challengeParams) 0 = z.natAbs := by
  rw [modularDistance_eq_natAbs_valMinAbs_local, sub_zero,
    valMinAbs_intCast_eq_of_natAbs_le_387 z hz]

private theorem challengeFailureRamp_eq_weight_of_natAbs_le_387
    (z : ℤ) (hz : z.natAbs ≤ 387) :
    challengeFailureRamp z = ((z.natAbs - 256 : Nat) : ℝ≥0∞) / 512 := by
  unfold challengeFailureRamp
  rw [modularDistance_intCast_zero_eq_natAbs_of_le_387 z hz]
  have hsub : (z.natAbs : ℝ≥0∞) - 256 =
      ((z.natAbs - 256 : Nat) : ℝ≥0∞) := by
    simpa only [Nat.cast_ofNat] using (ENNReal.natCast_sub z.natAbs 256).symm
  rw [hsub, min_eq_right]
  exact_mod_cast (show z.natAbs - 256 ≤ 512 by omega)

private theorem challengeFailureRamp_eq_weight_on_approxCounts
    (z : ℤ) (hz : (lowerCounts 704 * d1Counts) z ≠ 0) :
    challengeFailureRamp z = ((z.natAbs - 256 : Nat) : ℝ≥0∞) / 512 := by
  apply challengeFailureRamp_eq_weight_of_natAbs_le_387
  have hwindow := measureWindow_approxCounts z hz
  clear hz
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · simp only [Int.natAbs_natCast]
    omega
  · simp only [Int.natAbs_neg, Int.natAbs_natCast]
    omega

private theorem ennreal_nat_ratio_le_ratio
    {a b c d : Nat} (hc : 0 < c) (hd : 0 < d)
    (h : d * a ≤ c * b) :
    (a : ℝ≥0∞) / c ≤ (b : ℝ≥0∞) / d := by
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (by exact_mod_cast hd.ne')) (Or.inl ENNReal.coe_ne_top)).2
  calc
    (a : ℝ≥0∞) / c * d = ((a * d : Nat) : ℝ≥0∞) / c := by
      push_cast
      simp only [div_eq_mul_inv]
      ac_rfl
    _ ≤ (b : ℝ≥0∞) := by
      apply (ENNReal.div_le_iff
        (by exact_mod_cast hc.ne') ENNReal.coe_ne_top).2
      exact_mod_cast (by simpa [Nat.mul_comm] using h)

private theorem finite_missingMass_enclosure
    (s : Finset ℤ) (F A : ToVCVio.IntMeasure)
    (D S H : Nat) (rho : ℤ → ℝ≥0∞) (w : ℤ → Nat)
    (hD : 0 < D) (hS : 0 < S)
    (hmassF : ∑ z ∈ s, F z = D)
    (hdom : ∀ z, D * A z ≤ S * F z)
    (hrho : ∀ z, A z ≠ 0 → rho z = (w z : ℝ≥0∞) / H)
    (hrho_le : ∀ z, rho z ≤ 1) :
    (∑ z ∈ s, ((A z * w z : Nat) : ℝ≥0∞) / (S * H)) ≤
        ∑ z ∈ s, (F z : ℝ≥0∞) / D * rho z ∧
      (∑ z ∈ s, (F z : ℝ≥0∞) / D * rho z) ≤
        (∑ z ∈ s, ((A z * w z : Nat) : ℝ≥0∞) / (S * H)) +
          ((S - ∑ z ∈ s, A z : Nat) : ℝ≥0∞) / S := by
  have hscaled : D * ∑ z ∈ s, A z ≤ S * D := by
    calc
      D * ∑ z ∈ s, A z = ∑ z ∈ s, D * A z := by
        rw [Finset.mul_sum]
      _ ≤ ∑ z ∈ s, S * F z :=
        Finset.sum_le_sum fun z _ => hdom z
      _ = S * ∑ z ∈ s, F z := by
        rw [Finset.mul_sum]
      _ = S * D := by rw [hmassF]
  have hmassA : ∑ z ∈ s, A z ≤ S := by
    exact le_of_mul_le_mul_left (by simpa [Nat.mul_comm] using hscaled) hD
  have hratio (z : ℤ) :
      (A z : ℝ≥0∞) / S ≤ (F z : ℝ≥0∞) / D :=
    ennreal_nat_ratio_le_ratio hS hD (hdom z)
  have hweight (z : ℤ) :
      ((A z * w z : Nat) : ℝ≥0∞) / (S * H) =
        (A z : ℝ≥0∞) / S * ((w z : ℝ≥0∞) / H) := by
    push_cast
    exact ENNReal.mul_div_mul_comm
      (Or.inl (by exact_mod_cast hS.ne')) (Or.inl ENNReal.coe_ne_top)
  have hlower (z : ℤ) :
      ((A z * w z : Nat) : ℝ≥0∞) / (S * H) ≤
        (F z : ℝ≥0∞) / D * rho z := by
    by_cases hz : A z = 0
    · simp [hz]
    · rw [hweight, ← hrho z hz]
      exact mul_le_mul' (hratio z) le_rfl
  have hupper (z : ℤ) :
      (F z : ℝ≥0∞) / D * rho z ≤
        ((A z * w z : Nat) : ℝ≥0∞) / (S * H) +
          ((F z : ℝ≥0∞) / D - (A z : ℝ≥0∞) / S) := by
    by_cases hz : A z = 0
    · simp only [hz, Nat.cast_zero, zero_mul]
      simpa using mul_le_of_le_one_right (by simp) (hrho_le z)
    · rw [hweight, ← hrho z hz]
      calc
        (F z : ℝ≥0∞) / D * rho z =
            ((A z : ℝ≥0∞) / S +
              ((F z : ℝ≥0∞) / D - (A z : ℝ≥0∞) / S)) * rho z := by
              rw [add_tsub_cancel_of_le (hratio z)]
        _ = (A z : ℝ≥0∞) / S * rho z +
              ((F z : ℝ≥0∞) / D - (A z : ℝ≥0∞) / S) *
                rho z := by rw [add_mul]
        _ ≤ (A z : ℝ≥0∞) / S * rho z +
              ((F z : ℝ≥0∞) / D - (A z : ℝ≥0∞) / S) * 1 := by
            exact add_le_add le_rfl (mul_le_mul' le_rfl (hrho_le z))
        _ = (A z : ℝ≥0∞) / S * rho z +
              ((F z : ℝ≥0∞) / D - (A z : ℝ≥0∞) / S) := by
            rw [mul_one]
  have hresidual :
      ∑ z ∈ s,
          ((F z : ℝ≥0∞) / D - (A z : ℝ≥0∞) / S) =
        ((S - ∑ z ∈ s, A z : Nat) : ℝ≥0∞) / S := by
    let sumA : ℝ≥0∞ := ∑ z ∈ s, (A z : ℝ≥0∞) / S
    let sumF : ℝ≥0∞ := ∑ z ∈ s, (F z : ℝ≥0∞) / D
    let residual : ℝ≥0∞ :=
      ∑ z ∈ s,
        ((F z : ℝ≥0∞) / D - (A z : ℝ≥0∞) / S)
    have hsumA_top : sumA ≠ ∞ := by
      apply ENNReal.sum_ne_top.2
      intro z hz
      exact ENNReal.div_ne_top ENNReal.coe_ne_top (by exact_mod_cast hS.ne')
    have hsumAF : sumA ≤ sumF :=
      Finset.sum_le_sum fun z _ => hratio z
    have hdecomp : sumA + residual = sumF := by
      dsimp only [sumA, residual, sumF]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun z _ => add_tsub_cancel_of_le (hratio z)
    have hresidual_eq : residual = sumF - sumA := by
      apply (ENNReal.add_right_inj hsumA_top).mp
      rw [hdecomp, add_tsub_cancel_of_le hsumAF]
    have hsumF_one : sumF = 1 := by
      dsimp only [sumF]
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul, ← Nat.cast_sum, hmassF]
      exact ENNReal.mul_inv_cancel
        (show (D : ℝ≥0∞) ≠ 0 by exact_mod_cast hD.ne') ENNReal.coe_ne_top
    have hsumA_eq :
        sumA = ((∑ z ∈ s, A z : Nat) : ℝ≥0∞) / S := by
      dsimp only [sumA]
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul, ← Nat.cast_sum]
    rw [show (∑ z ∈ s,
        ((F z : ℝ≥0∞) / D - (A z : ℝ≥0∞) / S)) = residual from rfl,
      hresidual_eq, hsumF_one, hsumA_eq]
    have hratio_one :
        (((∑ z ∈ s, A z : Nat) : ℝ≥0∞) / S) ≤ 1 := by
      apply (ENNReal.div_le_iff
        (by exact_mod_cast hS.ne') ENNReal.coe_ne_top).2
      simpa using (show ((∑ z ∈ s, A z : Nat) : ℝ≥0∞) ≤ S by
        exact_mod_cast hmassA)
    have hratio_top :
        (((∑ z ∈ s, A z : Nat) : ℝ≥0∞) / S) ≠ ∞ :=
      ENNReal.div_ne_top ENNReal.coe_ne_top (by exact_mod_cast hS.ne')
    apply (ENNReal.add_right_inj hratio_top).mp
    rw [add_tsub_cancel_of_le hratio_one, ← ENNReal.add_div, ← Nat.cast_add,
      Nat.add_sub_of_le hmassA]
    exact (ENNReal.div_self
      (show (S : ℝ≥0∞) ≠ 0 by exact_mod_cast hS.ne') ENNReal.coe_ne_top).symm
  constructor
  · exact Finset.sum_le_sum fun z _ => hlower z
  · calc
      (∑ z ∈ s, (F z : ℝ≥0∞) / D * rho z) ≤
          ∑ z ∈ s,
            (((A z * w z : Nat) : ℝ≥0∞) / (S * H) +
              ((F z : ℝ≥0∞) / D - (A z : ℝ≥0∞) / S)) :=
        Finset.sum_le_sum fun z _ => hupper z
      _ = (∑ z ∈ s, ((A z * w z : Nat) : ℝ≥0∞) / (S * H)) +
          ∑ z ∈ s,
            ((F z : ℝ≥0∞) / D - (A z : ℝ≥0∞) / S) := by
        rw [Finset.sum_add_distrib]
      _ = (∑ z ∈ s, ((A z * w z : Nat) : ℝ≥0∞) / (S * H)) +
          ((S - ∑ z ∈ s, A z : Nat) : ℝ≥0∞) / S := by
        rw [hresidual]

private theorem sum_union_support_left
    (F A : ToVCVio.IntMeasure) :
    ∑ z ∈ F.coeff.support ∪ A.coeff.support, F z = ToVCVio.totalMass F := by
  change (∑ z ∈ F.coeff.support ∪ A.coeff.support, F z) =
    ∑ z ∈ F.coeff.support, F z
  symm
  apply Finset.sum_subset Finset.subset_union_left
  intro z hz hz'
  have hnot : z ∉ F.coeff.support := hz'
  exact Finsupp.notMem_support_iff.mp hnot

private theorem sum_union_support_right
    (F A : ToVCVio.IntMeasure) :
    ∑ z ∈ F.coeff.support ∪ A.coeff.support, A z = ToVCVio.totalMass A := by
  rw [Finset.union_comm]
  exact sum_union_support_left A F

private theorem expectedValue_challengeEntryNoiseIntExp_eq_support_sum :
    OracleComp.EvalDist.expectedValue
        challengeEntryNoiseIntExp challengeFailureRamp =
      ∑ z ∈ ((productCounts ^ 704) * d1Counts).coeff.support ∪
          (lowerCounts 704 * d1Counts).coeff.support,
        (((productCounts ^ 704) * d1Counts) z : ℝ≥0∞) /
            256 ^ 1409 * challengeFailureRamp z := by
  rw [OracleComp.EvalDist.expectedValue_def]
  simp_rw [probOutput_challengeEntryNoiseIntExp_counts]
  rw [tsum_eq_sum (s :=
    ((productCounts ^ 704) * d1Counts).coeff.support ∪
      (lowerCounts 704 * d1Counts).coeff.support)]
  intro z hz
  simp only [Finset.mem_union, not_or] at hz
  rw [Finsupp.notMem_support_iff.mp hz.1]
  rw [Nat.cast_zero, ENNReal.zero_div, zero_mul]

/-- The exact expected ramp is enclosed by the rounded weighted mass and missing mass. -/
theorem challengeEntryRamp_missingMass_bounds :
    let F := (productCounts ^ 704) * d1Counts
    let A := lowerCounts 704 * d1Counts
    let s := F.coeff.support ∪ A.coeff.support
    (∑ z ∈ s,
        ((A z * (z.natAbs - 256) : Nat) : ℝ≥0∞) /
          ((256 * scale) * 512)) ≤
        OracleComp.EvalDist.expectedValue
          challengeEntryNoiseIntExp challengeFailureRamp ∧
      OracleComp.EvalDist.expectedValue
          challengeEntryNoiseIntExp challengeFailureRamp ≤
        (∑ z ∈ s,
          ((A z * (z.natAbs - 256) : Nat) : ℝ≥0∞) /
            ((256 * scale) * 512)) +
          (((256 * scale) - ToVCVio.totalMass A : Nat) : ℝ≥0∞) /
            (256 * scale) := by
  dsimp only
  have hfinite := finite_missingMass_enclosure
    (((productCounts ^ 704) * d1Counts).coeff.support ∪
      (lowerCounts 704 * d1Counts).coeff.support)
    ((productCounts ^ 704) * d1Counts)
    (lowerCounts 704 * d1Counts)
    (256 ^ 1409) (256 * scale) 512
    challengeFailureRamp (fun z => z.natAbs - 256)
    (by exact pow_pos (by norm_num) _)
    (by unfold scale; positivity)
    (by
      rw [sum_union_support_left, totalMass_fullCounts])
    approxCounts_domination
    challengeFailureRamp_eq_weight_on_approxCounts
    challengeFailureRamp_le_one_local
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hfinite
  rw [← expectedValue_challengeEntryNoiseIntExp_eq_support_sum,
    sum_union_support_right] at hfinite
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hfinite

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

private theorem productCounts_apply_le_totalMass (z : ℤ) :
    productCounts z ≤ ToVCVio.totalMass productCounts := by
  simpa using finsetSum_apply_le_totalMass productCounts {z}

/-- Every convolution coefficient used by the recurrence is strictly below the radix. -/
theorem convolutionCoefficient_lt_radix (n : Nat) (z : ℤ) :
    (lowerCounts n * productCounts) z < radix := by
  calc
    (lowerCounts n * productCounts) z ≤
        ToVCVio.totalMass (lowerCounts n) * 65536 := by
      apply MLKEM.mul_apply_le
        (show ToVCVio.MeasureWindow (lowerCounts n)
            (-384) (-384 + (769 : ℤ) - 1) by
          norm_num
          exact measureWindow_lowerCounts n)
      intro v
      rw [← totalMass_productCounts]
      exact productCounts_apply_le_totalMass v
    _ ≤ scale * 65536 := Nat.mul_le_mul_right 65536 (totalMass_lowerCounts_le n)
    _ < radix := by norm_num [scale, radix]

end

end lweCKA.ChallengeCertificateModel
