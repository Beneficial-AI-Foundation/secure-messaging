/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Challenge.Model.Noise

/-!
# Lower approximation and ramp enclosure for the Frodo Challenge certificate

This endpoint proves the rounded lower-measure bounds, the missing-mass ramp
enclosure, and the final recurrence coefficient bound.
-/

open OracleComp
open scoped BigOperators ENNReal

namespace lweCKA.ChallengeCertificateModel

open ChallengeModelInternal

set_option Elab.async false in
section

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
    · simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
    · intro y hy hne
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hne, ite_false]
    · exact fun h => (h hz).elim
  · rw [if_neg hz]
    apply Finset.sum_eq_zero
    intro y hy
    have hne : y ≠ z := fun h => hz (h ▸ hy)
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hne, ite_false]

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
      by_cases hz : z = 0 <;> simp [lowerCounts, AddMonoidAlgebra.one_def, hz,
        -LaurentPolynomial.single_eq_C_mul_T]
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
    lweCKA.expectedValue
        challengeEntryNoiseIntExp challengeFailureRamp =
      ∑ z ∈ ((productCounts ^ 704) * d1Counts).coeff.support ∪
          (lowerCounts 704 * d1Counts).coeff.support,
        (((productCounts ^ 704) * d1Counts) z : ℝ≥0∞) /
            256 ^ 1409 * challengeFailureRamp z := by
  rw [lweCKA.expectedValue_def]
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
        lweCKA.expectedValue
          challengeEntryNoiseIntExp challengeFailureRamp ∧
      lweCKA.expectedValue
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
