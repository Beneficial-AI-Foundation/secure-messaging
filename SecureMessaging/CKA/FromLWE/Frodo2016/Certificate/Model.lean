/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Model.Noise

/-!
# Domination and ramp enclosure for historical Frodo certificates

This endpoint bounds the exact entry-noise distribution by the rounded
certificate measure and proves the final reconciliation-ramp enclosure.
-/

open OracleComp
open scoped BigOperators ENNReal

namespace lweCKA.Frodo2016.Certificate

open SharedModelInternal

set_option Elab.async false in
section

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
        intro hs
        exact hx (Finset.mem_inter.mpr ⟨hxs, hs⟩)
      rw [Finsupp.notMem_support_iff.mp hnot, zero_mul]
    _ ≤ ∑ x ∈ F.coeff.support, F x * G (z - x) :=
      Finset.sum_le_sum_of_subset Finset.inter_subset_right
    _ = (F * G) z := by
      rw [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum]
      congr 1
      funext x
      rw [show -x + z = z - x by ring]

private theorem lowerCounts_domination
    (c : Config) (k : ℕ) (z : ℤ) :
    (2 ^ (2 * c.seedBits)) ^ k * lowerCounts c k z ≤
      2 ^ 128 *
        ((ToVCVio.productMeasure (counts c) (counts c)) ^ k) z := by
  induction k generalizing z with
  | zero =>
      by_cases hz : z = 0 <;>
        simp [lowerCounts, AddMonoidAlgebra.one_def, hz,
          -LaurentPolynomial.single_eq_C_mul_T]
  | succ k ih =>
      let P := ToVCVio.productMeasure (counts c) (counts c)
      by_cases hz : z ∈ Finset.Icc (-(c.window : ℤ)) (c.window : ℤ)
      · rw [lowerCounts_succ_apply, ite_eq_left hz]
        have hdiv :
            2 ^ (2 * c.seedBits) *
                ((lowerCounts c k * P) z / 2 ^ (2 * c.seedBits)) ≤
              (lowerCounts c k * P) z := by
          simpa [Nat.mul_comm] using
            Nat.div_mul_le_self ((lowerCounts c k * P) z) (2 ^ (2 * c.seedBits))
        calc
          (2 ^ (2 * c.seedBits)) ^ (k + 1) *
                ((lowerCounts c k * P) z / 2 ^ (2 * c.seedBits)) =
              (2 ^ (2 * c.seedBits)) ^ k *
                (2 ^ (2 * c.seedBits) *
                  ((lowerCounts c k * P) z / 2 ^ (2 * c.seedBits))) := by
            rw [pow_succ]
            ring
          _ ≤ (2 ^ (2 * c.seedBits)) ^ k * (lowerCounts c k * P) z :=
            Nat.mul_le_mul_left _ hdiv
          _ = ∑ i ∈ Finset.range (2 * c.window + 1),
                ((2 ^ (2 * c.seedBits)) ^ k *
                  lowerCounts c k (-(c.window : ℤ) + i)) *
                    P (z - (-(c.window : ℤ) + i)) := by
            rw [ToVCVio.mul_apply_window
              (show ToVCVio.MeasureWindow (lowerCounts c k)
                  (-(c.window : ℤ))
                  (-(c.window : ℤ) + (2 * c.window + 1 : ℕ) - 1) by
                convert measureWindow_lowerCounts c k using 1
                all_goals push_cast
                all_goals omega) z,
              Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
          _ ≤ ∑ i ∈ Finset.range (2 * c.window + 1),
                (2 ^ 128 * (P ^ k) (-(c.window : ℤ) + i)) *
                  P (z - (-(c.window : ℤ) + i)) := by
            exact Finset.sum_le_sum fun i _ =>
              Nat.mul_le_mul_right _ (ih (-(c.window : ℤ) + i))
          _ = 2 ^ 128 * ∑ i ∈ Finset.range (2 * c.window + 1),
                (P ^ k) (-(c.window : ℤ) + i) *
                  P (z - (-(c.window : ℤ) + i)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
          _ ≤ 2 ^ 128 * ((P ^ k) * P) z := by
            apply Nat.mul_le_mul_left
            let s : Finset ℤ := (Finset.range (2 * c.window + 1)).image
              (fun i : Nat => -(c.window : ℤ) + i)
            have hinj : Function.Injective (fun i : Nat => -(c.window : ℤ) + i) := by
              intro i j h
              exact_mod_cast Int.add_left_cancel h
            rw [show (∑ i ∈ Finset.range (2 * c.window + 1),
                (P ^ k) (-(c.window : ℤ) + i) *
                  P (z - (-(c.window : ℤ) + i))) =
                ∑ x ∈ s, (P ^ k) x * P (z - x) by
                  unfold s
                  rw [Finset.sum_image hinj.injOn]]
            exact finsetSum_mul_apply_le _ _ _ _
          _ = 2 ^ 128 * (P ^ (k + 1)) z := by
            rw [show P ^ (k + 1) = P ^ k * P by rw [pow_succ]]
      · rw [lowerCounts_succ_apply, ite_eq_right hz]
        simp

private theorem lowerCounts_mul_counts_domination
    (c : Config) (k : ℕ) (z : ℤ) :
    (2 ^ (2 * c.seedBits)) ^ k * (lowerCounts c k * counts c) z ≤
      2 ^ 128 *
        (((ToVCVio.productMeasure (counts c) (counts c)) ^ k * counts c) z) := by
  let P := ToVCVio.productMeasure (counts c) (counts c)
  calc
    (2 ^ (2 * c.seedBits)) ^ k * (lowerCounts c k * counts c) z =
        ∑ i ∈ Finset.range (2 * c.window + 1),
          ((2 ^ (2 * c.seedBits)) ^ k *
            lowerCounts c k (-(c.window : ℤ) + i)) *
              counts c (z - (-(c.window : ℤ) + i)) := by
      rw [ToVCVio.mul_apply_window
        (show ToVCVio.MeasureWindow (lowerCounts c k)
            (-(c.window : ℤ))
            (-(c.window : ℤ) + (2 * c.window + 1 : ℕ) - 1) by
          convert measureWindow_lowerCounts c k using 1
          all_goals push_cast
          all_goals omega) z,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    _ ≤ ∑ i ∈ Finset.range (2 * c.window + 1),
          (2 ^ 128 * (P ^ k) (-(c.window : ℤ) + i)) *
            counts c (z - (-(c.window : ℤ) + i)) := by
      exact Finset.sum_le_sum fun i _ =>
        Nat.mul_le_mul_right _ (lowerCounts_domination c k (-(c.window : ℤ) + i))
    _ = 2 ^ 128 * ∑ i ∈ Finset.range (2 * c.window + 1),
          (P ^ k) (-(c.window : ℤ) + i) *
            counts c (z - (-(c.window : ℤ) + i)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    _ ≤ 2 ^ 128 * ((P ^ k) * counts c) z := by
      apply Nat.mul_le_mul_left
      let s : Finset ℤ := (Finset.range (2 * c.window + 1)).image
        (fun i : Nat => -(c.window : ℤ) + i)
      have hinj : Function.Injective (fun i : Nat => -(c.window : ℤ) + i) := by
        intro i j h
        exact_mod_cast Int.add_left_cancel h
      rw [show (∑ i ∈ Finset.range (2 * c.window + 1),
          (P ^ k) (-(c.window : ℤ) + i) *
            counts c (z - (-(c.window : ℤ) + i))) =
          ∑ x ∈ s, (P ^ k) x * counts c (z - x) by
            unfold s
            rw [Finset.sum_image hinj.injOn]]
      exact finsetSum_mul_apply_le _ _ _ _

private theorem totalMass_fullCounts
    (c : Config) (hmass : ToVCVio.totalMass (counts c) = 2 ^ c.seedBits) :
    ToVCVio.totalMass
        ((ToVCVio.productMeasure (counts c) (counts c)) ^ (2 * c.n) * counts c) =
      (2 ^ c.seedBits) ^ (4 * c.n + 1) := by
  rw [ToVCVio.totalMass_mul, ToVCVio.totalMass_pow,
    ToVCVio.totalMass_productMeasure, hmass]
  rw [← pow_two, ← pow_mul, ← pow_succ]
  congr 1
  omega

private theorem totalMass_approxCounts
    (c : Config) (hmass : ToVCVio.totalMass (counts c) = 2 ^ c.seedBits) :
    ToVCVio.totalMass (lowerCounts c (2 * c.n) * counts c) =
      2 ^ c.seedBits * ToVCVio.totalMass (lowerCounts c (2 * c.n)) := by
  rw [ToVCVio.totalMass_mul, hmass, Nat.mul_comm]

private theorem approxCounts_domination
    (c : Config) (z : ℤ) :
    (2 ^ c.seedBits) ^ (4 * c.n + 1) *
        (lowerCounts c (2 * c.n) * counts c) z ≤
      (2 ^ c.seedBits * 2 ^ 128) *
        (((ToVCVio.productMeasure (counts c) (counts c)) ^ (2 * c.n) *
          counts c) z) := by
  have h := lowerCounts_mul_counts_domination c (2 * c.n) z
  rw [← pow_mul] at h
  have hmul := Nat.mul_le_mul_left (2 ^ c.seedBits) h
  calc
    (2 ^ c.seedBits) ^ (4 * c.n + 1) *
        (lowerCounts c (2 * c.n) * counts c) z =
      2 ^ c.seedBits *
        ((2 ^ c.seedBits) ^ (2 * (2 * c.n)) *
          (lowerCounts c (2 * c.n) * counts c) z) := by
        rw [show 4 * c.n + 1 = 2 * (2 * c.n) + 1 by omega, pow_succ]
        ring
    _ ≤ 2 ^ c.seedBits *
        (2 ^ 128 *
          (((ToVCVio.productMeasure (counts c) (counts c)) ^ (2 * c.n) *
            counts c) z)) := by
      have hpow : (2 ^ c.seedBits) ^ (2 * (2 * c.n)) =
          2 ^ (2 * c.seedBits * (2 * c.n)) := by
        rw [← pow_mul]
        congr 1
        ring
      rw [hpow]
      exact hmul
    _ = _ := by ring

private theorem reconciliationFailureRamp_le_one (p : Params) (z : ℤ) :
    reconciliationFailureRamp p z ≤ 1 := by
  unfold reconciliationFailureRamp
  apply (ENNReal.div_le_iff (by simp [Params.halfWidth]) (by simp)).2
  simpa only [one_mul] using
    (min_le_left (p.halfWidth : ℝ≥0∞)
      ((modularDistance p (z : Scalar p) 0 : ℝ≥0∞) -
        2 ^ (p.discardBits - 2)))

private theorem modularDistance_eq_natAbs_valMinAbs
    (p : Params) (u v : Scalar p) :
    modularDistance p u v = (u - v).valMinAbs.natAbs := by
  by_cases h : u = v
  · subst v
    simp [modularDistance]
  · have hsub : u - v ≠ 0 := sub_ne_zero.mpr h
    have hneg : v - u = -(u - v) := by simp
    have hnegval : (v - u).val = p.q - (u - v).val := by
      rw [hneg, ZMod.neg_val, ite_eq_right hsub]
    rw [modularDistance, hnegval, ZMod.valMinAbs_natAbs_eq_min]

private theorem valMinAbs_intCast_eq_of_natAbs_le
    (p : Params) (M : ℕ) (hM : 2 * M < p.q)
    (z : ℤ) (hz : z.natAbs ≤ M) :
    ((z : Scalar p).valMinAbs) = z := by
  have hzrange : (-(M : ℤ)) ≤ z ∧ z ≤ M := by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z <;> simp_all
  apply (ZMod.valMinAbs_spec (z : Scalar p) z).2
  constructor
  · rfl
  · simp only [Set.mem_Ioc]
    exact_mod_cast (show (-(p.q : ℤ)) < z * 2 ∧ z * 2 ≤ p.q by omega)

private theorem modularDistance_intCast_zero_eq_natAbs_of_le
    (p : Params) (M : ℕ) (hM : 2 * M < p.q)
    (z : ℤ) (hz : z.natAbs ≤ M) :
    modularDistance p (z : Scalar p) 0 = z.natAbs := by
  rw [modularDistance_eq_natAbs_valMinAbs, sub_zero,
    valMinAbs_intCast_eq_of_natAbs_le p M hM z hz]

private theorem halfWidth_eq_twice_radius
    (c : Config) (p : Params) (hp : p.WellFormed)
    (hr : 2 ^ (p.discardBits - 2) = c.radius) :
    p.halfWidth = 2 * c.radius := by
  have h := hp.keyBits_lt
  have hd : 2 ≤ p.discardBits := by
    simp only [Params.discardBits]
    omega
  rw [← hr, Params.halfWidth, show p.discardBits - 1 =
      (p.discardBits - 2) + 1 by omega, pow_succ]
  ring

private theorem reconciliationFailureRamp_eq_weight_of_natAbs_le
    (c : Config) (p : Params) (hp : p.WellFormed)
    (hr : 2 ^ (p.discardBits - 2) = c.radius)
    (hwindow : 2 * (c.window + c.a) < p.q)
    (z : ℤ) (hz : z.natAbs ≤ c.window + c.a) :
    reconciliationFailureRamp p z =
      ((min (2 * c.radius) (z.natAbs - c.radius) : Nat) : ℝ≥0∞) /
        (2 * c.radius) := by
  unfold reconciliationFailureRamp
  have hrENN : (2 : ℝ≥0∞) ^ (p.discardBits - 2) = c.radius := by
    exact_mod_cast hr
  have hhalfENN : (p.halfWidth : ℝ≥0∞) = 2 * c.radius := by
    exact_mod_cast halfWidth_eq_twice_radius c p hp hr
  rw [modularDistance_intCast_zero_eq_natAbs_of_le p (c.window + c.a)
    hwindow z hz, hrENN, hhalfENN]
  have hsub : (z.natAbs : ℝ≥0∞) - c.radius =
      ((z.natAbs - c.radius : Nat) : ℝ≥0∞) := by
    simpa only [Nat.cast_ofNat] using
      (ENNReal.natCast_sub z.natAbs c.radius).symm
  have hmin :
      min (2 * (c.radius : ℝ≥0∞))
          ((z.natAbs - c.radius : Nat) : ℝ≥0∞) =
        ((min (2 * c.radius) (z.natAbs - c.radius) : Nat) : ℝ≥0∞) := by
    by_cases h : 2 * c.radius ≤ z.natAbs - c.radius
    · have hENN : 2 * (c.radius : ℝ≥0∞) ≤
          ((z.natAbs - c.radius : Nat) : ℝ≥0∞) := by
        exact_mod_cast h
      rw [min_eq_left h, min_eq_left hENN]
      norm_num
    · have hle : z.natAbs - c.radius ≤ 2 * c.radius := Nat.le_of_not_ge h
      have hleENN : ((z.natAbs - c.radius : Nat) : ℝ≥0∞) ≤
          2 * (c.radius : ℝ≥0∞) := by
        exact_mod_cast hle
      rw [min_eq_right hle, min_eq_right hleENN]
  rw [hsub, hmin]

private theorem reconciliationFailureRamp_eq_weight_on_approxCounts
    (c : Config) (p : Params) (hp : p.WellFormed)
    (hr : 2 ^ (p.discardBits - 2) = c.radius)
    (hwindow : 2 * (c.window + c.a) < p.q)
    (z : ℤ) (hz : (lowerCounts c (2 * c.n) * counts c) z ≠ 0) :
    reconciliationFailureRamp p z =
      ((min (2 * c.radius) (z.natAbs - c.radius) : Nat) : ℝ≥0∞) /
        (2 * c.radius) := by
  apply reconciliationFailureRamp_eq_weight_of_natAbs_le c p hp hr hwindow
  have hw := measureWindow_approxCounts c (2 * c.n) z hz
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · simp only [Int.natAbs_natCast]
    simp only [center] at hw
    omega
  · simp only [Int.natAbs_neg, Int.natAbs_natCast]
    simp only [center] at hw
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
      D * ∑ z ∈ s, A z = ∑ z ∈ s, D * A z := by rw [Finset.mul_sum]
      _ ≤ ∑ z ∈ s, S * F z := Finset.sum_le_sum fun z _ => hdom z
      _ = S * ∑ z ∈ s, F z := by rw [Finset.mul_sum]
      _ = S * D := by rw [hmassF]
  have hmassA : ∑ z ∈ s, A z ≤ S := by
    exact le_of_mul_le_mul_left (by simpa [Nat.mul_comm] using hscaled) hD
  have hratio (z : ℤ) : (A z : ℝ≥0∞) / S ≤ (F z : ℝ≥0∞) / D :=
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
              ((F z : ℝ≥0∞) / D - (A z : ℝ≥0∞) / S) * rho z := by rw [add_mul]
        _ ≤ (A z : ℝ≥0∞) / S * rho z +
              ((F z : ℝ≥0∞) / D - (A z : ℝ≥0∞) / S) * 1 := by
            exact add_le_add le_rfl (mul_le_mul' le_rfl (hrho_le z))
        _ = _ := by rw [mul_one]
  have hresidual :
      ∑ z ∈ s, ((F z : ℝ≥0∞) / D - (A z : ℝ≥0∞) / S) =
        ((S - ∑ z ∈ s, A z : Nat) : ℝ≥0∞) / S := by
    let sumA : ℝ≥0∞ := ∑ z ∈ s, (A z : ℝ≥0∞) / S
    let sumF : ℝ≥0∞ := ∑ z ∈ s, (F z : ℝ≥0∞) / D
    let residual : ℝ≥0∞ :=
      ∑ z ∈ s, ((F z : ℝ≥0∞) / D - (A z : ℝ≥0∞) / S)
    have hsumA_top : sumA ≠ ∞ := by
      apply ENNReal.sum_ne_top.2
      intro z hz
      exact ENNReal.div_ne_top ENNReal.coe_ne_top (by exact_mod_cast hS.ne')
    have hsumAF : sumA ≤ sumF := Finset.sum_le_sum fun z _ => hratio z
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
    have hratio_top : (((∑ z ∈ s, A z : Nat) : ℝ≥0∞) / S) ≠ ∞ :=
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
          ∑ z ∈ s, (((A z * w z : Nat) : ℝ≥0∞) / (S * H) +
            ((F z : ℝ≥0∞) / D - (A z : ℝ≥0∞) / S)) :=
        Finset.sum_le_sum fun z _ => hupper z
      _ = (∑ z ∈ s, ((A z * w z : Nat) : ℝ≥0∞) / (S * H)) +
          ∑ z ∈ s, ((F z : ℝ≥0∞) / D - (A z : ℝ≥0∞) / S) := by
        rw [Finset.sum_add_distrib]
      _ = _ := by rw [hresidual]

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

private theorem sum_union_support_weighted_right
    (F A : ToVCVio.IntMeasure) (w : ℤ → Nat) :
    ∑ z ∈ F.coeff.support ∪ A.coeff.support, A z * w z =
      ∑ z ∈ A.coeff.support, A z * w z := by
  symm
  apply Finset.sum_subset Finset.subset_union_right
  intro z hz hz'
  have hnot : z ∉ A.coeff.support := hz'
  rw [Finsupp.notMem_support_iff.mp hnot, zero_mul]

private theorem expectedValue_entryNoiseIntExp_eq_support_sum
    (c : Config) (p : Params) (χ : ProbComp ℤ)
    (hn : p.n = c.n)
    (hlaw : ∀ z : ℤ, Pr{let x ← χ}[x = z] = (counts c z : ℝ≥0∞) / 2 ^ c.seedBits)
    (hsym : ∀ z : ℤ, c.weight (-z) = c.weight z) :
    expectedValue (entryNoiseIntExp p.n χ) (reconciliationFailureRamp p) =
      ∑ z ∈
          (((ToVCVio.productMeasure (counts c) (counts c)) ^ (2 * c.n) *
              counts c).coeff.support ∪
            (lowerCounts c (2 * c.n) * counts c).coeff.support),
        ((((ToVCVio.productMeasure (counts c) (counts c)) ^ (2 * c.n) *
            counts c) z : ℝ≥0∞) /
          (2 ^ c.seedBits) ^ (4 * c.n + 1)) * reconciliationFailureRamp p z := by
  rw [expectedValue_def]
  simp_rw [probOutput_entryNoiseIntExp_counts c χ hlaw hsym]
  rw [hn]
  rw [tsum_eq_sum (s :=
    (((ToVCVio.productMeasure (counts c) (counts c)) ^ (2 * c.n) *
        counts c).coeff.support ∪
      (lowerCounts c (2 * c.n) * counts c).coeff.support))]
  intro z hz
  simp only [Finset.mem_union, not_or] at hz
  rw [Finsupp.notMem_support_iff.mp hz.1]
  simp

/-- The expected reconciliation ramp is bounded by the packed rounded mass and missing mass. -/
theorem expectedValue_ramp_le_certificate
    (c : Config) (p : Params) (hp : p.WellFormed)
    (χ : ProbComp ℤ) (hχ : prFail χ = 0)
    (hn : p.n = c.n) (hr : 2 ^ (p.discardBits - 2) = c.radius)
    (hbits : 0 < c.seedBits)
    (hmass : ToVCVio.totalMass (counts c) = 2 ^ c.seedBits)
    (hlaw : ∀ z : ℤ, Pr{let x ← χ}[x = z] = (counts c z : ℝ≥0∞) / 2 ^ c.seedBits)
    (hsym : ∀ z : ℤ, c.weight (-z) = c.weight z)
    (hwindow : 2 * (c.window + c.a) < p.q)
    (hpack : c.window + c.a < 2 ^ (c.seedBits + 1)) :
    expectedValue (entryNoiseIntExp p.n χ) (reconciliationFailureRamp p) ≤
      ((certificateValues c).1 : ℝ≥0∞) /
        (2 ^ 128 * 2 ^ c.seedBits * (2 * c.radius)) +
      ((certificateValues c).2 : ℝ≥0∞) / 2 ^ 128 := by
  have hχ0 : prFail χ = 0 := hχ
  clear hχ0
  have hfinite := finite_missingMass_enclosure
    ((((ToVCVio.productMeasure (counts c) (counts c)) ^ (2 * c.n) *
        counts c).coeff.support ∪
      (lowerCounts c (2 * c.n) * counts c).coeff.support))
    ((ToVCVio.productMeasure (counts c) (counts c)) ^ (2 * c.n) * counts c)
    (lowerCounts c (2 * c.n) * counts c)
    ((2 ^ c.seedBits) ^ (4 * c.n + 1)) (2 ^ c.seedBits * 2 ^ 128)
    (2 * c.radius) (reconciliationFailureRamp p)
    (fun z => min (2 * c.radius) (z.natAbs - c.radius))
    (pow_pos (pow_pos (by omega) _) _)
    (Nat.mul_pos (pow_pos (by omega) _) (pow_pos (by omega) _))
    (by rw [sum_union_support_left, totalMass_fullCounts c hmass])
    (approxCounts_domination c)
    (by
      intro z hz
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        reconciliationFailureRamp_eq_weight_on_approxCounts
          c p hp hr hwindow z hz)
    (reconciliationFailureRamp_le_one p)
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hfinite
  rw [← expectedValue_entryNoiseIntExp_eq_support_sum c p χ hn hlaw hsym,
    sum_union_support_right] at hfinite
  have hweighted :
      (∑ z ∈
          (((ToVCVio.productMeasure (counts c) (counts c)) ^ (2 * c.n) *
              counts c).coeff.support ∪
            (lowerCounts c (2 * c.n) * counts c).coeff.support),
        ((lowerCounts c (2 * c.n) * counts c) z : ℝ≥0∞) *
            ((min (2 * c.radius) (z.natAbs - c.radius) : Nat) : ℝ≥0∞) /
          ((2 ^ c.seedBits * 2 ^ 128) * (2 * c.radius))) =
        ((∑ z ∈ (lowerCounts c (2 * c.n) * counts c).coeff.support,
            (lowerCounts c (2 * c.n) * counts c) z *
              min (2 * c.radius) (z.natAbs - c.radius) : Nat) : ℝ≥0∞) /
          ((2 ^ c.seedBits * 2 ^ 128) * (2 * c.radius)) := by
    simp only [← Nat.cast_mul, div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Nat.cast_sum,
      sum_union_support_weighted_right]
  rw [hweighted] at hfinite
  have hmissingNat :
      2 ^ c.seedBits * 2 ^ 128 -
          ToVCVio.totalMass (lowerCounts c (2 * c.n) * counts c) =
        2 ^ c.seedBits *
          (2 ^ 128 - ToVCVio.totalMass (lowerCounts c (2 * c.n))) := by
    rw [totalMass_approxCounts c hmass, Nat.mul_sub_left_distrib]
  have hmissing :
      ((2 ^ c.seedBits * 2 ^ 128 -
          ToVCVio.totalMass (lowerCounts c (2 * c.n) * counts c) : Nat) :
            ℝ≥0∞) /
          (2 ^ c.seedBits * 2 ^ 128) =
        ((2 ^ 128 - ToVCVio.totalMass (lowerCounts c (2 * c.n)) : Nat) :
            ℝ≥0∞) / 2 ^ 128 := by
    rw [hmissingNat]
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    exact ENNReal.mul_div_mul_left
      (((2 ^ 128 - ToVCVio.totalMass (lowerCounts c (2 * c.n)) : Nat) :
        ℝ≥0∞)) ((2 : ℝ≥0∞) ^ 128) (by positivity) (by simp)
  rw [certificateValues_eq_counts c hbits hmass hpack]
  dsimp only
  calc
    _ ≤ ((∑ z ∈ (lowerCounts c (2 * c.n) * counts c).coeff.support,
            (lowerCounts c (2 * c.n) * counts c) z *
              min (2 * c.radius) (z.natAbs - c.radius) : Nat) : ℝ≥0∞) /
          ((2 ^ c.seedBits * 2 ^ 128) * (2 * c.radius)) +
        ((2 ^ c.seedBits * 2 ^ 128 -
            ToVCVio.totalMass (lowerCounts c (2 * c.n) * counts c) : Nat) :
              ℝ≥0∞) /
          (2 ^ c.seedBits * 2 ^ 128) := hfinite.2
    _ = _ := by
      rw [hmissing]
      congr 2
      ring

end

end lweCKA.Frodo2016.Certificate
