/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.ReconciliationPhase.Geometry
import Mathlib.Order.Interval.Finset.Nat

/-!
# Exact phase geometry for Frodo reconciliation

This file gives closed forms for scalar reconciliation and counts the sender phases on which
reconciliation fails for a fixed modular difference.
-/

namespace lweCKA

open ReconciliationPhase.Internal

private theorem extractScalar_sub_radius_eq_iff_phase_of_hint_zero
    (p : Params) (hp : p.WellFormed) (w v : Scalar p)
    (hhint : hintScalar p v = 0) :
    extractScalar p (w - ((2 ^ (p.discardBits - 2) : ℕ) : Scalar p)) =
        extractScalar p v ↔
      ((((v.val % p.halfWidth + 2 ^ (p.discardBits - 2) : ℕ) : Scalar p) -
        (v - w)).val < p.blockWidth) := by
  let r := 2 ^ (p.discardBits - 2)
  let m := v.val / p.halfWidth
  let t := v.val % p.halfWidth
  let keySpace := 2 ^ p.keyBits
  have hhalfpos : 0 < p.halfWidth := by simp [Params.halfWidth]
  have hhalf := halfWidth_eq_two_mul_radius p hp
  have hwidth := blockWidth_eq_two_mul_halfWidth p hp
  have hq : p.q = keySpace * p.blockWidth := by
    simpa [keySpace] using q_eq_keySpace_mul_blockWidth p hp
  have hmod : m % 2 = 0 := by
    have hval := congrArg ZMod.val hhint
    simpa only [hintScalar, ZMod.val_natCast, ZMod.val_zero, m] using hval
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hmod
  have hmlt : m < 2 * keySpace := by
    apply (Nat.div_lt_iff_lt_mul hhalfpos).2
    have hvlt : v.val < p.q := ZMod.val_lt v
    have hfactor : keySpace * p.blockWidth = 2 * keySpace * p.halfWidth := by
      rw [hwidth]
      ring
    omega
  have hkkey : k < keySpace := by rw [hk] at hmlt; omega
  have hcenter : v.val = k * p.blockWidth + t := by
    calc
      v.val = t + p.halfWidth * m := (Nat.mod_add_div v.val p.halfWidth).symm
      _ = k * p.blockWidth + t := by rw [hk, hwidth]; ring
  have hround : (v.val + p.halfWidth) / p.blockWidth = k := by
    rw [roundedBlock_eq_halfIndex p hp, show v.val / p.halfWidth = m by rfl, hk]
    omega
  have hExtract : extractScalar p v = (k : KeyScalar p) := by
    simp only [extractScalar, hround]
  rw [hExtract]
  rw [extractScalar_eq_natCast_iff_centered p hp _ k (by simpa [keySpace] using hkkey)]
  have hcenterCast :
      ((k * p.blockWidth : ℕ) : Scalar p) + ((t : ℕ) : Scalar p) = v := by
    rw [← Nat.cast_add, ← hcenter, ZMod.natCast_zmod_val]
  have hhalfCast : ((p.halfWidth : ℕ) : Scalar p) = 2 * (r : Scalar p) := by
    simp only [r]
    rw [hhalf]
    norm_num
  change
    (w - (r : Scalar p) + ((p.halfWidth : ℕ) : Scalar p) -
        ((k * p.blockWidth : ℕ) : Scalar p)).val < p.blockWidth ↔ _
  have hexpr :
      w - (r : Scalar p) + ((p.halfWidth : ℕ) : Scalar p) -
          ((k * p.blockWidth : ℕ) : Scalar p) =
        ((t + r : ℕ) : Scalar p) - (v - w) := by
    rw [hhalfCast, Nat.cast_add, ← hcenterCast]
    ring
  rw [hexpr]

private theorem extractScalar_add_radius_eq_iff_phase_of_hint_one
    (p : Params) (hp : p.WellFormed) (w v : Scalar p)
    (hhint : hintScalar p v = 1) :
    extractScalar p (w + ((2 ^ (p.discardBits - 2) : ℕ) : Scalar p)) =
        extractScalar p v ↔
      ((((v.val % p.halfWidth + 2 ^ (p.discardBits - 2) : ℕ) : Scalar p) -
        (v - w)).val < p.blockWidth) := by
  let r := 2 ^ (p.discardBits - 2)
  let m := v.val / p.halfWidth
  let t := v.val % p.halfWidth
  let keySpace := 2 ^ p.keyBits
  let k := m / 2
  have hhalfpos : 0 < p.halfWidth := by simp [Params.halfWidth]
  have hkeypos : 0 < keySpace := by simp [keySpace]
  have hhalf := halfWidth_eq_two_mul_radius p hp
  have hwidth := blockWidth_eq_two_mul_halfWidth p hp
  have hq : p.q = keySpace * p.blockWidth := by
    simpa [keySpace] using q_eq_keySpace_mul_blockWidth p hp
  have hmod : m % 2 = 1 := by
    have hval := congrArg ZMod.val hhint
    simpa only [hintScalar, ZMod.val_natCast, ZMod.val_one, m] using hval
  have hm : m = 2 * k + 1 := by
    have hdecomp := Nat.mod_add_div m 2
    simp only [hmod] at hdecomp
    omega
  have hmlt : m < 2 * keySpace := by
    apply (Nat.div_lt_iff_lt_mul hhalfpos).2
    have hvlt : v.val < p.q := ZMod.val_lt v
    have hfactor : keySpace * p.blockWidth = 2 * keySpace * p.halfWidth := by
      rw [hwidth]
      ring
    omega
  have hkkey : k < keySpace := by omega
  have hksucc : k + 1 ≤ keySpace := by omega
  have hcenter : v.val = p.halfWidth * m + t := by
    calc
      v.val = t + p.halfWidth * m := (Nat.mod_add_div v.val p.halfWidth).symm
      _ = p.halfWidth * m + t := Nat.add_comm _ _
  have hround : (v.val + p.halfWidth) / p.blockWidth = k + 1 := by
    rw [roundedBlock_eq_halfIndex p hp, show v.val / p.halfWidth = m by rfl, hm]
    omega
  have hExtract : extractScalar p v = ((k + 1 : ℕ) : KeyScalar p) := by
    simp only [extractScalar, hround]
  rw [hExtract]
  have hcenterCast :
      ((p.halfWidth * m : ℕ) : Scalar p) + ((t : ℕ) : Scalar p) = v := by
    rw [← Nat.cast_add, ← hcenter, ZMod.natCast_zmod_val]
  have hhalfCast : ((p.halfWidth : ℕ) : Scalar p) = 2 * (r : Scalar p) := by
    simp only [r]
    rw [hhalf]
    norm_num
  have hwidthCast : ((p.blockWidth : ℕ) : Scalar p) =
      2 * ((p.halfWidth : ℕ) : Scalar p) := by
    rw [hwidth]
    norm_num
  have hexpr :
      w + (r : Scalar p) + ((p.halfWidth : ℕ) : Scalar p) -
          (((k + 1) * p.blockWidth : ℕ) : Scalar p) =
        ((t + r : ℕ) : Scalar p) - (v - w) := by
    rw [Nat.cast_add, Nat.cast_mul, hwidthCast, hhalfCast]
    rw [hm] at hcenterCast
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at hcenterCast
    rw [← hcenterCast, hhalfCast]
    push_cast
    ring
  by_cases hlast : k + 1 = keySpace
  · have hkeycast : (((k + 1 : ℕ) : KeyScalar p)) = 0 := by
      rw [hlast]
      exact ZMod.natCast_self keySpace
    rw [hkeycast]
    have hfiber := extractScalar_eq_natCast_iff_centered p hp
      (w + (r : Scalar p)) 0 hkeypos
    simp only [Nat.zero_mul, Nat.cast_zero, sub_zero] at hfiber
    have hcenterzero :
        ((((k + 1) * p.blockWidth : ℕ) : Scalar p)) = 0 := by
      rw [hlast, ← hq]
      exact ZMod.natCast_self p.q
    have hsame :
        w + (r : Scalar p) + ((p.halfWidth : ℕ) : Scalar p) =
          w + (r : Scalar p) + ((p.halfWidth : ℕ) : Scalar p) -
            (((k + 1) * p.blockWidth : ℕ) : Scalar p) := by
      rw [hcenterzero, sub_zero]
    rw [hfiber, hsame, hexpr]
  · have hlt : k + 1 < keySpace := by omega
    rw [extractScalar_eq_natCast_iff_centered p hp _ (k + 1)
      (by simpa [keySpace] using hlt), hexpr]

/-- Exact scalar agreement in terms of sender phase and sender-minus-receiver difference. -/
theorem reconcileScalar_eq_extractScalar_iff_phase
    (p : Params) (hp : p.WellFormed) (w v : Scalar p) :
    reconcileScalar p w (hintScalar p v) = extractScalar p v ↔
      ((((v.val % p.halfWidth + 2 ^ (p.discardBits - 2) : ℕ) : Scalar p) -
        (v - w)).val < p.blockWidth) := by
  by_cases hzero : hintScalar p v = 0
  · rw [hzero, reconcileScalar_zero_eq_extractScalar_sub_radius p hp]
    exact extractScalar_sub_radius_eq_iff_phase_of_hint_zero p hp w v hzero
  · have hone : hintScalar p v = 1 := by
      apply ZMod.val_injective
      have hlt := ZMod.val_lt (hintScalar p v)
      have hpos : 0 < (hintScalar p v).val := by
        rw [ZMod.val_pos]
        exact hzero
      rw [ZMod.val_one]
      omega
    rw [hone, reconcileScalar_one_eq_extractScalar_add_radius p hp]
    exact extractScalar_add_radius_eq_iff_phase_of_hint_one p hp w v hone

/-- The exact number of failing sender phases for a fixed modular difference. -/
theorem card_reconciliationFailurePhases
    (p : Params) (hp : p.WellFormed) (z : Scalar p) :
    ((Finset.range p.halfWidth).filter fun u =>
      p.blockWidth ≤
        ((((u + 2 ^ (p.discardBits - 2) : ℕ) : Scalar p) - z).val)).card =
      min p.halfWidth
        (modularDistance p z 0 - 2 ^ (p.discardBits - 2)) := by
  let r := 2 ^ (p.discardBits - 2)
  have hrpos : 0 < r := by simp [r]
  have hhalf := halfWidth_eq_two_mul_radius p hp
  have hwidth := blockWidth_eq_two_mul_halfWidth p hp
  have hq := q_eq_keySpace_mul_blockWidth p hp
  have hkey : 2 ≤ 2 ^ p.keyBits := by
    have := one_lt_pow' (show 1 < (2 : ℕ) by omega) (Nat.ne_of_gt hp.keyBits_pos)
    omega
  have hqbound : 2 * p.blockWidth ≤ p.q := by
    rw [hq]
    exact Nat.mul_le_mul_right p.blockWidth hkey
  have hrq : r < p.q := by omega
  by_cases hz : z = 0
  · subst z
    have hempty :
        (Finset.range p.halfWidth).filter (fun u =>
          p.blockWidth ≤
            ((((u + r : ℕ) : Scalar p) - 0).val)) = ∅ := by
      apply Finset.filter_eq_empty_iff.2
      intro u hu
      simp only [Finset.mem_range] at hu
      simp only [not_le, sub_zero]
      have hlt : u + r < p.q := by omega
      rw [ZMod.val_natCast_of_lt hlt]
      omega
    change ((Finset.range p.halfWidth).filter (fun u =>
      p.blockWidth ≤ ((((u + r : ℕ) : Scalar p) - 0).val))).card = _
    rw [hempty, Finset.card_empty]
    simp [modularDistance]
  · have hnegval : (-z).val = p.q - z.val := by
      rw [ZMod.neg_val, if_neg hz]
    by_cases hcenter : z.val ≤ p.q - z.val
    · have hdist : modularDistance p z 0 = z.val := by
        simp only [modularDistance, sub_zero, zero_sub, hnegval]
        exact min_eq_left hcenter
      have hfilter :
          (Finset.range p.halfWidth).filter (fun u =>
            p.blockWidth ≤
              ((((u + r : ℕ) : Scalar p) - z).val)) =
            (Finset.Ico 0 p.halfWidth).filter (fun u => u < z.val - r) := by
        rw [Finset.range_eq_Ico]
        apply Finset.filter_congr
        intro u hu
        simp only [Finset.mem_Ico] at hu
        have hcastlt : u + r < p.q := by omega
        have hcastval : (((u + r : ℕ) : Scalar p)).val = u + r :=
          ZMod.val_natCast_of_lt hcastlt
        by_cases hle : z.val ≤ u + r
        · have hvalorder : z.val ≤ (((u + r : ℕ) : Scalar p)).val := by
            rw [ZMod.val_natCast_of_lt hcastlt]
            exact hle
          rw [ZMod.val_sub hvalorder, ZMod.val_natCast_of_lt hcastlt]
          omega
        · have hlt : u + r < z.val := by omega
          have hdiffval :
              (z - ((u + r : ℕ) : Scalar p)).val = z.val - (u + r) := by
            have hvalorder : (((u + r : ℕ) : Scalar p)).val ≤ z.val := by
              rw [ZMod.val_natCast_of_lt hcastlt]
              exact Nat.le_of_lt hlt
            rw [ZMod.val_sub hvalorder, ZMod.val_natCast_of_lt hcastlt]
          have hdiffne : z - ((u + r : ℕ) : Scalar p) ≠ 0 := by
            intro heq
            have := congrArg ZMod.val heq
            rw [hdiffval, ZMod.val_zero] at this
            omega
          rw [show ((u + r : ℕ) : Scalar p) - z =
              -(z - ((u + r : ℕ) : Scalar p)) by ring,
            ZMod.neg_val, if_neg hdiffne, hdiffval]
          omega
      change ((Finset.range p.halfWidth).filter (fun u =>
        p.blockWidth ≤ ((((u + r : ℕ) : Scalar p) - z).val))).card = _
      rw [hfilter, Finset.Ico_filter_lt, Nat.card_Ico, hdist]
      simp only [Nat.sub_zero]
      rfl
    · let d := p.q - z.val
      have hdpos : 0 < d := by
        have hzlt : z.val < p.q := ZMod.val_lt z
        simp only [d]
        omega
      have hdcenter : d < z.val := by simpa [d] using lt_of_not_ge hcenter
      have htwod : 2 * d < p.q := by
        have hzlt : z.val < p.q := ZMod.val_lt z
        simp only [d] at hdcenter ⊢
        omega
      have hdist : modularDistance p z 0 = d := by
        simp only [modularDistance, sub_zero, zero_sub, hnegval, d]
        exact min_eq_right (Nat.le_of_lt hdcenter)
      have hfilter :
          (Finset.range p.halfWidth).filter (fun u =>
            p.blockWidth ≤
              ((((u + r : ℕ) : Scalar p) - z).val)) =
            (Finset.Ico 0 p.halfWidth).filter (fun u => 3 * r - d ≤ u) := by
        rw [Finset.range_eq_Ico]
        apply Finset.filter_congr
        intro u hu
        simp only [Finset.mem_Ico] at hu
        have hcastlt : u + r < p.q := by omega
        have hsumlt : u + r + d < p.q := by omega
        have hminus : -z = ((d : ℕ) : Scalar p) := by
          rw [← ZMod.natCast_zmod_val (-z), hnegval]
        have hexpr :
            ((u + r : ℕ) : Scalar p) - z = ((u + r + d : ℕ) : Scalar p) := by
          rw [sub_eq_add_neg, hminus, ← Nat.cast_add]
        rw [hexpr, ZMod.val_natCast_of_lt hsumlt]
        omega
      change ((Finset.range p.halfWidth).filter (fun u =>
        p.blockWidth ≤ ((((u + r : ℕ) : Scalar p) - z).val))).card = _
      rw [hfilter, Finset.Ico_filter_le, Nat.card_Ico, hdist]
      simp only [Nat.max_eq_right (Nat.zero_le _)]
      omega

end lweCKA
