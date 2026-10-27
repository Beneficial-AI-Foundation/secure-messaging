/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.ReconciliationCorrectness

/-!
# Exact phase geometry for Frodo reconciliation

This file gives closed forms for scalar reconciliation and counts the sender phases on which
reconciliation fails for a fixed modular difference.
-/

namespace lweCKA

private theorem discardBits_two_le (p : Params) (hp : p.WellFormed) :
    2 ≤ p.discardBits := by
  have h := hp.keyBits_lt
  simp only [Params.discardBits]
  omega

theorem ReconciliationPhase.Internal.halfWidth_eq_two_mul_radius (p : Params) (hp : p.WellFormed) :
    p.halfWidth = 2 * 2 ^ (p.discardBits - 2) := by
  have hd := discardBits_two_le p hp
  rw [Params.halfWidth, show p.discardBits - 1 = (p.discardBits - 2) + 1 by omega,
    pow_succ, Nat.mul_comm]

open ReconciliationPhase.Internal

theorem
    ReconciliationPhase.Internal.blockWidth_eq_two_mul_halfWidth
    (p : Params) (hp : p.WellFormed) :
    p.blockWidth = 2 * p.halfWidth := by
  have hd := discardBits_two_le p hp
  change 2 ^ p.discardBits = 2 * 2 ^ (p.discardBits - 1)
  calc
    2 ^ p.discardBits = 2 ^ ((p.discardBits - 1) + 1) := by congr 1; omega
    _ = 2 ^ (p.discardBits - 1) * 2 := pow_succ _ _
    _ = 2 * 2 ^ (p.discardBits - 1) := Nat.mul_comm _ _

theorem ReconciliationPhase.Internal.q_eq_keySpace_mul_blockWidth (p : Params) (hp : p.WellFormed) :
    p.q = 2 ^ p.keyBits * p.blockWidth := by
  have h := hp.keyBits_lt
  have hk : p.keyBits ≤ p.logQ := by omega
  rw [Params.q, Params.blockWidth, Params.discardBits, ← pow_add]
  congr 1
  omega

private theorem q_eq_halfBlocks_mul_halfWidth (p : Params) (hp : p.WellFormed) :
    p.q = 2 ^ (p.keyBits + 1) * p.halfWidth := by
  rw [q_eq_keySpace_mul_blockWidth p hp, blockWidth_eq_two_mul_halfWidth p hp,
    pow_succ]
  ac_rfl

theorem ReconciliationPhase.Internal.roundedBlock_eq_halfIndex
    (p : Params) (hp : p.WellFormed) (x : ℕ) :
    (x + p.halfWidth) / p.blockWidth = (x / p.halfWidth + 1) / 2 := by
  have hhalf : 0 < p.halfWidth := by simp [Params.halfWidth]
  rw [blockWidth_eq_two_mul_halfWidth p hp, Nat.mul_comm 2 p.halfWidth,
    ← Nat.div_div_eq_div_mul]
  congr 1
  simpa using Nat.add_mul_div_left x 1 hhalf

private theorem modularDistance_radius_shifts
    (p : Params) (hp : p.WellFormed) (w : Scalar p) :
    modularDistance p w
        (w - ((2 ^ (p.discardBits - 2) : ℕ) : Scalar p)) =
      2 ^ (p.discardBits - 2) ∧
    modularDistance p w
        (w + ((2 ^ (p.discardBits - 2) : ℕ) : Scalar p)) =
      2 ^ (p.discardBits - 2) := by
  let r := 2 ^ (p.discardBits - 2)
  have hrpos : 0 < r := by simp [r]
  have hkey : 2 ≤ 2 ^ p.keyBits := by
    have := one_lt_pow' (show 1 < (2 : ℕ) by omega) (Nat.ne_of_gt hp.keyBits_pos)
    omega
  have hq := q_eq_keySpace_mul_blockWidth p hp
  have hhalf := halfWidth_eq_two_mul_radius p hp
  have hblock := blockWidth_eq_two_mul_halfWidth p hp
  have hqbound : 2 * p.blockWidth ≤ p.q := by
    rw [hq]
    exact Nat.mul_le_mul_right p.blockWidth hkey
  have hrq : r < p.q := by omega
  have htwo : 2 * r ≤ p.q := by omega
  have hrval : ((r : ℕ) : Scalar p).val = r := ZMod.val_natCast_of_lt hrq
  have hrne : ((r : ℕ) : Scalar p) ≠ 0 := by
    intro h
    have := congrArg ZMod.val h
    simp only [hrval, ZMod.val_zero] at this
    omega
  constructor
  · rw [modularDistance]
    have hforward : w - (w - (r : Scalar p)) = (r : Scalar p) := by ring
    have hbackward : w - (r : Scalar p) - w = -(r : Scalar p) := by ring
    rw [hforward, hbackward, hrval, ZMod.neg_val, ite_eq_right hrne]
    omega
  · rw [modularDistance]
    have hforward : w - (w + (r : Scalar p)) = -(r : Scalar p) := by ring
    have hbackward : w + (r : Scalar p) - w = (r : Scalar p) := by ring
    rw [hforward, hbackward, hrval, ZMod.neg_val, ite_eq_right hrne]
    omega

private theorem hintScalar_add_halfWidth
    (p : Params) (hp : p.WellFormed) (x : Scalar p) :
    hintScalar p (x + ((p.halfWidth : ℕ) : Scalar p)) = hintScalar p x + 1 := by
  let blocks := 2 ^ (p.keyBits + 1)
  have hhalf : 0 < p.halfWidth := by simp [Params.halfWidth]
  have hblocks : 0 < blocks := by simp [blocks]
  have hblockseven : blocks % 2 = 0 := by simp [blocks, pow_succ]
  have hq : p.q = blocks * p.halfWidth := by
    simpa [blocks] using q_eq_halfBlocks_mul_halfWidth p hp
  have hhalflt : p.halfWidth < p.q := by
    have hkey : 2 ≤ blocks := by
      have := one_lt_pow' (show 1 < (2 : ℕ) by omega)
        (show p.keyBits + 1 ≠ 0 by omega)
      omega
    nlinarith
  have hhalfval : (((p.halfWidth : ℕ) : Scalar p)).val = p.halfWidth :=
    ZMod.val_natCast_of_lt hhalflt
  apply ZMod.val_injective
  simp only [hintScalar, ZMod.val_natCast, ZMod.val_add, hhalfval]
  by_cases hnowrap : x.val + p.halfWidth < p.q
  · have hdivadd :
        (x.val + p.halfWidth) / p.halfWidth = x.val / p.halfWidth + 1 := by
      simpa using Nat.add_mul_div_left x.val 1 hhalf
    rw [Nat.mod_eq_of_lt hnowrap, hdivadd]
    rw [ZMod.val_one]
    exact Nat.add_mod (x.val / p.halfWidth) 1 2
  · have hxlt : x.val < p.q := ZMod.val_lt x
    have hxdivlt : x.val / p.halfWidth < blocks := by
      apply (Nat.div_lt_iff_lt_mul hhalf).2
      omega
    have hmul :
        (blocks - 1) * p.halfWidth + p.halfWidth = blocks * p.halfWidth := by
      calc
        (blocks - 1) * p.halfWidth + p.halfWidth =
            (blocks - 1) * p.halfWidth + 1 * p.halfWidth := by simp
        _ = ((blocks - 1) + 1) * p.halfWidth := by rw [Nat.add_mul]
        _ = blocks * p.halfWidth := by rw [Nat.sub_add_cancel hblocks]
    have hxlower : (blocks - 1) * p.halfWidth ≤ x.val := by
      omega
    have hxupper : x.val < ((blocks - 1) + 1) * p.halfWidth := by
      rw [Nat.sub_add_cancel hblocks]
      simpa [← hq] using hxlt
    have hxdiv : x.val / p.halfWidth = blocks - 1 :=
      Nat.div_eq_of_lt_le hxlower hxupper
    have hsumlt : x.val + p.halfWidth < 2 * p.q := by omega
    have hmod : (x.val + p.halfWidth) % p.q = x.val + p.halfWidth - p.q := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hmod, hxdiv]
    have hsmall : x.val + p.halfWidth - p.q < p.halfWidth := by omega
    rw [Nat.div_eq_of_lt hsmall]
    have hprevmod : (blocks - 1) % 2 = 1 := by omega
    simp only [Nat.zero_mod, hprevmod, ZMod.val_one]

private theorem radius_shifts_cover_hint
    (p : Params) (hp : p.WellFormed) (w : Scalar p) (b : HintScalar) :
    hintScalar p (w - ((2 ^ (p.discardBits - 2) : ℕ) : Scalar p)) = b ∨
      hintScalar p (w + ((2 ^ (p.discardBits - 2) : ℕ) : Scalar p)) = b := by
  let r : Scalar p := (2 ^ (p.discardBits - 2) : ℕ)
  have hhalf := halfWidth_eq_two_mul_radius p hp
  have hcast : ((p.halfWidth : ℕ) : Scalar p) = 2 * r := by
    simp only [r]
    rw [hhalf]
    norm_num
  have hshift : w - r + ((p.halfWidth : ℕ) : Scalar p) = w + r := by
    rw [hcast]
    ring
  have hflip := hintScalar_add_halfWidth p hp (w - r)
  rw [hshift] at hflip
  by_cases h : hintScalar p (w - r) = b
  · exact Or.inl h
  · right
    rw [hflip]
    apply ZMod.val_injective
    have ha := ZMod.val_lt (hintScalar p (w - r))
    have hb := ZMod.val_lt b
    have hne : (hintScalar p (w - r)).val ≠ b.val := by
      intro heq
      apply h
      apply ZMod.val_injective
      exact heq
    simp only [ZMod.val_add, ZMod.val_one]
    omega

theorem ReconciliationPhase.Internal.extractScalar_eq_natCast_iff_centered
    (p : Params) (hp : p.WellFormed) (x : Scalar p) (k : ℕ)
    (hk : k < 2 ^ p.keyBits) :
    extractScalar p x = (k : KeyScalar p) ↔
      (x + ((p.halfWidth : ℕ) : Scalar p) -
          ((k * p.blockWidth : ℕ) : Scalar p)).val < p.blockWidth := by
  let keySpace := 2 ^ p.keyBits
  let a := x.val + p.halfWidth
  let c := k * p.blockWidth
  have hhalf : 0 < p.halfWidth := by simp [Params.halfWidth]
  have hwidth : 0 < p.blockWidth := by simp [Params.blockWidth]
  have hkey : 0 < keySpace := by simp [keySpace]
  have hq : p.q = keySpace * p.blockWidth := by
    simpa [keySpace] using q_eq_keySpace_mul_blockWidth p hp
  have hhalfwidth := blockWidth_eq_two_mul_halfWidth p hp
  have hxlt : x.val < p.q := ZMod.val_lt x
  have hhalflt : p.halfWidth < p.blockWidth := by omega
  have hwidthleq : p.blockWidth ≤ p.q := by
    rw [hq]
    exact Nat.le_mul_of_pos_left p.blockWidth hkey
  have halt : a < p.q + p.blockWidth := by omega
  have hclt : c < p.q := by
    rw [hq]
    exact Nat.mul_lt_mul_of_pos_right (by simpa [c, keySpace] using hk) hwidth
  have hcval : ((c : ℕ) : Scalar p).val = c := ZMod.val_natCast_of_lt hclt
  have hexpr :
      x + ((p.halfWidth : ℕ) : Scalar p) -
          ((k * p.blockWidth : ℕ) : Scalar p) =
        ((a : ℕ) : Scalar p) - ((c : ℕ) : Scalar p) := by
    calc
      x + ((p.halfWidth : ℕ) : Scalar p) -
          ((k * p.blockWidth : ℕ) : Scalar p) =
          ((x.val : ℕ) : Scalar p) + ((p.halfWidth : ℕ) : Scalar p) -
            ((k * p.blockWidth : ℕ) : Scalar p) := by
              rw [ZMod.natCast_zmod_val]
      _ = ((a : ℕ) : Scalar p) - ((c : ℕ) : Scalar p) := by
        simp only [a, c, Nat.cast_add]
  change ((a / p.blockWidth : ℕ) : KeyScalar p) = (k : KeyScalar p) ↔ _
  rw [ZMod.natCast_eq_natCast_iff']
  change a / p.blockWidth % keySpace = k % keySpace ↔ _
  have hk' : k < keySpace := by simpa [keySpace] using hk
  conv => lhs; rhs; rw [Nat.mod_eq_of_lt hk']
  rw [hexpr]
  by_cases ha : a < p.q
  · have hadiv : a / p.blockWidth < keySpace := by
      apply (Nat.div_lt_iff_lt_mul hwidth).2
      omega
    rw [Nat.mod_eq_of_lt hadiv]
    by_cases hca : c ≤ a
    · have hvalorder : ((c : ℕ) : Scalar p).val ≤ ((a : ℕ) : Scalar p).val := by
        simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hclt, Nat.mod_eq_of_lt ha]
          using hca
      rw [ZMod.val_sub hvalorder]
      rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha,
        Nat.mod_eq_of_lt hclt]
      have hnext : c + p.blockWidth = (k + 1) * p.blockWidth := by
        simp only [c, Nat.add_mul, one_mul]
      constructor
      · intro hdiv
        have hlo := Nat.mul_div_le a p.blockWidth
        have hhi := Nat.lt_mul_of_div_lt (show a / p.blockWidth < k + 1 by omega) hwidth
        rw [hdiv] at hlo
        omega
      · intro hsub
        exact Nat.div_eq_of_lt_le hca (by
          have : a < (k + 1) * p.blockWidth := by omega
          exact this)
    · have hac : a < c := by omega
      have hdiffval :
          (((c : ℕ) : Scalar p) - ((a : ℕ) : Scalar p)).val = c - a := by
        have hvalorder : ((a : ℕ) : Scalar p).val ≤ ((c : ℕ) : Scalar p).val := by
          simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hclt, Nat.mod_eq_of_lt ha]
            using Nat.le_of_lt hac
        rw [ZMod.val_sub hvalorder]
        rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hclt,
          Nat.mod_eq_of_lt ha]
      have hdiffne : ((c : ℕ) : Scalar p) - ((a : ℕ) : Scalar p) ≠ 0 := by
        intro hzero
        have := congrArg ZMod.val hzero
        rw [hdiffval, ZMod.val_zero] at this
        omega
      have hval :
          (((a : ℕ) : Scalar p) - ((c : ℕ) : Scalar p)).val = p.q - (c - a) := by
        rw [show ((a : ℕ) : Scalar p) - ((c : ℕ) : Scalar p) =
            -(((c : ℕ) : Scalar p) - ((a : ℕ) : Scalar p)) by ring,
          ZMod.neg_val, ite_eq_right hdiffne, hdiffval]
      rw [hval]
      have hnext : c + p.blockWidth = (k + 1) * p.blockWidth := by
        simp only [c, Nat.add_mul, one_mul]
      have hkstep : (k + 1) * p.blockWidth ≤ p.q := by
        have : k + 1 ≤ keySpace := by simpa [keySpace] using hk
        calc
          (k + 1) * p.blockWidth ≤ keySpace * p.blockWidth :=
            Nat.mul_le_mul_right p.blockWidth this
          _ = p.q := hq.symm
      constructor <;> intro h
      · have hdivlt : a / p.blockWidth < k :=
          (Nat.div_lt_iff_lt_mul hwidth).2 (by simpa [c] using hac)
        omega
      · omega
  · have hqa : p.q ≤ a := by omega
    have hadiv : a / p.blockWidth = keySpace := by
      apply Nat.div_eq_of_lt_le
      · rw [← hq]
        exact hqa
      · rw [Nat.add_mul]
        omega
    rw [hadiv, Nat.mod_self]
    have hamod : a % p.q = a - p.q := by
      rw [Nat.mod_eq_sub_mod hqa, Nat.mod_eq_of_lt (by omega)]
    have haval : ((a : ℕ) : Scalar p).val = a - p.q := by
      rw [ZMod.val_natCast, hamod]
    by_cases hkzero : k = 0
    · subst k
      simp only [c, Nat.zero_mul, Nat.cast_zero, sub_zero]
      rw [ZMod.val_natCast, hamod]
      constructor
      · intro
        omega
      · intro
        trivial
    · have hapos : a - p.q < c := by
        have hkone : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hkzero
        have : p.blockWidth ≤ c := by
          simpa [c, one_mul] using Nat.mul_le_mul_right p.blockWidth hkone
        omega
      have hdiffval :
          (((c : ℕ) : Scalar p) - ((a : ℕ) : Scalar p)).val =
            c - (a - p.q) := by
        have hvalorder : ((a : ℕ) : Scalar p).val ≤ ((c : ℕ) : Scalar p).val := by
          rw [haval, hcval]
          exact Nat.le_of_lt hapos
        rw [ZMod.val_sub hvalorder, ZMod.val_natCast, ZMod.val_natCast,
          Nat.mod_eq_of_lt hclt, hamod]
      have hdiffne : ((c : ℕ) : Scalar p) - ((a : ℕ) : Scalar p) ≠ 0 := by
        intro hzero
        have := congrArg ZMod.val hzero
        rw [hdiffval, ZMod.val_zero] at this
        omega
      rw [show ((a : ℕ) : Scalar p) - ((c : ℕ) : Scalar p) =
          -(((c : ℕ) : Scalar p) - ((a : ℕ) : Scalar p)) by ring,
        ZMod.neg_val, ite_eq_right hdiffne, hdiffval]
      have hnext : c + p.blockWidth = (k + 1) * p.blockWidth := by
        simp only [c, Nat.add_mul, one_mul]
      have hkstep : (k + 1) * p.blockWidth ≤ p.q := by
        have : k + 1 ≤ keySpace := by simpa [keySpace] using hk
        calc
          (k + 1) * p.blockWidth ≤ keySpace * p.blockWidth :=
            Nat.mul_le_mul_right p.blockWidth this
          _ = p.q := hq.symm
      constructor <;> intro h <;> omega

private theorem phaseOffset_sub_difference_lt
    (p : Params) (hp : p.WellFormed) (w u : Scalar p) (t : ℕ)
    (ht : t < p.halfWidth)
    (hnear : modularDistance p w u ≤ 2 ^ (p.discardBits - 2)) :
    ((((t + 2 ^ (p.discardBits - 2) : ℕ) : Scalar p) - (u - w)).val <
      p.blockWidth) := by
  let r := 2 ^ (p.discardBits - 2)
  let e := t + r
  have hrpos : 0 < r := by simp [r]
  have hhalf := halfWidth_eq_two_mul_radius p hp
  have hwidth := blockWidth_eq_two_mul_halfWidth p hp
  have hq := q_eq_keySpace_mul_blockWidth p hp
  have hkey : 0 < 2 ^ p.keyBits := by simp
  have hewidth : e < p.blockWidth := by omega
  have hwidthq : p.blockWidth ≤ p.q := by
    rw [hq]
    exact Nat.le_mul_of_pos_left p.blockWidth hkey
  have heq : e < p.q := lt_of_lt_of_le hewidth hwidthq
  have heval : ((e : ℕ) : Scalar p).val = e := ZMod.val_natCast_of_lt heq
  change (((e : ℕ) : Scalar p) - (u - w)).val < p.blockWidth
  unfold modularDistance at hnear
  rw [min_le_iff] at hnear
  rcases hnear with hforward | hbackward
  · let d := (w - u).val
    have hd : d ≤ r := by simpa [d, r] using hforward
    have hsumwidth : e + d < p.blockWidth := by omega
    have hsumq : e + d < p.q := lt_of_lt_of_le hsumwidth hwidthq
    have hexpr :
        ((e : ℕ) : Scalar p) - (u - w) = ((e + d : ℕ) : Scalar p) := by
      rw [show u - w = -(w - u) by ring, ← ZMod.natCast_zmod_val (w - u)]
      simp only [d, Nat.cast_add]
      ring
    change (((e : ℕ) : Scalar p) - (u - w)).val < p.blockWidth
    rw [hexpr, ZMod.val_natCast_of_lt hsumq]
    exact hsumwidth
  · let d := (u - w).val
    have hd : d ≤ r := by simpa [d, r] using hbackward
    have hde : d ≤ e := by omega
    have hsubwidth : e - d < p.blockWidth := by omega
    have hsubq : e - d < p.q := lt_of_lt_of_le hsubwidth hwidthq
    have hexpr :
        ((e : ℕ) : Scalar p) - (u - w) = ((e - d : ℕ) : Scalar p) := by
      rw [Nat.cast_sub hde, ZMod.natCast_zmod_val (u - w)]
    change (((e : ℕ) : Scalar p) - (u - w)).val < p.blockWidth
    rw [hexpr, ZMod.val_natCast_of_lt hsubq]
    exact hsubwidth

private theorem extractScalar_sub_radius_of_hint_zero_of_distance_le
    (p : Params) (hp : p.WellFormed) (w u : Scalar p)
    (hhint : hintScalar p u = 0)
    (hnear : modularDistance p w u ≤ 2 ^ (p.discardBits - 2)) :
    extractScalar p u =
      extractScalar p (w - ((2 ^ (p.discardBits - 2) : ℕ) : Scalar p)) := by
  let r := 2 ^ (p.discardBits - 2)
  let m := u.val / p.halfWidth
  let t := u.val % p.halfWidth
  let keySpace := 2 ^ p.keyBits
  have hhalfpos : 0 < p.halfWidth := by simp [Params.halfWidth]
  have hwidthpos : 0 < p.blockWidth := by simp [Params.blockWidth]
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
    have hult : u.val < p.q := ZMod.val_lt u
    have hfactor : keySpace * p.blockWidth = 2 * keySpace * p.halfWidth := by
      rw [hwidth]
      ring
    omega
  have hkkey : k < keySpace := by
    rw [hk] at hmlt
    omega
  have ht : t < p.halfWidth := Nat.mod_lt _ hhalfpos
  have hcenter : u.val = k * p.blockWidth + t := by
    calc
      u.val = t + p.halfWidth * m := (Nat.mod_add_div u.val p.halfWidth).symm
      _ = k * p.blockWidth + t := by rw [hk, hwidth]; ring
  have hround : (u.val + p.halfWidth) / p.blockWidth = k := by
    rw [roundedBlock_eq_halfIndex p hp, show u.val / p.halfWidth = m by rfl, hk]
    omega
  have hExtract : extractScalar p u = (k : KeyScalar p) := by
    simp only [extractScalar, hround]
  rw [hExtract]
  symm
  apply (extractScalar_eq_natCast_iff_centered p hp _ k (by simpa [keySpace] using hkkey)).2
  have hcenterCast :
      ((k * p.blockWidth : ℕ) : Scalar p) + ((t : ℕ) : Scalar p) = u := by
    rw [← Nat.cast_add, ← hcenter, ZMod.natCast_zmod_val]
  have hhalfCast : ((p.halfWidth : ℕ) : Scalar p) = 2 * (r : Scalar p) := by
    simp only [r]
    rw [hhalf]
    norm_num
  have hexpr :
      w - (r : Scalar p) + ((p.halfWidth : ℕ) : Scalar p) -
          ((k * p.blockWidth : ℕ) : Scalar p) =
        ((t + r : ℕ) : Scalar p) - (u - w) := by
    rw [hhalfCast, Nat.cast_add]
    rw [← hcenterCast]
    ring
  rw [hexpr]
  exact phaseOffset_sub_difference_lt p hp w u t ht (by simpa [r] using hnear)

private theorem extractScalar_add_radius_of_hint_one_of_distance_le
    (p : Params) (hp : p.WellFormed) (w u : Scalar p)
    (hhint : hintScalar p u = 1)
    (hnear : modularDistance p w u ≤ 2 ^ (p.discardBits - 2)) :
    extractScalar p u =
      extractScalar p (w + ((2 ^ (p.discardBits - 2) : ℕ) : Scalar p)) := by
  let r := 2 ^ (p.discardBits - 2)
  let m := u.val / p.halfWidth
  let t := u.val % p.halfWidth
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
    have hult : u.val < p.q := ZMod.val_lt u
    have hfactor : keySpace * p.blockWidth = 2 * keySpace * p.halfWidth := by
      rw [hwidth]
      ring
    omega
  have hkkey : k < keySpace := by omega
  have hksucc : k + 1 ≤ keySpace := by omega
  have ht : t < p.halfWidth := Nat.mod_lt _ hhalfpos
  have hcenter : u.val = p.halfWidth * m + t := by
    calc
      u.val = t + p.halfWidth * m := (Nat.mod_add_div u.val p.halfWidth).symm
      _ = p.halfWidth * m + t := Nat.add_comm _ _
  have hround : (u.val + p.halfWidth) / p.blockWidth = k + 1 := by
    rw [roundedBlock_eq_halfIndex p hp, show u.val / p.halfWidth = m by rfl, hm]
    omega
  have hExtract : extractScalar p u = ((k + 1 : ℕ) : KeyScalar p) := by
    simp only [extractScalar, hround]
  rw [hExtract]
  symm
  change extractScalar p (w + (r : Scalar p)) = ((k + 1 : ℕ) : KeyScalar p)
  have hcenterCast :
      ((p.halfWidth * m : ℕ) : Scalar p) + ((t : ℕ) : Scalar p) = u := by
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
        ((t + r : ℕ) : Scalar p) - (u - w) := by
    rw [Nat.cast_add, Nat.cast_mul, hwidthCast, hhalfCast]
    rw [hm] at hcenterCast
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at hcenterCast
    rw [← hcenterCast]
    rw [hhalfCast]
    push_cast
    ring
  by_cases hlast : k + 1 = keySpace
  · have hkeycast : (((k + 1 : ℕ) : KeyScalar p)) = 0 := by
      rw [hlast]
      exact ZMod.natCast_self keySpace
    have htarget0 :
        extractScalar p (w + (r : Scalar p)) = ((0 : ℕ) : KeyScalar p) := by
      apply (extractScalar_eq_natCast_iff_centered p hp (w + (r : Scalar p)) 0
        hkeypos).2
      simp only [Nat.zero_mul, Nat.cast_zero, sub_zero]
      have hcenterzero :
          ((((k + 1) * p.blockWidth : ℕ) : Scalar p)) = 0 := by
        rw [hlast, ← hq]
        exact ZMod.natCast_self p.q
      have hsame :
          w + (r : Scalar p) + ((p.halfWidth : ℕ) : Scalar p) =
            w + (r : Scalar p) + ((p.halfWidth : ℕ) : Scalar p) -
              (((k + 1) * p.blockWidth : ℕ) : Scalar p) := by
        rw [hcenterzero, sub_zero]
      rw [hsame, hexpr]
      exact phaseOffset_sub_difference_lt p hp w u t ht (by simpa [r] using hnear)
    exact htarget0.trans (by simpa only [Nat.cast_zero] using hkeycast.symm)
  · have hlt : k + 1 < keySpace := by omega
    apply (extractScalar_eq_natCast_iff_centered p hp _ (k + 1)
      (by simpa [keySpace] using hlt)).2
    rw [hexpr]
    exact phaseOffset_sub_difference_lt p hp w u t ht (by simpa [r] using hnear)

/-- Recovery with the zero hint is extraction after the negative quarter-block shift. -/
theorem reconcileScalar_zero_eq_extractScalar_sub_radius
    (p : Params) (hp : p.WellFormed) (w : Scalar p) :
    reconcileScalar p w 0 =
      extractScalar p (w - ((2 ^ (p.discardBits - 2) : ℕ) : Scalar p)) := by
  let u := nearestWithHint p w 0
  have hspec := nearestWithHint_spec p hp w 0
  have hdist := modularDistance_radius_shifts p hp w
  have hnear : modularDistance p w u ≤ 2 ^ (p.discardBits - 2) := by
    rcases radius_shifts_cover_hint p hp w 0 with hsub | hadd
    · exact (hspec.2 _ hsub).trans_eq hdist.1
    · exact (hspec.2 _ hadd).trans_eq hdist.2
  unfold reconcileScalar
  exact extractScalar_sub_radius_of_hint_zero_of_distance_le p hp w u hspec.1 hnear

/-- Recovery with the one hint is extraction after the positive quarter-block shift. -/
theorem reconcileScalar_one_eq_extractScalar_add_radius
    (p : Params) (hp : p.WellFormed) (w : Scalar p) :
    reconcileScalar p w 1 =
      extractScalar p (w + ((2 ^ (p.discardBits - 2) : ℕ) : Scalar p)) := by
  let u := nearestWithHint p w 1
  have hspec := nearestWithHint_spec p hp w 1
  have hdist := modularDistance_radius_shifts p hp w
  have hnear : modularDistance p w u ≤ 2 ^ (p.discardBits - 2) := by
    rcases radius_shifts_cover_hint p hp w 1 with hsub | hadd
    · exact (hspec.2 _ hsub).trans_eq hdist.1
    · exact (hspec.2 _ hadd).trans_eq hdist.2
  unfold reconcileScalar
  exact extractScalar_add_radius_of_hint_one_of_distance_le p hp w u hspec.1 hnear

end lweCKA
