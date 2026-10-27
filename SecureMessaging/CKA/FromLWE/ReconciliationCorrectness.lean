/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.CKA.FromLWE.Reconciliation
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.ZMod.ValMinAbs

/-!
# Correctness of Frodo reconciliation

The executable search returns a closest residue with the requested hint. Residues within the
strict reconciliation radius therefore extract the same shared-key bits.
-/

@[expose] public section

namespace lweCKA

/-- Circular distance from an integer residue to zero is at most its integer magnitude. -/
theorem modularDistance_intCast_zero_le_natAbs
    (p : Params) (z : ℤ) :
    modularDistance p (z : Scalar p) 0 ≤ z.natAbs := by
  cases z with
  | ofNat n =>
      unfold modularDistance
      simp only [Int.ofNat_eq_natCast, Int.cast_natCast, Int.natAbs_natCast, sub_zero]
      exact le_trans (min_le_left _ _) (by
        rw [ZMod.val_natCast]
        exact Nat.mod_le _ _)
  | negSucc n =>
      unfold modularDistance
      simp only [Int.cast_negSucc, Int.natAbs_negSucc, sub_zero, zero_sub, neg_neg]
      exact le_trans (min_le_right _ _) (by
        rw [ZMod.val_natCast]
        exact Nat.mod_le _ _)


private theorem discardBits_two_le (p : Params) (hp : p.WellFormed) :
    2 ≤ p.discardBits := by
  have h := hp.keyBits_lt
  simp only [Params.discardBits]
  omega

private theorem halfWidth_two_mul_radius (p : Params) (hp : p.WellFormed) :
    p.halfWidth = 2 * 2 ^ (p.discardBits - 2) := by
  have hd := discardBits_two_le p hp
  rw [Params.halfWidth, show p.discardBits - 1 = (p.discardBits - 2) + 1 by omega,
    pow_succ, Nat.mul_comm]

private theorem blockWidth_eq_two_mul_halfWidth (p : Params) (hp : p.WellFormed) :
    p.blockWidth = 2 * p.halfWidth := by
  have hd := discardBits_two_le p hp
  change 2 ^ p.discardBits = 2 * 2 ^ (p.discardBits - 1)
  calc
    2 ^ p.discardBits = 2 ^ ((p.discardBits - 1) + 1) := by congr 1; omega
    _ = 2 ^ (p.discardBits - 1) * 2 := pow_succ _ _
    _ = 2 * 2 ^ (p.discardBits - 1) := Nat.mul_comm _ _

private theorem q_eq_keySpace_mul_blockWidth (p : Params) (hp : p.WellFormed) :
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

private theorem initialHint (p : Params) (hp : p.WellFormed) (b : HintScalar) :
    hintScalar p ((b.val * p.halfWidth : ℕ) : Scalar p) = b := by
  have hb : b.val < 2 := ZMod.val_lt b
  have hkey : 2 ≤ 2 ^ p.keyBits := by
    have := one_lt_pow' (show 1 < (2 : ℕ) by omega) (Nat.ne_of_gt hp.keyBits_pos)
    omega
  have hhalf : 0 < p.halfWidth := by simp [Params.halfWidth]
  have hblock := blockWidth_eq_two_mul_halfWidth p hp
  have hq := q_eq_keySpace_mul_blockWidth p hp
  have hlt : b.val * p.halfWidth < p.q := by
    nlinarith
  rw [hintScalar, ZMod.val_natCast_of_lt hlt, Nat.mul_div_left _ hhalf]
  exact ZMod.natCast_zmod_val b

private def nearestStep
    (p : Params) (w : Scalar p) (b : HintScalar)
    (best candidate : Scalar p) : Scalar p :=
  if hintScalar p candidate = b ∧
      (modularDistance p w candidate < modularDistance p w best ∨
        (modularDistance p w candidate = modularDistance p w best ∧
          candidate.val < best.val)) then
    candidate
  else
    best

private theorem nearestFold_spec
    (p : Params) (w : Scalar p) (b : HintScalar)
    (l : List (Scalar p)) (best : Scalar p) (hbest : hintScalar p best = b) :
    let result := l.foldl (nearestStep p w b) best
    hintScalar p result = b ∧
      modularDistance p w result ≤ modularDistance p w best ∧
      ∀ candidate ∈ l, hintScalar p candidate = b →
        modularDistance p w result ≤ modularDistance p w candidate := by
  induction l generalizing best with
  | nil => simp [hbest]
  | cons candidate l ih =>
      by_cases hchoose : hintScalar p candidate = b ∧
          (modularDistance p w candidate < modularDistance p w best ∨
            (modularDistance p w candidate = modularDistance p w best ∧
              candidate.val < best.val))
      · have hrec := ih candidate hchoose.1
        simp only [List.foldl_cons]
        rw [nearestStep, ite_eq_left hchoose]
        refine ⟨hrec.1, ?_, ?_⟩
        · exact le_trans hrec.2.1 (by omega)
        · intro x hx hhint
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hrec.2.1
          · exact hrec.2.2 x hx hhint
      · have hrec := ih best hbest
        simp only [List.foldl_cons]
        rw [nearestStep, ite_eq_right hchoose]
        refine ⟨hrec.1, hrec.2.1, ?_⟩
        intro x hx hhint
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact le_trans hrec.2.1 (Nat.le_of_not_gt fun hlt => hchoose ⟨hhint, Or.inl hlt⟩)
        · exact hrec.2.2 x hx hhint

/-- The executable search returns a closest residue with the requested hint. -/
theorem nearestWithHint_spec
    (p : Params) (hp : p.WellFormed)
    (w : Scalar p) (b : HintScalar) :
    hintScalar p (nearestWithHint p w b) = b ∧
      ∀ v : Scalar p, hintScalar p v = b →
        modularDistance p w (nearestWithHint p w b) ≤
          modularDistance p w v := by
  have hfold := nearestFold_spec p w b (List.range p.q)
    ((b.val * p.halfWidth : ℕ) : Scalar p) (initialHint p hp b)
  have hsearch : nearestWithHint p w b =
      (List.range p.q).foldl (nearestStep p w b)
        ((b.val * p.halfWidth : ℕ) : Scalar p) := rfl
  rw [hsearch]
  refine ⟨hfold.1, ?_⟩
  intro v hv
  have hmem : v ∈ ((List.range p.q : List ℕ) : List (Scalar p)) := by
    simp only [List.pure_def, List.bind_eq_flatMap, List.mem_flatMap, List.mem_range,
      List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨v.val, ZMod.val_lt v, (ZMod.natCast_zmod_val v).symm⟩
  exact hfold.2.2 v hmem hv

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

private theorem modularDistance_triangle
    (p : Params) (u v z : Scalar p) :
    modularDistance p u z ≤ modularDistance p u v + modularDistance p v z := by
  rw [modularDistance_eq_natAbs_valMinAbs, modularDistance_eq_natAbs_valMinAbs,
    modularDistance_eq_natAbs_valMinAbs]
  calc
    (u - z).valMinAbs.natAbs = ((u - v) + (v - z)).valMinAbs.natAbs := by
      congr 2
      simp [sub_eq_add_neg, add_assoc]
    _ ≤ ((u - v).valMinAbs + (v - z).valMinAbs).natAbs :=
      ZMod.natAbs_valMinAbs_add_le _ _
    _ ≤ (u - v).valMinAbs.natAbs + (v - z).valMinAbs.natAbs :=
      Int.natAbs_add_le _ _

private theorem roundedBlock_eq_halfIndex
    (p : Params) (hp : p.WellFormed) (x : ℕ) :
    (x + p.halfWidth) / p.blockWidth = (x / p.halfWidth + 1) / 2 := by
  have hhalf : 0 < p.halfWidth := by simp [Params.halfWidth]
  rw [blockWidth_eq_two_mul_halfWidth p hp, Nat.mul_comm 2 p.halfWidth,
    ← Nat.div_div_eq_div_mul]
  congr 1
  simpa using Nat.add_mul_div_left x 1 hhalf

private theorem hintIndex_mod_two_eq
    (p : Params) {u v : Scalar p} (h : hintScalar p u = hintScalar p v) :
    u.val / p.halfWidth % 2 = v.val / p.halfWidth % 2 := by
  have hval := congrArg ZMod.val h
  simpa [hintScalar, ZMod.val_natCast] using hval

private theorem halfIndex_eq_of_same_mod_two_of_sub_lt
    (H x y : ℕ) (hH : 0 < H) (hyx : y ≤ x) (hsub : x - y < H)
    (hmod : x / H % 2 = y / H % 2) :
    x / H = y / H := by
  have hdiv : y / H ≤ x / H := Nat.div_le_div_right hyx
  have hsubadd : x - y + y = x := Nat.sub_add_cancel hyx
  have hxmod : x % H < H := Nat.mod_lt x hH
  have hymod : y % H < H := Nat.mod_lt y hH
  have hxrepr := Nat.mod_add_div x H
  have hyrepr := Nat.mod_add_div y H
  have hyupper : y < H * (y / H + 1) := by nlinarith
  have hxupper : x < H * (y / H + 2) := by nlinarith
  have hdivupper : x / H < y / H + 2 :=
    (Nat.div_lt_iff_lt_mul hH).2 (by simpa [Nat.mul_comm] using hxupper)
  have htxmod : x / H % 2 < 2 := Nat.mod_lt _ (by omega)
  have htymod : y / H % 2 < 2 := Nat.mod_lt _ (by omega)
  have htxrepr := Nat.mod_add_div (x / H) 2
  have htyrepr := Nat.mod_add_div (y / H) 2
  omega

private theorem not_wrap_close_of_same_hint
    (p : Params) (hp : p.WellFormed) (u v : Scalar p)
    (hle : u.val ≤ v.val) (hwrap : p.q - (v.val - u.val) < p.halfWidth)
    (hhint : hintScalar p u = hintScalar p v) : False := by
  let blocks := 2 ^ (p.keyBits + 1)
  have hblocks : 0 < blocks := by simp [blocks]
  have hq : p.q = blocks * p.halfWidth := by
    simpa [blocks] using q_eq_halfBlocks_mul_halfWidth p hp
  have hvlt : v.val < p.q := ZMod.val_lt v
  have hdecomp : p.q - (v.val - u.val) = p.q - v.val + u.val := by omega
  have huH : u.val < p.halfWidth := by omega
  have hqvH : p.q - v.val < p.halfWidth := by omega
  have huindex : u.val / p.halfWidth = 0 := Nat.div_eq_of_lt huH
  have hmul :
      (blocks - 1) * p.halfWidth + p.halfWidth = blocks * p.halfWidth := by
    calc
      (blocks - 1) * p.halfWidth + p.halfWidth =
          (blocks - 1) * p.halfWidth + 1 * p.halfWidth := by simp
      _ = ((blocks - 1) + 1) * p.halfWidth := by rw [Nat.add_mul]
      _ = blocks * p.halfWidth := by rw [Nat.sub_add_cancel hblocks]
  have hvlower : (blocks - 1) * p.halfWidth ≤ v.val := by omega
  have hvupper : v.val < ((blocks - 1) + 1) * p.halfWidth := by
    rw [Nat.sub_add_cancel hblocks]
    simpa [← hq] using hvlt
  have hvindex : v.val / p.halfWidth = blocks - 1 :=
    Nat.div_eq_of_lt_le hvlower hvupper
  have hmod := hintIndex_mod_two_eq p hhint
  have hblocksmod : blocks % 2 = 0 := by simp [blocks, pow_succ]
  omega

private theorem modularDistance_comm (p : Params) (u v : Scalar p) :
    modularDistance p u v = modularDistance p v u := by
  simp [modularDistance, Nat.min_comm]

private theorem extractScalar_eq_of_order_of_same_hint_of_close
    (p : Params) (hp : p.WellFormed) (u v : Scalar p)
    (hle : u.val ≤ v.val) (hhint : hintScalar p u = hintScalar p v)
    (hclose : modularDistance p u v < p.halfWidth) :
    extractScalar p u = extractScalar p v := by
  by_cases huv : u = v
  · subst v
    rfl
  have hvusub : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
  have hcases := hclose
  unfold modularDistance at hcases
  rw [show u - v = -(v - u) by simp, ZMod.neg_val, ite_eq_right hvusub,
    ZMod.val_sub hle, min_lt_iff] at hcases
  rcases hcases with hwrap | hsub
  · exact False.elim (not_wrap_close_of_same_hint p hp u v hle hwrap hhint)
  · have hindex := halfIndex_eq_of_same_mod_two_of_sub_lt
      p.halfWidth v.val u.val (by simp [Params.halfWidth]) hle hsub
      (hintIndex_mod_two_eq p hhint).symm
    simp only [extractScalar]
    rw [roundedBlock_eq_halfIndex p hp, roundedBlock_eq_halfIndex p hp, hindex]

private theorem extractScalar_eq_of_same_hint_of_close
    (p : Params) (hp : p.WellFormed) (u v : Scalar p)
    (hhint : hintScalar p u = hintScalar p v)
    (hclose : modularDistance p u v < p.halfWidth) :
    extractScalar p u = extractScalar p v := by
  rcases le_total u.val v.val with hle | hle
  · exact extractScalar_eq_of_order_of_same_hint_of_close p hp u v hle hhint hclose
  · symm
    apply extractScalar_eq_of_order_of_same_hint_of_close p hp v u hle hhint.symm
    rwa [modularDistance_comm p v u]

/-- A residue inside the strict reconciliation radius recovers the sender's extracted value. -/
theorem reconcileScalar_eq_extractScalar_of_modularDistance_lt
    (p : Params) (hp : p.WellFormed) (w v : Scalar p)
    (hclose : modularDistance p w v < 2 ^ (p.discardBits - 2)) :
    reconcileScalar p w (hintScalar p v) = extractScalar p v := by
  have hspec := nearestWithHint_spec p hp w (hintScalar p v)
  have hminimum := hspec.2 v rfl
  have hnear :
      modularDistance p (nearestWithHint p w (hintScalar p v)) v < p.halfWidth := by
    calc
      modularDistance p (nearestWithHint p w (hintScalar p v)) v ≤
          modularDistance p (nearestWithHint p w (hintScalar p v)) w +
            modularDistance p w v := modularDistance_triangle p _ w v
      _ = modularDistance p w (nearestWithHint p w (hintScalar p v)) +
            modularDistance p w v := by rw [modularDistance_comm p]
      _ ≤ modularDistance p w v + modularDistance p w v :=
        Nat.add_le_add_right hminimum _
      _ < 2 ^ (p.discardBits - 2) + 2 ^ (p.discardBits - 2) :=
        Nat.add_lt_add hclose hclose
      _ = p.halfWidth := by
        rw [halfWidth_two_mul_radius p hp]
        omega
  unfold reconcileScalar
  exact extractScalar_eq_of_same_hint_of_close p hp _ v hspec.1 hnear

/-- Entrywise strict-radius closeness makes matrix reconciliation agree with extraction. -/
theorem reconcile_eq_extract_of_modularDistance_lt
    (p : Params) (hp : p.WellFormed) (w v : SharedMatrix p)
    (hclose : ∀ i j : Fin p.nbar,
      modularDistance p (w i j) (v i j) < 2 ^ (p.discardBits - 2)) :
    reconcile p w (makeHint p v) = extract p v := by
  funext i j
  exact reconcileScalar_eq_extractScalar_of_modularDistance_lt p hp (w i j) (v i j)
    (hclose i j)

end lweCKA
