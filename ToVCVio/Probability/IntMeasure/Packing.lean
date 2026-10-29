/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.Probability.IntMeasure.Radix

/-!
# Generic packing lemmas for integer counting measures

This module proves radix-packing arguments used by numerical certificates.
It contains no scheme-specific constants or recurrence.
-/

open scoped BigOperators

namespace ToVCVio.Packing

private theorem packDigits_lt {R n : Nat} {f : Nat → Nat}
    (h : ∀ i < n, f i < R) :
    ∑ i ∈ Finset.range n, f i * R ^ i < R ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hfn : f n < R := h n n.lt_succ_self
      have ihh := ih fun i hi => h i (hi.trans n.lt_succ_self)
      calc
        ∑ i ∈ Finset.range (n + 1), f i * R ^ i =
            (∑ i ∈ Finset.range n, f i * R ^ i) + f n * R ^ n :=
          Finset.sum_range_succ _ n
        _ < R ^ n + f n * R ^ n := by omega
        _ = (1 + f n) * R ^ n := by ring
        _ ≤ R * R ^ n := Nat.mul_le_mul_right _ (by omega)
        _ = R ^ (n + 1) := by ring

private theorem packDigits_digit {R n : Nat} {f : Nat → Nat}
    (h : ∀ i < n, f i < R) {t : Nat} (ht : t < n) :
    (∑ i ∈ Finset.range n, f i * R ^ i) / R ^ t % R = f t := by
  have hR : 0 < R := (Nat.zero_le _).trans_lt (h t ht)
  have hsplit := Finset.sum_range_add (fun i => f i * R ^ i) t (n - t)
  rw [show t + (n - t) = n from by omega] at hsplit
  obtain ⟨s, hs⟩ : ∃ s, n - t = s + 1 := ⟨n - t - 1, by omega⟩
  rw [hs, Finset.sum_range_succ'] at hsplit
  have htail : ∀ j : Nat, f (t + (j + 1)) * R ^ (t + (j + 1)) =
      R ^ t * (R * (f (t + (j + 1)) * R ^ j)) := by
    intro j
    rw [pow_add, pow_succ]
    ring
  rw [Finset.sum_congr rfl fun j _ => htail j, ← Finset.mul_sum,
    show t + 0 = t from rfl] at hsplit
  have hsum_inner :
      ∑ i ∈ Finset.range s, R * (f (t + (i + 1)) * R ^ i) =
        R * ∑ j ∈ Finset.range s, f (t + (j + 1)) * R ^ j :=
    (Finset.mul_sum _ _ _).symm
  rw [hsum_inner] at hsplit
  have hform :
      ∑ i ∈ Finset.range n, f i * R ^ i =
        (∑ i ∈ Finset.range t, f i * R ^ i) +
          R ^ t * (f t + R * ∑ j ∈ Finset.range s, f (t + (j + 1)) * R ^ j) := by
    rw [hsplit]
    ring
  have hlow : ∑ i ∈ Finset.range t, f i * R ^ i < R ^ t :=
    packDigits_lt fun i hi => h i (hi.trans ht)
  rw [hform, Nat.add_mul_div_left _ _ (pow_pos hR t), Nat.div_eq_of_lt hlow,
    zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (h t ht)]

private theorem testBit_pack_at {b n : Nat} {f : Nat → Nat}
    (hf : ∀ i < n, f i < 2 ^ b)
    {i r : Nat} (hi : i < n) (hr : r < b) :
    Nat.testBit (∑ q ∈ Finset.range n, f q * (2 ^ b) ^ q) (b * i + r) =
      Nat.testBit (f i) r := by
  have hdigit := packDigits_digit hf hi
  rw [show (2 ^ b) ^ i = 2 ^ (b * i) by rw [pow_mul]] at hdigit
  have hbit := congrArg (fun x : Nat => Nat.testBit x r) hdigit
  simpa only [Nat.testBit_mod_two_pow, hr, decide_true,
    Bool.true_and, Nat.testBit_div_two_pow, Nat.add_comm] using hbit

private theorem testBit_pack_outside {b n : Nat} {f : Nat → Nat}
    (hf : ∀ i < n, f i < 2 ^ b) {j : Nat} (hj : b * n ≤ j) :
    Nat.testBit (∑ q ∈ Finset.range n, f q * (2 ^ b) ^ q) j = false := by
  have hpack :
      ∑ q ∈ Finset.range n, f q * (2 ^ b) ^ q < 2 ^ (b * n) := by
    simpa only [pow_mul] using packDigits_lt hf
  have hpow : 2 ^ (b * n) ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hj
  exact Nat.testBit_lt_two_pow (hpack.trans_le hpow)

private theorem testBit_repeatedMask
    {b t n j : Nat} (hb : 0 < b) :
    Nat.testBit
        ((2 ^ (b - t) - 1) * ∑ q ∈ Finset.range n, (2 ^ b) ^ q) j =
      decide (j / b < n ∧ j % b < b - t) := by
  let i := j / b
  let r := j % b
  have hr : r < b := Nat.mod_lt _ hb
  have hji : b * i + r = j := Nat.div_add_mod j b
  have hmasklt : 2 ^ (b - t) - 1 < 2 ^ b := by
    have hp : 2 ^ (b - t) ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) (Nat.sub_le b t)
    have hpos := Nat.two_pow_pos (b - t)
    omega
  rw [Finset.mul_sum]
  change _ = decide (i < n ∧ r < b - t)
  by_cases hi : i < n
  · conv_lhs => rw [← hji]
    rw [testBit_pack_at (fun _ _ => hmasklt) hi hr,
      Nat.testBit_two_pow_sub_one]
    simp only [hi, true_and]
  · have hout : b * n ≤ j := by
      have hni : n ≤ j / b := Nat.le_of_not_gt hi
      simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hb).mp hni
    rw [testBit_pack_outside (fun _ _ => hmasklt) hout]
    simp only [hi, false_and, decide_false]

/-- Extracting a contiguous bit slice from packed base-power digits yields the shifted digits. -/
theorem packed_bitSlice
    {b k t n m : Nat} (hb : 0 < b) (ht : t ≤ b) (hkn : k + n ≤ m)
    (f : Nat → Nat) (hf : ∀ i < m, f i < 2 ^ b) :
    (((∑ q ∈ Finset.range m, f q * (2 ^ b) ^ q) >>> (b * k + t)) &&&
        ((2 ^ (b - t) - 1) * ∑ q ∈ Finset.range n, (2 ^ b) ^ q)) =
      ∑ q ∈ Finset.range n, (f (k + q) / 2 ^ t) * (2 ^ b) ^ q := by
  apply Nat.eq_of_testBit_eq
  intro j
  let i := j / b
  let r := j % b
  have hr : r < b := Nat.mod_lt _ hb
  have hji : b * i + r = j := Nat.div_add_mod j b
  have hg : ∀ q < n, f (k + q) / 2 ^ t < 2 ^ b := by
    intro q hq
    exact (Nat.div_le_self _ _).trans_lt (hf _ (by omega))
  rw [Nat.testBit_land, testBit_repeatedMask hb]
  by_cases hi : i < n
  · have hki : k + i < m := by omega
    rw [show decide (j / b < n ∧ j % b < b - t) = decide (r < b - t) by
      simp only [i, r, hi, true_and]]
    by_cases hrt : r < b - t
    · simp only [hrt, decide_true, Bool.and_true]
      rw [← hji, testBit_pack_at hg hi hr]
      have htr : t + r < b := by omega
      have hqbit : Nat.testBit (f (k + i) / 2 ^ t) r =
          Nat.testBit (f (k + i)) (t + r) := by
        rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]
      rw [Nat.testBit_shiftRight, hqbit]
      rw [show (b * k + t) + (b * i + r) = b * (k + i) + (t + r) by ring,
        testBit_pack_at hf hki htr]
    · simp only [hrt, decide_false, Bool.and_false]
      rw [← hji, testBit_pack_at hg hi hr]
      have hqbound : f (k + i) / 2 ^ t < 2 ^ (b - t) := by
        apply (Nat.div_lt_iff_lt_mul (by positivity)).2
        rw [← pow_add]
        simpa [Nat.sub_add_cancel ht] using hf (k + i) hki
      have hpow : 2 ^ (b - t) ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) (by omega)
      exact (Nat.testBit_lt_two_pow (hqbound.trans_le hpow)).symm
  · have hout : b * n ≤ j := by
      have hni : n ≤ j / b := Nat.le_of_not_gt hi
      simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hb).mp hni
    simp only [i, hi, false_and, decide_false, Bool.and_false]
    exact (testBit_pack_outside hg hout).symm

/-- A multiply-add fold over a range equals the corresponding reverse-order radix pack. -/
theorem foldl_range_mul_add_eq_reversePack
    (R : Nat) (f : Nat → Nat) (n : Nat) :
    (List.range n).foldl (fun acc i => acc * R + f i) 0 =
      ∑ i ∈ Finset.range n, f (n - 1 - i) * R ^ i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
        Finset.sum_range_succ']
      have hidx (i : Nat) : n + 1 - 1 - (i + 1) = n - 1 - i := by omega
      simp_rw [hidx, pow_succ]
      simp only [Nat.add_sub_cancel, Nat.sub_zero, pow_zero, mul_one]
      rw [Finset.sum_mul]
      ac_rfl

/-- A multiply-add fold of ones equals the finite geometric radix pack. -/
theorem foldl_range_mul_add_one_eq_pack (R n : Nat) :
    (List.range n).foldl (fun acc _ => acc * R + 1) 0 =
      ∑ i ∈ Finset.range n, R ^ i := by
  simpa using foldl_range_mul_add_eq_reversePack R (fun _ => 1) n

private theorem finset_sum_modEq
    {M : Nat} {iota : Type*} {s : Finset iota} {f g : iota → Nat}
    (h : ∀ i ∈ s, f i ≡ g i [MOD M]) :
    (∑ i ∈ s, f i) ≡ ∑ i ∈ s, g i [MOD M] := by
  classical
  induction s using Finset.cons_induction with
  | empty => rfl
  | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons]
      exact (h a (Finset.mem_cons_self a s)).add
        (ih fun i hi => h i (Finset.mem_cons_of_mem hi))

private theorem pack_mod_pred_eq_sum
    {R n : Nat} {f : Nat → Nat} (hR : 2 ≤ R)
    (hsum : ∑ i ∈ Finset.range n, f i < R - 1) :
    (∑ i ∈ Finset.range n, f i * R ^ i) % (R - 1) =
      ∑ i ∈ Finset.range n, f i := by
  have hbase : R ≡ 1 [MOD R - 1] := by
    have heq : R = (R - 1) + 1 := by omega
    rw [heq]
    exact Nat.add_modEq_left
  have hterm : ∀ i : Nat, f i * R ^ i ≡ f i [MOD R - 1] := by
    intro i
    simpa using (hbase.pow i).mul_left (f i)
  have hcong :
      (∑ i ∈ Finset.range n, f i * R ^ i) ≡
        ∑ i ∈ Finset.range n, f i [MOD R - 1] :=
    finset_sum_modEq fun i _ => hterm i
  calc
    (∑ i ∈ Finset.range n, f i * R ^ i) % (R - 1) =
        (∑ i ∈ Finset.range n, f i) % (R - 1) := hcong
    _ = ∑ i ∈ Finset.range n, f i := Nat.mod_eq_of_lt hsum

/-- A bounded packed measure reduces modulo one less than the radix to its total mass. -/
theorem measurePack_mod_pred_eq_totalMass
    {R n : Nat} {lo : ℤ} {F : ToVCVio.IntMeasure}
    (hwindow : ToVCVio.MeasureWindow F lo (lo + (n : ℤ) - 1))
    (hR : 2 ≤ R) (hmass : ToVCVio.totalMass F < R - 1) :
    ToVCVio.Radix.measurePack R lo F % (R - 1) = ToVCVio.totalMass F := by
  rw [ToVCVio.Radix.measurePack_eq_range_sum hwindow]
  have hsum : ∑ i ∈ Finset.range n, F (lo + i) < R - 1 := by
    rw [← ToVCVio.Radix.totalMass_eq_range_sum hwindow]
    exact hmass
  exact (pack_mod_pred_eq_sum hR hsum).trans
    (ToVCVio.Radix.totalMass_eq_range_sum hwindow).symm

/-- A bounded dot product is the middle digit of the product of two radix packs. -/
theorem dot_eq_pack_extract_bound {R q B : Nat} (hq : 0 < q)
    (a b : Nat → Nat) (hb : ∀ t < q, b t ≤ B)
    (ha : B * ∑ t ∈ Finset.range q, a t < R) :
    ∑ t ∈ Finset.range q, a t * b t =
      (∑ t ∈ Finset.range q, a t * R ^ t) *
        (∑ t ∈ Finset.range q, b (q - 1 - t) * R ^ t) /
          R ^ (q - 1) % R := by
  have hwinA : ToVCVio.MeasureWindow (ToVCVio.Radix.seqMeasure q a) 0 ((q : ℤ) - 1) :=
    ToVCVio.Radix.measureWindow_seqMeasure q a
  have hwinB :
      ToVCVio.MeasureWindow (ToVCVio.Radix.seqMeasure q fun u => b (q - 1 - u))
        0 ((q : ℤ) - 1) :=
    ToVCVio.Radix.measureWindow_seqMeasure q _
  have hwinA' :
      ToVCVio.MeasureWindow (ToVCVio.Radix.seqMeasure q a) 0 (0 + (q : ℤ) - 1) := by
    rw [zero_add]
    exact hwinA
  have hB : ∀ v : ℤ,
      (ToVCVio.Radix.seqMeasure q fun u => b (q - 1 - u)) v ≤ B :=
    ToVCVio.Radix.seqMeasure_apply_le fun t ht => hb (q - 1 - t) (by omega)
  have hmiddle :
      (ToVCVio.Radix.seqMeasure q a * ToVCVio.Radix.seqMeasure q fun u => b (q - 1 - u))
          (((q - 1 : Nat) : ℤ)) =
        ∑ t ∈ Finset.range q, a t * b t := by
    rw [ToVCVio.mul_apply_window hwinA']
    refine Finset.sum_congr rfl fun i hi => ?_
    have hilt := Finset.mem_range.mp hi
    rw [zero_add, ToVCVio.Radix.seqMeasure_apply a hilt]
    have harg : ((q - 1 : Nat) : ℤ) - (i : ℤ) = ((q - 1 - i : Nat) : ℤ) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_sub (by omega : i ≤ q - 1)]
      ring
    rw [harg, ToVCVio.Radix.seqMeasure_apply _ (by omega)]
    have hidx : q - 1 - (q - 1 - i) = i := by omega
    rw [hidx]
  have hdigit : ∀ v : ℤ,
      (ToVCVio.Radix.seqMeasure q a * ToVCVio.Radix.seqMeasure q fun u => b (q - 1 - u)) v < R := by
    intro v
    have hle := ToVCVio.Radix.mul_apply_le (n := q) hwinA' hB v
    rw [ToVCVio.Radix.totalMass_seqMeasure] at hle
    exact hle.trans_lt (by simpa only [Nat.mul_comm] using ha)
  have hwinAB :
      ToVCVio.MeasureWindow
        (ToVCVio.Radix.seqMeasure q a * ToVCVio.Radix.seqMeasure q fun u => b (q - 1 - u)) 0
        (0 + ((2 * q - 1 : Nat) : ℤ) - 1) := by
    have hmul := ToVCVio.measureWindow_mul hwinA hwinB
    rw [add_zero] at hmul
    refine hmul.mono (by omega) ?_
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * q)]
    omega
  have hdigitExtract :=
    ToVCVio.Radix.measurePack_digit (R := R) hwinAB hdigit (t := q - 1) (by omega)
  rw [zero_add] at hdigitExtract
  have hsplit := ToVCVio.Radix.measurePack_mul (R := R) hwinA hwinB
  rw [add_zero] at hsplit
  rw [← hmiddle, ← hdigitExtract, hsplit,
    ToVCVio.Radix.measurePack_seqMeasure, ToVCVio.Radix.measurePack_seqMeasure]

/-- A weighted finitely supported sum over a measure window equals its indexed range sum. -/
theorem finsuppWeightedSum_eq_range_sum
    (F : ToVCVio.IntMeasure) (lo : ℤ) (n : Nat)
    (w : ℤ → Nat) (hF : ToVCVio.MeasureWindow F lo (lo + n - 1)) :
    Finsupp.sum F (fun z a => a * w z) =
      ∑ i ∈ Finset.range n, F (lo + i) * w (lo + i) := by
  rw [Finsupp.sum_of_support_subset F
    (s := (Finset.range n).image fun i : Nat => lo + (i : ℤ))
    ?_ (fun z a => a * w z) fun i _ => zero_mul _]
  · rw [Finset.sum_image fun i _ j _ h => by omega]
  · intro z hz
    have hw := hF z (Finsupp.mem_support_iff.mp hz)
    rw [Finset.mem_image]
    exact ⟨(z - lo).toNat, Finset.mem_range.mpr (by omega), by omega⟩


end ToVCVio.Packing
