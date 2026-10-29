/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import ToVCVio.Probability.IntMeasure.Packing
import ToVCVio.Probability.IntMeasure.Radix
import VCVio.ProgramLogic.Unary.HoareTriple
import VCVio.OracleComp.EvalDist.Sum

/-!
# Rounded convolution certificates

A precision-parametric, downward-rounded convolution of integer counting measures. The rounded
counts are dominated by the exact ones, and mass lost outside the window is counted as failure,
so `probEvent_le_certificate` bounds a failure probability by two packed natural numbers.
-/

open OracleComp
open scoped BigOperators ENNReal
namespace FailureCertificate.RoundedConvolution
/-- Parameters and source weights for a truncated, downward-rounded convolution certificate. -/
structure Config where
  /-- Number of independent product terms in the accumulated sum. -/
  steps : ℕ
  /-- Radius of the source-count support, restricted to the integer interval `[-a, a]`. -/
  a : ℕ
  /-- Exponent used to normalize each source count by `2 ^ seedBits`. -/
  seedBits : ℕ
  /-- Radius of the retained interval after each product convolution. -/
  window : ℕ
  /-- Exponent of the initial count scale `2 ^ precision`. -/
  precision : ℕ
  /-- Integer count assigned to each source value before restricting its support. -/
  weight : ℤ → ℕ

/-- Source counting measure obtained by restricting the weights to `[-a, a]`. -/
noncomputable def counts (c : Config) : ToVCVio.IntMeasure :=
  ∑ z ∈ Finset.Icc (-(c.a : ℤ)) (c.a : ℤ),
    AddMonoidAlgebra.single z (c.weight z)

/-- Counts after successive product convolutions, truncations, and downward rounding. -/
noncomputable def lowerCounts (c : Config) : ℕ → ToVCVio.IntMeasure
  | 0 => AddMonoidAlgebra.single 0 (2 ^ c.precision)
  | k + 1 =>
      ∑ z ∈ Finset.Icc (-(c.window : ℤ)) (c.window : ℤ),
        AddMonoidAlgebra.single z
          (((lowerCounts c k *
            ToVCVio.productMeasure (counts c) (counts c)) z) /
              2 ^ (2 * c.seedBits))

/-- Bits per packed coefficient, including room for the source-product count mass. -/
def bits (c : Config) : ℕ :=
  c.precision + 1 + 2 * c.seedBits

/-- Power-of-two radix used to pack integer counting-measure coefficients. -/
def radix (c : Config) : ℕ :=
  2 ^ bits c

/-- Packed counts of the product of two source samples, shifted by `a ^ 2`. -/
def productPack (c : Config) : ℕ :=
  (List.range (2 * c.a + 1)).foldl (fun acc (i : ℕ) =>
    (List.range (2 * c.a + 1)).foldl (fun acc (j : ℕ) =>
      let x := (i : ℤ) - c.a
      let y := (j : ℤ) - c.a
      acc + c.weight x * c.weight y *
        radix c ^ ((x * y + (c.a : ℤ) ^ 2).toNat)) acc) 0

/-- Packed source counts for the final independent additive error. -/
def extraPack (c : Config) : ℕ :=
  (List.range (2 * c.a + 1)).foldl (fun acc (i : ℕ) =>
    acc + c.weight ((i : ℤ) - c.a) * radix c ^ i) 0

/-- Mask retaining the low `precision + 1` bits in each coefficient of the window. -/
def mask (c : Config) : ℕ :=
  (2 ^ (c.precision + 1) - 1) *
    (List.range (2 * c.window + 1)).foldl
      (fun acc _ => acc * radix c + 1) 0

/-- One packed product convolution, normalization shift, and window mask. -/
def step (c : Config) (x : ℕ) : ℕ :=
  ((x * productPack c) >>>
    (c.a ^ 2 * bits c + 2 * c.seedBits)) &&& mask c

/-- Packed approximation after `k` steps, starting from scaled point mass at zero. -/
def runN (c : Config) (k : ℕ) : ℕ :=
  (List.range k).foldl (fun x _ => step c x)
    (2 ^ c.precision * radix c ^ c.window)

/-- Weighted count after the final error convolution, paired with the preceding mass deficit. -/
def certificateValues (c : Config) (w : ℤ → ℕ) : ℕ × ℕ :=
  let M := c.window + c.a
  let wp := (List.range (2 * M + 1)).foldl
    (fun acc (i : ℕ) => acc * radix c + w ((i : ℤ) - M)) 0
  let run := runN c c.steps
  (((run * extraPack c * wp) >>> (bits c * (2 * M))) % radix c,
    2 ^ c.precision - run % (radix c - 1))


private def repunit (c : Config) : ℕ :=
  (List.range (2 * c.window + 1)).foldl (fun acc _ => acc * radix c + 1) 0
private def center (c : Config) : ℕ := c.window + c.a
private def run (c : Config) : ℕ := runN c c.steps
private theorem run_eq_runN (c : Config) : run c = runN c c.steps := rfl



private theorem sum_single_apply (s : Finset ℤ) (f : ℤ → ℕ) (z : ℤ) :
    (∑ y ∈ s, AddMonoidAlgebra.single y (f y) : ToVCVio.IntMeasure) z =
      if z ∈ s then f z else 0 := by
  classical
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Finset.sum_ite_eq']

/-- Inside `[-a, a]`, the source count measure is the configured weight. -/
theorem counts_apply_of_mem (c : Config) (z : ℤ)
    (hz : z ∈ Finset.Icc (-(c.a : ℤ)) (c.a : ℤ)) :
    counts c z = c.weight z := by
  rw [counts, sum_single_apply, ite_eq_left hz]

/-- Outside `[-a, a]`, the source count measure vanishes. -/
theorem counts_apply_of_not_mem (c : Config) (z : ℤ)
    (hz : z ∉ Finset.Icc (-(c.a : ℤ)) (c.a : ℤ)) :
    counts c z = 0 := by
  rw [counts, sum_single_apply, ite_eq_right hz]

private theorem measureWindow_counts (c : Config) :
    ToVCVio.MeasureWindow (counts c) (-(c.a : ℤ)) (c.a : ℤ) := by
  intro z hz
  by_contra hmem
  exact hz (counts_apply_of_not_mem c z (by simpa only [Finset.mem_Icc] using hmem))

private theorem measureWindow_products (c : Config) :
    ToVCVio.MeasureWindow (ToVCVio.productMeasure (counts c) (counts c))
      (-((c.a : ℤ) ^ 2)) ((c.a : ℤ) ^ 2) := by
  simpa [pow_two] using
    ToVCVio.measureWindow_productMeasure (measureWindow_counts c) (measureWindow_counts c)

private theorem lowerCounts_succ_apply (c : Config) (k : ℕ) (z : ℤ) :
    lowerCounts c (k + 1) z =
      if z ∈ Finset.Icc (-(c.window : ℤ)) (c.window : ℤ) then
        ((lowerCounts c k * ToVCVio.productMeasure (counts c) (counts c)) z) /
          2 ^ (2 * c.seedBits)
      else 0 := by
  rw [lowerCounts, sum_single_apply]

private theorem measureWindow_lowerCounts (c : Config) (k : ℕ) :
    ToVCVio.MeasureWindow (lowerCounts c k)
      (-(c.window : ℤ)) (c.window : ℤ) := by
  intro z hz
  cases k with
  | zero =>
      rw [lowerCounts, AddMonoidAlgebra.coeff_single, Finsupp.single_apply] at hz
      split_ifs at hz with h
      · omega
      · exact absurd rfl hz
  | succ k =>
      rw [lowerCounts_succ_apply] at hz
      split_ifs at hz with h
      · exact Finset.mem_Icc.mp h
      · exact absurd rfl hz

/-- A symmetric window `[-a, a]` in the `lo + n - 1` form used by the radix API. -/
private theorem measureWindow_toRange {F : ToVCVio.IntMeasure} {a : ℕ}
    (h : ToVCVio.MeasureWindow F (-(a : ℤ)) a) :
    ToVCVio.MeasureWindow F (-(a : ℤ)) (-(a : ℤ) + (2 * a + 1 : ℕ) - 1) :=
  h.mono le_rfl (by omega)

private theorem finsetSum_apply_le_totalMass
    (F : ToVCVio.IntMeasure) (s : Finset ℤ) :
    ∑ z ∈ s, F z ≤ ToVCVio.totalMass F :=
  Finset.sum_le_sum_of_ne_zero fun _ _ hz => Finsupp.mem_support_iff.mpr hz

private theorem finsetSum_mul_apply_le
    (F G : ToVCVio.IntMeasure) (s : Finset ℤ) (z : ℤ) :
    ∑ x ∈ s, F x * G (z - x) ≤ (F * G) z := by
  refine (Finset.sum_le_sum_of_ne_zero fun x _ hx =>
    Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hx)).trans_eq ?_
  rw [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum]
  exact Finset.sum_congr rfl fun x _ => by rw [neg_add_eq_sub]

private theorem range_sum_eq_image_sum (lo : ℤ) (n : ℕ) (g : ℤ → ℕ) :
    ∑ i ∈ Finset.range n, g (lo + i) =
      ∑ z ∈ (Finset.range n).image (fun i : ℕ => lo + i), g z :=
  (Finset.sum_image fun _ _ _ _ h => by omega).symm

private theorem totalMass_products (c : Config)
    (hmass : ToVCVio.totalMass (counts c) = 2 ^ c.seedBits) :
    ToVCVio.totalMass (ToVCVio.productMeasure (counts c) (counts c)) =
      2 ^ (2 * c.seedBits) := by
  rw [ToVCVio.totalMass_productMeasure, hmass, ← pow_two, ← pow_mul, Nat.mul_comm c.seedBits 2]

theorem totalMass_lowerCounts_le
    (c : Config) (hmass : ToVCVio.totalMass (counts c) = 2 ^ c.seedBits)
    (k : ℕ) :
    ToVCVio.totalMass (lowerCounts c k) ≤ 2 ^ c.precision := by
  induction k with
  | zero => rw [lowerCounts, ToVCVio.totalMass_single]
  | succ k ih =>
      let D2 := 2 ^ (2 * c.seedBits)
      let X := lowerCounts c k * ToVCVio.productMeasure (counts c) (counts c)
      have hscaled : D2 * ToVCVio.totalMass (lowerCounts c (k + 1)) ≤ D2 * 2 ^ c.precision := by
        calc
          D2 * ToVCVio.totalMass (lowerCounts c (k + 1)) =
              ∑ i ∈ Finset.range (2 * c.window + 1), D2 * (X (-(c.window : ℤ) + i) / D2) := by
            rw [ToVCVio.Radix.totalMass_eq_range_sum
              (measureWindow_toRange (measureWindow_lowerCounts c (k + 1))), Finset.mul_sum]
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [lowerCounts_succ_apply, ite_eq_left (Finset.mem_Icc.mpr
              (by have := Finset.mem_range.mp hi; omega))]
          _ ≤ ∑ i ∈ Finset.range (2 * c.window + 1), X (-(c.window : ℤ) + i) :=
            Finset.sum_le_sum fun _ _ => Nat.mul_div_le _ _
          _ ≤ ToVCVio.totalMass X := by
            rw [range_sum_eq_image_sum (-(c.window : ℤ)) _ (fun z => X z)]
            exact finsetSum_apply_le_totalMass _ _
          _ = ToVCVio.totalMass (lowerCounts c k) * D2 := by
            rw [ToVCVio.totalMass_mul, totalMass_products c hmass]
          _ ≤ D2 * 2 ^ c.precision := (Nat.mul_comm _ _).trans_le (Nat.mul_le_mul_left _ ih)
      exact le_of_mul_le_mul_left hscaled (by positivity)

private theorem productCoefficient_lt_radix
    (c : Config) (hmass : ToVCVio.totalMass (counts c) = 2 ^ c.seedBits)
    (k : ℕ) (z : ℤ) :
    (lowerCounts c k * ToVCVio.productMeasure (counts c) (counts c)) z <
      2 ^ ((c.precision + 1) + 2 * c.seedBits) := by
  calc
    _ ≤ ToVCVio.totalMass
        (lowerCounts c k * ToVCVio.productMeasure (counts c) (counts c)) :=
      finsetSum_apply_le_totalMass _ {z}
    _ = ToVCVio.totalMass (lowerCounts c k) *
        ToVCVio.totalMass (ToVCVio.productMeasure (counts c) (counts c)) := by
      rw [ToVCVio.totalMass_mul]
    _ ≤ 2 ^ c.precision * 2 ^ (2 * c.seedBits) := by
      rw [totalMass_products c hmass]
      exact Nat.mul_le_mul_right _ (totalMass_lowerCounts_le c hmass k)
    _ < 2 ^ ((c.precision + 1) + 2 * c.seedBits) := by
      rw [← pow_add]
      exact Nat.pow_lt_pow_right (by omega) (by omega)

private theorem foldl_range_add_eq_sum (n : ℕ) (f : ℕ → ℕ) (x : ℕ) :
    (List.range n).foldl (fun acc (i : ℕ) => acc + f i) x =
      x + ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih, Finset.sum_range_succ, add_assoc]

private theorem rangeImage_eq_Icc (a : ℕ) :
    (Finset.range (2 * a + 1)).image (fun i : ℕ => (i : ℤ) - a) =
      Finset.Icc (-(a : ℤ)) (a : ℤ) := by
  ext z
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · exact fun _ => ⟨(z + a).toNat, by omega, by omega⟩

private theorem counts_apply_index (c : Config) (i : ℕ)
    (hi : i < 2 * c.a + 1) :
    counts c ((i : ℤ) - c.a) = c.weight ((i : ℤ) - c.a) := by
  apply counts_apply_of_mem
  simp only [Finset.mem_Icc]
  omega

private theorem extraPack_eq_measurePack (c : Config) :
    (List.range (2 * c.a + 1)).foldl (fun acc (i : ℕ) =>
      acc + c.weight ((i : ℤ) - c.a) *
        (2 ^ ((c.precision + 1) + 2 * c.seedBits) : ℕ) ^ i) 0 =
      ToVCVio.Radix.measurePack (2 ^ ((c.precision + 1) + 2 * c.seedBits))
        (-(c.a : ℤ)) (counts c) := by
  rw [ToVCVio.Radix.measurePack_eq_range_sum
    (measureWindow_toRange (measureWindow_counts c))]
  rw [foldl_range_add_eq_sum, zero_add]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [show -(c.a : ℤ) + i = (i : ℤ) - c.a by ring,
    counts_apply_index c i (Finset.mem_range.mp hi)]


private theorem extraPack_eq_measurePack' (c : Config) :
    extraPack c = ToVCVio.Radix.measurePack (radix c) (-(c.a : ℤ)) (counts c) := by
  simpa only [extraPack, radix, bits] using extraPack_eq_measurePack c

private theorem repunit_eq_sum (c : Config) :
    repunit c = ∑ i ∈ Finset.range (2 * c.window + 1), radix c ^ i := by
  unfold repunit
  exact ToVCVio.Packing.foldl_range_mul_add_one_eq_pack
    (radix c) (2 * c.window + 1)

private theorem mask_eq_sum (c : Config) :
    mask c = (2 ^ (bits c - 2 * c.seedBits) - 1) *
      ∑ i ∈ Finset.range (2 * c.window + 1),
        (2 ^ bits c) ^ i := by
  change (2 ^ (c.precision + 1) - 1) * repunit c = _
  rw [repunit_eq_sum]
  simp only [radix, bits]
  rw [show (c.precision + 1) + 2 * c.seedBits - 2 * c.seedBits = (c.precision + 1) by omega]

private theorem counts_eq_indexed_sum (c : Config) :
    counts c = ∑ i ∈ Finset.range (2 * c.a + 1),
      AddMonoidAlgebra.single ((i : ℤ) - c.a) (c.weight ((i : ℤ) - c.a)) := by
  rw [counts, ← rangeImage_eq_Icc, Finset.sum_image fun _ _ _ _ h => by omega]

private theorem productMeasure_counts_eq_sum (c : Config) :
    ToVCVio.productMeasure (counts c) (counts c) =
      ∑ i ∈ Finset.range (2 * c.a + 1),
        ∑ j ∈ Finset.range (2 * c.a + 1),
          AddMonoidAlgebra.single
            (((i : ℤ) - c.a) * ((j : ℤ) - c.a))
            (c.weight ((i : ℤ) - c.a) * c.weight ((j : ℤ) - c.a)) := by
  rw [counts_eq_indexed_sum, ToVCVio.productMeasure,
    AddMonoidAlgebra.coeff_sum]
  refine (Finsupp.sum_finsetSum_index (fun _ => by simp) (fun a m₁ m₂ => ?_)).symm.trans ?_
  · refine (Finsupp.sum_congr fun b k => ?_).trans Finsupp.sum_add
    rw [add_mul]
    exact AddMonoidAlgebra.single_add _ _ _
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (Finsupp.sum_single_index (by simp)).trans ?_
  refine (Finsupp.sum_finsetSum_index (fun _ => by simp) (fun b k₁ k₂ => ?_)).symm.trans ?_
  · rw [mul_add]
    exact AddMonoidAlgebra.single_add _ _ _
  refine Finset.sum_congr rfl fun j _ => ?_
  change (Finsupp.single ((j : ℤ) - c.a) (c.weight ((j : ℤ) - c.a))).sum
      (fun b k => AddMonoidAlgebra.single (((i : ℤ) - c.a) * b)
        (c.weight ((i : ℤ) - c.a) * k)) = _
  rw [Finsupp.sum_single_index]
  simp





private theorem measurePack_finset_sum
    {ι : Type} (R : ℕ) (lo : ℤ)
    (s : Finset ι) (F : ι → ToVCVio.IntMeasure) :
    ToVCVio.Radix.measurePack R lo (∑ i ∈ s, F i) =
      ∑ i ∈ s, ToVCVio.Radix.measurePack R lo (F i) := by
  classical
  unfold ToVCVio.Radix.measurePack
  rw [AddMonoidAlgebra.coeff_sum]
  exact (Finsupp.sum_finsetSum_index (fun _ => zero_mul _) fun _ _ _ => add_mul _ _ _).symm

private theorem productPack_eq_measurePack (c : Config) :
    productPack c = ToVCVio.Radix.measurePack (radix c) (-((c.a : ℤ) ^ 2))
      (ToVCVio.productMeasure (counts c) (counts c)) := by
  simp only [productPack, foldl_range_add_eq_sum, zero_add]
  rw [productMeasure_counts_eq_sum, measurePack_finset_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [measurePack_finset_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ToVCVio.Radix.measurePack_single]
  congr 2
  ring_nf

private theorem runN_succ (c : Config) (k : ℕ) :
    runN c (k + 1) = step c (runN c k) := by
  rw [runN, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

private theorem measurePack_lowerCounts_zero (c : Config) :
    ToVCVio.Radix.measurePack (radix c) (-(c.window : ℤ)) (lowerCounts c 0) =
      2 ^ c.precision * radix c ^ c.window := by
  rw [lowerCounts, ToVCVio.Radix.measurePack_single]
  congr 2
  omega

private theorem measurePack_lowerCounts_mod_pred
    (c : Config) (hbits : 0 < c.seedBits)
    (hmass : ToVCVio.totalMass (counts c) = 2 ^ c.seedBits) (k : ℕ) :
    ToVCVio.Radix.measurePack (radix c) (-(c.window : ℤ)) (lowerCounts c k) %
        (radix c - 1) = ToVCVio.totalMass (lowerCounts c k) := by
  apply ToVCVio.Packing.measurePack_mod_pred_eq_totalMass (n := 2 * c.window + 1)
  · exact measureWindow_toRange (measureWindow_lowerCounts c k)
  · exact Nat.le_self_pow (by simp only [bits]; omega) 2
  · have hle := totalMass_lowerCounts_le c hmass k
    have hpow : 2 ^ (c.precision + 2) ≤ radix c :=
      Nat.pow_le_pow_right (by omega) (by simp only [bits]; omega)
    have hp : 0 < 2 ^ c.precision := by positivity
    have hgap : 2 ^ c.precision < 2 ^ (c.precision + 2) - 1 := by
      rw [pow_add]
      norm_num
      omega
    omega

private theorem measureWindow_lower_product (c : Config) (k : ℕ) :
    ToVCVio.MeasureWindow
      (lowerCounts c k * ToVCVio.productMeasure (counts c) (counts c))
      (-((c.window : ℤ) + (c.a : ℤ) ^ 2))
      ((c.window : ℤ) + (c.a : ℤ) ^ 2) := by
  have h := ToVCVio.measureWindow_mul
    (measureWindow_lowerCounts c k) (measureWindow_products c)
  convert h using 1
  all_goals ring

private theorem measurePack_lowerCounts_succ_sum (c : Config) (k : ℕ) :
    ToVCVio.Radix.measurePack (radix c) (-(c.window : ℤ)) (lowerCounts c (k + 1)) =
      ∑ i ∈ Finset.range (2 * c.window + 1),
        ((lowerCounts c k * ToVCVio.productMeasure (counts c) (counts c))
          (-(c.window : ℤ) + i) / 2 ^ (2 * c.seedBits)) * radix c ^ i := by
  rw [ToVCVio.Radix.measurePack_eq_range_sum
    (measureWindow_toRange (measureWindow_lowerCounts c (k + 1)))]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [lowerCounts_succ_apply, ite_eq_left]
  simpa only [Finset.mem_Icc] using
    (show -(c.window : ℤ) ≤ -(c.window : ℤ) + (i : ℤ) ∧
        -(c.window : ℤ) + (i : ℤ) ≤ c.window by
      have := Finset.mem_range.mp hi
      omega)

private theorem measurePack_lower_product_sum (c : Config) (k : ℕ) :
    ToVCVio.Radix.measurePack (radix c) (-((c.window : ℤ) + (c.a : ℤ) ^ 2))
        (lowerCounts c k * ToVCVio.productMeasure (counts c) (counts c)) =
      ∑ i ∈ Finset.range (2 * (c.window + c.a ^ 2) + 1),
        (lowerCounts c k * ToVCVio.productMeasure (counts c) (counts c))
          (-((c.window : ℤ) + (c.a : ℤ) ^ 2) + i) * radix c ^ i := by
  apply ToVCVio.Radix.measurePack_eq_range_sum
  convert measureWindow_lower_product c k using 1
  all_goals push_cast
  all_goals ring_nf

private theorem measurePack_lower_product_mul (c : Config) (k : ℕ) :
    ToVCVio.Radix.measurePack (radix c) (-((c.window : ℤ) + (c.a : ℤ) ^ 2))
        (lowerCounts c k * ToVCVio.productMeasure (counts c) (counts c)) =
      ToVCVio.Radix.measurePack (radix c) (-(c.window : ℤ)) (lowerCounts c k) *
        productPack c := by
  rw [productPack_eq_measurePack]
  convert ToVCVio.Radix.measurePack_mul (R := radix c)
    (measureWindow_lowerCounts c k) (measureWindow_products c) using 2
  ring

private theorem packed_crop_step (c : Config) (f : ℕ → ℕ)
    (hf : ∀ i < 2 * (c.window + c.a ^ 2) + 1, f i < radix c) :
    (((∑ i ∈ Finset.range (2 * (c.window + c.a ^ 2) + 1),
          f i * radix c ^ i) >>>
        (c.a ^ 2 * bits c + 2 * c.seedBits)) &&& mask c) =
      ∑ i ∈ Finset.range (2 * c.window + 1),
        (f (c.a ^ 2 + i) / 2 ^ (2 * c.seedBits)) * radix c ^ i := by
  have h := ToVCVio.Packing.packed_bitSlice
    (b := bits c) (k := c.a ^ 2) (t := 2 * c.seedBits)
    (n := 2 * c.window + 1) (m := 2 * (c.window + c.a ^ 2) + 1)
    (by simp [bits]) (by simp [bits]) (by omega) f (by simpa [radix] using hf)
  simpa only [radix, mask_eq_sum,
    show bits c - 2 * c.seedBits = (c.precision + 1) by simp [bits],
    show c.a ^ 2 * bits c + 2 * c.seedBits =
      bits c * c.a ^ 2 + 2 * c.seedBits by ring] using h

private theorem measurePack_lowerCounts_succ
    (c : Config) (hmass : ToVCVio.totalMass (counts c) = 2 ^ c.seedBits)
    (k : ℕ) :
    ToVCVio.Radix.measurePack (radix c) (-(c.window : ℤ)) (lowerCounts c (k + 1)) =
      step c (ToVCVio.Radix.measurePack (radix c) (-(c.window : ℤ)) (lowerCounts c k)) := by
  have h := packed_crop_step c
    (fun i => (lowerCounts c k * ToVCVio.productMeasure (counts c) (counts c))
      (-((c.window : ℤ) + (c.a : ℤ) ^ 2) + i))
    (fun i _ => productCoefficient_lt_radix c hmass k
      (-((c.window : ℤ) + (c.a : ℤ) ^ 2) + i))
  have hindex (i : ℕ) :
      -((c.window : ℤ) + (c.a : ℤ) ^ 2) + (c.a ^ 2 + i : ℕ) =
        -(c.window : ℤ) + i := by
    push_cast
    ring
  simp_rw [hindex] at h
  have hp := (measurePack_lower_product_sum c k).symm.trans
    (measurePack_lower_product_mul c k)
  calc
    _ = ∑ i ∈ Finset.range (2 * c.window + 1),
        ((lowerCounts c k * ToVCVio.productMeasure (counts c) (counts c))
          (-(c.window : ℤ) + i) / 2 ^ (2 * c.seedBits)) * radix c ^ i :=
      measurePack_lowerCounts_succ_sum c k
    _ = (((∑ i ∈ Finset.range (2 * (c.window + c.a ^ 2) + 1),
        (lowerCounts c k * ToVCVio.productMeasure (counts c) (counts c))
          (-((c.window : ℤ) + (c.a : ℤ) ^ 2) + i) * radix c ^ i) >>>
          (c.a ^ 2 * bits c + 2 * c.seedBits)) &&& mask c) := h.symm
    _ = _ := by
      rw [step]
      exact congrArg (fun x : ℕ =>
        (x >>> (c.a ^ 2 * bits c + 2 * c.seedBits)) &&& mask c) hp

private theorem measurePack_lowerCounts_runN
    (c : Config) (hmass : ToVCVio.totalMass (counts c) = 2 ^ c.seedBits)
    (k : ℕ) :
    ToVCVio.Radix.measurePack (radix c) (-(c.window : ℤ)) (lowerCounts c k) =
      runN c k := by
  induction k with
  | zero => exact measurePack_lowerCounts_zero c
  | succ k ih => rw [measurePack_lowerCounts_succ c hmass k, ih, ← runN_succ]



private theorem measureWindow_approxCounts (c : Config) (k : ℕ) :
    ToVCVio.MeasureWindow (lowerCounts c k * counts c)
      (-(center c : ℤ)) (center c : ℤ) := by
  have h := ToVCVio.measureWindow_mul
    (measureWindow_lowerCounts c k) (measureWindow_counts c)
  convert h using 1
  · simp only [center, Nat.cast_add]
    ring
  · simp only [center, Nat.cast_add]

private theorem totalMass_approxCounts_le
    (c : Config) (hmass : ToVCVio.totalMass (counts c) = 2 ^ c.seedBits)
    (k : ℕ) :
    ToVCVio.totalMass (lowerCounts c k * counts c) ≤
      2 ^ c.precision * 2 ^ c.seedBits := by
  rw [ToVCVio.totalMass_mul, hmass]
  exact Nat.mul_le_mul_right _ (totalMass_lowerCounts_le c hmass k)

private theorem measurePack_approxCounts
    (c : Config) (hmass : ToVCVio.totalMass (counts c) = 2 ^ c.seedBits) :
    ToVCVio.Radix.measurePack (radix c) (-(center c : ℤ))
        (lowerCounts c c.steps * counts c) =
      run c * extraPack c := by
  calc
    _ = ToVCVio.Radix.measurePack (radix c) (-(c.window : ℤ))
          (lowerCounts c c.steps) *
        ToVCVio.Radix.measurePack (radix c) (-(c.a : ℤ)) (counts c) := by
      convert ToVCVio.Radix.measurePack_mul (R := radix c)
        (measureWindow_lowerCounts c c.steps) (measureWindow_counts c) using 1
      simp only [center, Nat.cast_add]
      ring_nf
    _ = run c * extraPack c := by
      rw [measurePack_lowerCounts_runN c hmass, ← run_eq_runN,
        ← extraPack_eq_measurePack']


theorem runN_eq_measurePack (c : Config)
    (hmass : ToVCVio.totalMass (counts c) = 2 ^ c.seedBits) (k : ℕ) :
    runN c k = ToVCVio.Radix.measurePack (radix c) (-(c.window : ℤ)) (lowerCounts c k) :=
  (measurePack_lowerCounts_runN c hmass k).symm
private theorem lowerCounts_mul_domination
    (c : Config) (k : ℕ) (G : ToVCVio.IntMeasure)
    (ih : ∀ z, (2 ^ (2 * c.seedBits)) ^ k * lowerCounts c k z ≤
      2 ^ c.precision * ((ToVCVio.productMeasure (counts c) (counts c)) ^ k) z)
    (z : ℤ) :
    (2 ^ (2 * c.seedBits)) ^ k * (lowerCounts c k * G) z ≤
      2 ^ c.precision * (((ToVCVio.productMeasure (counts c) (counts c)) ^ k * G) z) := by
  let P := ToVCVio.productMeasure (counts c) (counts c)
  calc
    _ = ∑ i ∈ Finset.range (2 * c.window + 1),
          ((2 ^ (2 * c.seedBits)) ^ k * lowerCounts c k (-(c.window : ℤ) + i)) *
            G (z - (-(c.window : ℤ) + i)) := by
      rw [ToVCVio.mul_apply_window (measureWindow_toRange (measureWindow_lowerCounts c k)) z,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    _ ≤ ∑ i ∈ Finset.range (2 * c.window + 1),
          (2 ^ c.precision * (P ^ k) (-(c.window : ℤ) + i)) *
            G (z - (-(c.window : ℤ) + i)) :=
      Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ (ih _)
    _ = 2 ^ c.precision * ∑ i ∈ Finset.range (2 * c.window + 1),
          (P ^ k) (-(c.window : ℤ) + i) * G (z - (-(c.window : ℤ) + i)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    _ ≤ 2 ^ c.precision * ((P ^ k) * G) z := by
      apply Nat.mul_le_mul_left
      rw [range_sum_eq_image_sum (-(c.window : ℤ)) _ (fun x => (P ^ k) x * G (z - x))]
      exact finsetSum_mul_apply_le _ _ _ _

theorem lowerCounts_domination
    (c : Config) (k : ℕ) (z : ℤ) :
    (2 ^ (2 * c.seedBits)) ^ k * lowerCounts c k z ≤
      2 ^ c.precision *
        ((ToVCVio.productMeasure (counts c) (counts c)) ^ k) z := by
  induction k generalizing z with
  | zero =>
      by_cases hz : z = 0 <;>
        simp [lowerCounts, AddMonoidAlgebra.one_def, hz,
          -LaurentPolynomial.single_eq_C_mul_T]
  | succ k ih =>
      rw [lowerCounts_succ_apply]
      split_ifs
      · calc
          _ ≤ (2 ^ (2 * c.seedBits)) ^ k *
                (lowerCounts c k * ToVCVio.productMeasure (counts c) (counts c)) z := by
            rw [pow_succ, mul_assoc]
            exact Nat.mul_le_mul_left _ (Nat.mul_div_le _ _)
          _ ≤ _ := lowerCounts_mul_domination c k _ ih z
          _ = _ := by rw [pow_succ]
      · simp

private theorem lowerCounts_mul_counts_domination
    (c : Config) (k : ℕ) (z : ℤ) :
    (2 ^ (2 * c.seedBits)) ^ k * (lowerCounts c k * counts c) z ≤
      2 ^ c.precision *
        (((ToVCVio.productMeasure (counts c) (counts c)) ^ k * counts c) z) :=
  lowerCounts_mul_domination c k _ (lowerCounts_domination c k) z

private theorem totalMass_fullCounts
    (c : Config) (hmass : ToVCVio.totalMass (counts c) = 2 ^ c.seedBits) :
    ToVCVio.totalMass
        ((ToVCVio.productMeasure (counts c) (counts c)) ^ c.steps * counts c) =
      (2 ^ c.seedBits) ^ (2 * c.steps + 1) := by
  rw [ToVCVio.totalMass_mul, ToVCVio.totalMass_pow,
    ToVCVio.totalMass_productMeasure, hmass]
  rw [← pow_two, ← pow_mul, ← pow_succ]

private theorem totalMass_approxCounts
    (c : Config) (hmass : ToVCVio.totalMass (counts c) = 2 ^ c.seedBits) :
    ToVCVio.totalMass (lowerCounts c c.steps * counts c) =
      2 ^ c.seedBits * ToVCVio.totalMass (lowerCounts c c.steps) := by
  rw [ToVCVio.totalMass_mul, hmass, Nat.mul_comm]

private theorem approxCounts_domination
    (c : Config) (z : ℤ) :
    (2 ^ c.seedBits) ^ (2 * c.steps + 1) *
        (lowerCounts c c.steps * counts c) z ≤
      (2 ^ c.seedBits * 2 ^ c.precision) *
        (((ToVCVio.productMeasure (counts c) (counts c)) ^ c.steps *
          counts c) z) := by
  have h := lowerCounts_mul_counts_domination c c.steps z
  rw [← pow_mul, show 2 * c.seedBits * c.steps = c.seedBits * (2 * c.steps) by ring,
    pow_mul] at h
  calc
    _ = 2 ^ c.seedBits * ((2 ^ c.seedBits) ^ (2 * c.steps) *
          (lowerCounts c c.steps * counts c) z) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ h
    _ = _ := by ring

private def weightPack (c : Config) (w : ℤ → ℕ) : ℕ :=
  (List.range (2 * center c + 1)).foldl
    (fun acc (i : ℕ) => acc * radix c + w ((i : ℤ) - center c)) 0

private theorem weightPack_eq_sum (c : Config) (w : ℤ → ℕ) :
    weightPack c w = ∑ i ∈ Finset.range (2 * center c + 1),
      w (-(center c : ℤ) + ((2 * center c + 1 - 1 - i : ℕ) : ℤ)) * radix c ^ i := by
  rw [weightPack, ToVCVio.Packing.foldl_range_mul_add_eq_reversePack]
  apply Finset.sum_congr rfl
  intro i hi
  congr 2
  ring

private theorem weightedMass_eq_packExtract (c : Config) (w : ℤ → ℕ)
    (hmass : ToVCVio.totalMass (counts c) = 2 ^ c.seedBits)
    (hw : ∀ z, w z ≤ 1) :
    Finsupp.sum (lowerCounts c c.steps * counts c) (fun z a => a * w z) =
      ToVCVio.Radix.measurePack (radix c) (-(center c : ℤ))
        (lowerCounts c c.steps * counts c) * weightPack c w /
          radix c ^ (2 * center c) % radix c := by
  let A := lowerCounts c c.steps * counts c
  have hwindow : ToVCVio.MeasureWindow A
      (-(center c : ℤ)) (-(center c : ℤ) + (2 * center c + 1 : ℕ) - 1) :=
    measureWindow_toRange (measureWindow_approxCounts c c.steps)
  have hsum : ∑ i ∈ Finset.range (2 * center c + 1), A (-(center c : ℤ) + i) =
      ToVCVio.totalMass A := (ToVCVio.Radix.totalMass_eq_range_sum hwindow).symm
  have hcarry : 1 * ∑ i ∈ Finset.range (2 * center c + 1),
      A (-(center c : ℤ) + i) < radix c := by
    rw [one_mul, hsum]
    calc
      _ ≤ 2 ^ c.precision * 2 ^ c.seedBits := totalMass_approxCounts_le c hmass c.steps
      _ < radix c := by
        rw [← pow_add]
        apply Nat.pow_lt_pow_right (by omega)
        simp only [bits]
        omega
  have hdot := ToVCVio.Packing.dot_eq_pack_extract_bound
    (R := radix c) (q := 2 * center c + 1) (B := 1) (by omega)
    (fun i => A (-(center c : ℤ) + i))
    (fun i => w (-(center c : ℤ) + i)) (fun i _ => hw _) hcarry
  rw [← ToVCVio.Radix.measurePack_eq_range_sum hwindow, ← weightPack_eq_sum] at hdot
  rw [ToVCVio.Packing.finsuppWeightedSum_eq_range_sum A
    (-(center c : ℤ)) (2 * center c + 1) w hwindow]
  simpa only [show 2 * center c + 1 - 1 = 2 * center c by omega] using hdot

theorem certificateValues_eq (c : Config) (w : ℤ → ℕ)
    (hbits : 0 < c.seedBits)
    (hmass : ToVCVio.totalMass (counts c) = 2 ^ c.seedBits)
    (hw : ∀ z, w z ≤ 1) :
    certificateValues c w =
      (Finsupp.sum (lowerCounts c c.steps * counts c) (fun z a => a * w z),
       2 ^ c.precision - ToVCVio.totalMass (lowerCounts c c.steps)) := by
  change (((run c * extraPack c * weightPack c w) >>> (bits c * (2 * center c))) % radix c,
      2 ^ c.precision - run c % (radix c - 1)) = _
  refine Prod.ext ?_ ?_
  · rw [Nat.shiftRight_eq_div_pow, pow_mul, ← measurePack_approxCounts c hmass]
    exact (weightedMass_eq_packExtract c w hmass hw).symm
  · rw [← measurePack_lowerCounts_mod_pred c hbits hmass c.steps,
      measurePack_lowerCounts_runN c hmass, ← run_eq_runN]

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
  have hS' : (S : ℝ≥0∞) ≠ 0 := by exact_mod_cast hS.ne'
  have hresidual :
      ∑ z ∈ s, ((F z : ℝ≥0∞) / D - (A z : ℝ≥0∞) / S) =
        ((S - ∑ z ∈ s, A z : Nat) : ℝ≥0∞) / S := by
    have hdecomp : ∑ z ∈ s, (A z : ℝ≥0∞) / S +
        ∑ z ∈ s, ((F z : ℝ≥0∞) / D - (A z : ℝ≥0∞) / S) = ∑ z ∈ s, (F z : ℝ≥0∞) / D := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun z _ => add_tsub_cancel_of_le (hratio z)
    have hsumF_one : ∑ z ∈ s, (F z : ℝ≥0∞) / D = 1 := by
      rw [← ENNReal.sum_div, ← Nat.cast_sum, hmassF]
      exact ENNReal.div_self (by exact_mod_cast hD.ne') (ENNReal.natCast_ne_top _)
    rw [hsumF_one, ← ENNReal.sum_div, ← Nat.cast_sum] at hdecomp
    rw [ENNReal.eq_sub_of_add_eq (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hS')
        ((add_comm _ _).trans hdecomp),
      ENNReal.natCast_sub, ENNReal.sub_div (fun _ _ => hS'),
      ENNReal.div_self hS' (ENNReal.natCast_ne_top S)]
  constructor
  · exact Finset.sum_le_sum fun z _ => hlower z
  · calc
      (∑ z ∈ s, (F z : ℝ≥0∞) / D * rho z) ≤
          ∑ z ∈ s, (((A z * w z : Nat) : ℝ≥0∞) / (S * H) +
            ((F z : ℝ≥0∞) / D - (A z : ℝ≥0∞) / S)) :=
        Finset.sum_le_sum fun z _ => hupper z
      _ = _ := by rw [Finset.sum_add_distrib, hresidual]

private theorem sum_union_support_left
    (F A : ToVCVio.IntMeasure) :
    ∑ z ∈ F.coeff.support ∪ A.coeff.support, F z = ToVCVio.totalMass F :=
  (Finset.sum_subset Finset.subset_union_left fun _ _ hz =>
    Finsupp.notMem_support_iff.mp hz).symm

private theorem sum_union_support_right
    (F A : ToVCVio.IntMeasure) :
    ∑ z ∈ F.coeff.support ∪ A.coeff.support, A z = ToVCVio.totalMass A := by
  rw [Finset.union_comm]
  exact sum_union_support_left A F

private theorem sum_union_support_weighted_right
    (F A : ToVCVio.IntMeasure) (w : ℤ → Nat) :
    ∑ z ∈ F.coeff.support ∪ A.coeff.support, A z * w z =
      ∑ z ∈ A.coeff.support, A z * w z :=
  (Finset.sum_subset Finset.subset_union_right fun _ _ hz => by
    rw [Finsupp.notMem_support_iff.mp hz, zero_mul]).symm

theorem probEvent_le_certificate
    (c : Config) (χ : ProbComp ℤ)
    (bad : ℤ → Prop) [DecidablePred bad]
    (hbits : 0 < c.seedBits)
    (hmass : ToVCVio.totalMass (counts c) = 2 ^ c.seedBits)
    (hlaw : ∀ z, Pr{let x ← χ}[x = z] =
      (((ToVCVio.productMeasure (counts c) (counts c)) ^ c.steps * counts c) z : ℝ≥0∞) /
        (2 ^ c.seedBits) ^ (2 * c.steps + 1)) :
    Pr{let z ← χ}[bad z] ≤
      ((certificateValues c (fun z => if bad z then 1 else 0)).1 : ℝ≥0∞) /
        2 ^ (c.precision + c.seedBits) +
      ((certificateValues c (fun z => if bad z then 1 else 0)).2 : ℝ≥0∞) /
        2 ^ c.precision := by
  classical
  let F := (ToVCVio.productMeasure (counts c) (counts c)) ^ c.steps * counts c
  let A := lowerCounts c c.steps * counts c
  let s := F.coeff.support ∪ A.coeff.support
  let w : ℤ → ℕ := fun z => if bad z then 1 else 0
  let rho : ℤ → ℝ≥0∞ := fun z => if bad z then 1 else 0
  have hw : ∀ z, w z ≤ 1 := by intro z; dsimp [w]; split_ifs <;> omega
  have hevent : Pr{let z ← χ}[bad z] =
      ∑ z ∈ s, (F z : ℝ≥0∞) / (2 ^ c.seedBits) ^ (2 * c.steps + 1) * rho z := by
    rw [OracleComp.prEvent_eq_tsum_ite]
    simp_rw [hlaw]
    have hterm (z : ℤ) :
        (if bad z then (F z : ℝ≥0∞) / (2 ^ c.seedBits) ^ (2 * c.steps + 1) else 0) =
          (F z : ℝ≥0∞) / (2 ^ c.seedBits) ^ (2 * c.steps + 1) * rho z := by
      dsimp [rho]; split_ifs <;> simp
    calc
      _ = ∑' z, (F z : ℝ≥0∞) / (2 ^ c.seedBits) ^ (2 * c.steps + 1) * rho z :=
        tsum_congr hterm
      _ = _ := by
        apply tsum_eq_sum
        intro z hz
        have hzF : z ∉ F.coeff.support := fun h => hz (Finset.mem_union_left _ h)
        rw [Finsupp.notMem_support_iff.mp hzF]
        simp
  have hfinite := finite_missingMass_enclosure s F A
    ((2 ^ c.seedBits) ^ (2 * c.steps + 1)) (2 ^ c.seedBits * 2 ^ c.precision)
    1 rho w (by positivity) (by positivity)
    (by rw [sum_union_support_left, totalMass_fullCounts c hmass])
    (approxCounts_domination c)
    (by intro z hz; dsimp [rho, w]; split_ifs <;> simp)
    (by intro z; dsimp [rho]; split_ifs <;> simp)
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, mul_one] at hfinite
  rw [← hevent, sum_union_support_right] at hfinite
  have hweighted :
      (∑ z ∈ s, ((A z * w z : ℕ) : ℝ≥0∞) /
        ((2 : ℝ≥0∞) ^ c.seedBits * 2 ^ c.precision)) =
      ((Finsupp.sum A (fun z a => a * w z) : ℕ) : ℝ≥0∞) /
        (2 ^ c.seedBits * 2 ^ c.precision) := by
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Nat.cast_sum, sum_union_support_weighted_right]
    rfl
  simp only [← Nat.cast_mul] at hfinite
  rw [hweighted] at hfinite
  have hmissingNat :
      2 ^ c.seedBits * 2 ^ c.precision - ToVCVio.totalMass A =
        2 ^ c.seedBits * (2 ^ c.precision - ToVCVio.totalMass (lowerCounts c c.steps)) := by
    rw [show ToVCVio.totalMass A = 2 ^ c.seedBits *
      ToVCVio.totalMass (lowerCounts c c.steps) from totalMass_approxCounts c hmass,
      Nat.mul_sub_left_distrib]
  have hmissing :
      ((2 ^ c.seedBits * 2 ^ c.precision - ToVCVio.totalMass A : ℕ) : ℝ≥0∞) /
        (2 ^ c.seedBits * 2 ^ c.precision) =
      ((2 ^ c.precision - ToVCVio.totalMass (lowerCounts c c.steps) : ℕ) : ℝ≥0∞) /
        2 ^ c.precision := by
    rw [hmissingNat]
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    exact ENNReal.mul_div_mul_left _ _ (by positivity) (by simp)
  rw [certificateValues_eq c w hbits hmass hw]
  dsimp only
  calc
    _ ≤ ((Finsupp.sum A (fun z a => a * w z) : ℕ) : ℝ≥0∞) /
        (2 ^ c.seedBits * 2 ^ c.precision) +
        ((2 ^ c.seedBits * 2 ^ c.precision - ToVCVio.totalMass A : ℕ) : ℝ≥0∞) /
          (2 ^ c.seedBits * 2 ^ c.precision) := hfinite.2
    _ = _ := by
      rw [hmissing]
      rw [pow_add, mul_comm (2 ^ c.precision) (2 ^ c.seedBits)]

end FailureCertificate.RoundedConvolution

