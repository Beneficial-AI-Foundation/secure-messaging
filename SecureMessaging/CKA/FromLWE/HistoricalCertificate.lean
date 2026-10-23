/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.PhaseCorrectness
import SecureMessaging.CKA.FromLWE.ChallengeCertificatePacking
import SecureMessaging.KEM.MLKEM.Correctness.FailureCertificate.Radix
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Nat.Bitwise

/-!
# Shared certificates for the historical Frodo parameter sets

The rounded integer measure, its radix implementation, and the missing-mass
argument are parameterized here once for all three historical rows.
-/

open OracleComp OracleComp.EvalDist
open scoped BigOperators ENNReal

namespace lweCKA.HistoricalCertificate

set_option Elab.async false in
section

/-- The data needed by the shared historical failure certificate. -/
structure Config where
  /-- Matrix dimension used by the entry-noise recurrence. -/
  n : ℕ
  /-- Radius of the centered source distribution's support. -/
  a : ℕ
  /-- Bit width of the uniform seed for one source sample. -/
  seedBits : ℕ
  /-- Half-width retained after each rounded convolution step. -/
  window : ℕ
  /-- Radius used by the reconciliation-failure ramp. -/
  radius : ℕ
  /-- Exact source-table count at an integer point. -/
  weight : ℤ → ℕ

/-- The exact counting measure of one centered sample. -/
noncomputable def counts (c : Config) : ToVCVio.IntMeasure :=
  ∑ z ∈ Finset.Icc (-(c.a : ℤ)) (c.a : ℤ),
    AddMonoidAlgebra.single z (c.weight z)

/-- The cropped, downward-rounded measure used by the certificate. -/
noncomputable def lowerCounts (c : Config) : ℕ → ToVCVio.IntMeasure
  | 0 => AddMonoidAlgebra.single 0 (2 ^ 128)
  | k + 1 => ∑ z ∈ Finset.Icc (-(c.window : ℤ)) (c.window : ℤ),
      AddMonoidAlgebra.single z
        (((lowerCounts c k * ToVCVio.productMeasure (counts c) (counts c)) z) /
          2 ^ (2 * c.seedBits))

/-- The two natural-number outputs of the packed recurrence. -/
def certificateValues (c : Config) : ℕ × ℕ :=
  let b := 129 + 2 * c.seedBits
  let R := 2 ^ b
  let productPack :=
    (List.range (2 * c.a + 1)).foldl (fun acc (i : ℕ) =>
      (List.range (2 * c.a + 1)).foldl (fun acc (j : ℕ) =>
        let x := (i : ℤ) - c.a
        let y := (j : ℤ) - c.a
        acc + c.weight x * c.weight y *
          R ^ (x * y + (c.a : ℤ) ^ 2).toNat) acc) 0
  let extraPack :=
    (List.range (2 * c.a + 1)).foldl (fun acc (i : ℕ) =>
      acc + c.weight ((i : ℤ) - c.a) * R ^ i) 0
  let repunit := (List.range (2 * c.window + 1)).foldl
    (fun acc _ => acc * R + 1) 0
  let mask := (2 ^ 129 - 1) * repunit
  let step := fun x : ℕ =>
    ((x * productPack) >>> (c.a ^ 2 * b + 2 * c.seedBits)) &&& mask
  let run := (List.range (2 * c.n)).foldl
    (fun x _ => step x) (2 ^ 128 * R ^ c.window)
  let M := c.window + c.a
  let weightPack := (List.range (2 * M + 1)).foldl (fun acc i =>
    acc * R + min (2 * c.radius)
      ((if i ≤ M then M - i else i - M) - c.radius)) 0
  (((run * extraPack * weightPack) >>> (b * (2 * M))) % R,
    2 ^ 128 - run % (R - 1))

private theorem counts_apply_of_mem (c : Config) (z : ℤ)
    (hz : z ∈ Finset.Icc (-(c.a : ℤ)) (c.a : ℤ)) :
    counts c z = c.weight z := by
  classical
  rw [counts, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    Finset.sum_eq_single z]
  · simp
  · intro y hy hne
    simp [hne]
  · exact fun h => (h hz).elim

private theorem counts_apply_of_not_mem (c : Config) (z : ℤ)
    (hz : z ∉ Finset.Icc (-(c.a : ℤ)) (c.a : ℤ)) :
    counts c z = 0 := by
  classical
  rw [counts, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro y hy
  have hne : y ≠ z := fun h => hz (h ▸ hy)
  simp [hne]

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
  classical
  rw [lowerCounts, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  by_cases hz : z ∈ Finset.Icc (-(c.window : ℤ)) (c.window : ℤ)
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

private theorem measureWindow_lowerCounts (c : Config) (k : ℕ) :
    ToVCVio.MeasureWindow (lowerCounts c k)
      (-(c.window : ℤ)) (c.window : ℤ) := by
  cases k with
  | zero =>
      intro z hz
      simp only [lowerCounts, AddMonoidAlgebra.coeff_single,
        Finsupp.single_apply] at hz
      split at hz
      · omega
      · simp at hz
  | succ k =>
      intro z hz
      rw [lowerCounts_succ_apply c k z] at hz
      split at hz
      · simpa only [Finset.mem_Icc] using
          (show z ∈ Finset.Icc (-(c.window : ℤ)) (c.window : ℤ) from ‹_›)
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
        intro hs
        exact hz (Finset.mem_inter.mpr ⟨hzs, hs⟩)
      exact Finsupp.notMem_support_iff.mp hnot
    _ ≤ ∑ z ∈ F.coeff.support, F z :=
      Finset.sum_le_sum_of_subset Finset.inter_subset_right
    _ = ToVCVio.totalMass F := by rfl

private theorem totalMass_lowerCounts_le
    (c : Config) (hmass : ToVCVio.totalMass (counts c) = 2 ^ c.seedBits)
    (k : ℕ) :
    ToVCVio.totalMass (lowerCounts c k) ≤ 2 ^ 128 := by
  induction k with
  | zero => rw [lowerCounts, ToVCVio.totalMass_single]
  | succ k ih =>
      let D2 := 2 ^ (2 * c.seedBits)
      have hD2 : D2 = ToVCVio.totalMass
          (ToVCVio.productMeasure (counts c) (counts c)) := by
        rw [ToVCVio.totalMass_productMeasure, hmass, ← pow_two, ← pow_mul,
          Nat.mul_comm c.seedBits 2]
      have hwindow : ToVCVio.MeasureWindow (lowerCounts c (k + 1))
          (-(c.window : ℤ)) (-(c.window : ℤ) + (2 * c.window + 1 : ℕ) - 1) := by
        convert measureWindow_lowerCounts c (k + 1) using 1
        all_goals omega
      have hscaled : D2 * ToVCVio.totalMass (lowerCounts c (k + 1)) ≤
          D2 * 2 ^ 128 := by
        calc
          D2 * ToVCVio.totalMass (lowerCounts c (k + 1)) =
              ∑ i ∈ Finset.range (2 * c.window + 1),
                D2 * ((lowerCounts c k *
                  ToVCVio.productMeasure (counts c) (counts c))
                    (-(c.window : ℤ) + i) / D2) := by
            rw [MLKEM.totalMass_eq_range_sum hwindow, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [lowerCounts_succ_apply]
            simp only [Finset.mem_Icc]
            rw [if_pos (by have hi := Finset.mem_range.mp hi; omega)]
          _ ≤ ∑ i ∈ Finset.range (2 * c.window + 1),
                (lowerCounts c k * ToVCVio.productMeasure (counts c) (counts c))
                  (-(c.window : ℤ) + i) := by
            exact Finset.sum_le_sum fun i _ => by
              simpa [Nat.mul_comm] using Nat.div_mul_le_self
                ((lowerCounts c k * ToVCVio.productMeasure (counts c) (counts c))
                  (-(c.window : ℤ) + i)) D2
          _ ≤ ToVCVio.totalMass
                (lowerCounts c k * ToVCVio.productMeasure (counts c) (counts c)) := by
            let s : Finset ℤ := (Finset.range (2 * c.window + 1)).image
              (fun i : Nat => -(c.window : ℤ) + i)
            have hinj : Function.Injective (fun i : Nat => -(c.window : ℤ) + i) := by
              intro i j h
              exact_mod_cast Int.add_left_cancel h
            rw [show (∑ i ∈ Finset.range (2 * c.window + 1),
                (lowerCounts c k * ToVCVio.productMeasure (counts c) (counts c))
                  (-(c.window : ℤ) + i)) =
                ∑ z ∈ s, (lowerCounts c k *
                  ToVCVio.productMeasure (counts c) (counts c)) z by
                  unfold s
                  rw [Finset.sum_image hinj.injOn]]
            exact finsetSum_apply_le_totalMass _ _
          _ = ToVCVio.totalMass (lowerCounts c k) * D2 := by
            rw [ToVCVio.totalMass_mul, ← hD2]
          _ ≤ D2 * 2 ^ 128 := by
            simpa [Nat.mul_comm] using Nat.mul_le_mul_right D2 ih
      have hD2pos : 0 < D2 := by unfold D2; positivity
      exact le_of_mul_le_mul_left (by simpa [Nat.mul_comm] using hscaled) hD2pos

private theorem productCoefficient_lt_radix
    (c : Config) (hmass : ToVCVio.totalMass (counts c) = 2 ^ c.seedBits)
    (k : ℕ) (z : ℤ) :
    (lowerCounts c k * ToVCVio.productMeasure (counts c) (counts c)) z <
      2 ^ (129 + 2 * c.seedBits) := by
  calc
    _ ≤ ToVCVio.totalMass
        (lowerCounts c k * ToVCVio.productMeasure (counts c) (counts c)) :=
      finsetSum_apply_le_totalMass _ {z}
    _ = ToVCVio.totalMass (lowerCounts c k) *
        ToVCVio.totalMass (ToVCVio.productMeasure (counts c) (counts c)) := by
      rw [ToVCVio.totalMass_mul]
    _ ≤ 2 ^ 128 * 2 ^ (2 * c.seedBits) := by
      rw [ToVCVio.totalMass_productMeasure, hmass, ← pow_two, ← pow_mul,
        Nat.mul_comm c.seedBits 2]
      exact Nat.mul_le_mul_right _ (totalMass_lowerCounts_le c hmass k)
    _ < 2 ^ (129 + 2 * c.seedBits) := by
      rw [← pow_add]
      exact Nat.pow_lt_pow_right (by omega) (by omega)

private theorem foldl_range_add_eq_sum (n : ℕ) (f : ℕ → ℕ) (x : ℕ) :
    (List.range n).foldl (fun acc i => acc + f i) x =
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
    constructor <;> omega
  · rintro ⟨hlo, hhi⟩
    refine ⟨(z + a).toNat, ?_, ?_⟩
    · omega
    · omega

private theorem counts_apply_index (c : Config) (i : ℕ)
    (hi : i < 2 * c.a + 1) :
    counts c ((i : ℤ) - c.a) = c.weight ((i : ℤ) - c.a) := by
  apply counts_apply_of_mem
  simp only [Finset.mem_Icc]
  omega

private theorem extraPack_eq_measurePack (c : Config) :
    (List.range (2 * c.a + 1)).foldl (fun acc (i : ℕ) =>
      acc + c.weight ((i : ℤ) - c.a) *
        (2 ^ (129 + 2 * c.seedBits) : ℕ) ^ i) 0 =
      MLKEM.measurePack (2 ^ (129 + 2 * c.seedBits)) (-(c.a : ℤ)) (counts c) := by
  rw [MLKEM.measurePack_eq_range_sum
    (show ToVCVio.MeasureWindow (counts c)
        (-(c.a : ℤ)) (-(c.a : ℤ) + (2 * c.a + 1 : ℕ) - 1) by
      convert measureWindow_counts c using 1
      all_goals push_cast
      all_goals omega)]
  rw [foldl_range_add_eq_sum, zero_add]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [show -(c.a : ℤ) + i = (i : ℤ) - c.a by ring,
    counts_apply_index c i (Finset.mem_range.mp hi)]

/-- Bit width of one coefficient in the packed recurrence. -/
def bits (c : Config) : ℕ := 129 + 2 * c.seedBits

/-- Radix used to pack recurrence coefficients. -/
def radix (c : Config) : ℕ := 2 ^ bits c

/-- Packed coefficient table for the product of two source measures. -/
def productPack (c : Config) : ℕ :=
  (List.range (2 * c.a + 1)).foldl (fun acc (i : ℕ) =>
    (List.range (2 * c.a + 1)).foldl (fun acc (j : ℕ) =>
      let x := (i : ℤ) - c.a
      let y := (j : ℤ) - c.a
      acc + c.weight x * c.weight y *
        radix c ^ ((x * y + (c.a : ℤ) ^ 2).toNat)) acc) 0

/-- Packed coefficient table for one source measure. -/
def extraPack (c : Config) : ℕ :=
  (List.range (2 * c.a + 1)).foldl (fun acc (i : ℕ) =>
    acc + c.weight ((i : ℤ) - c.a) * radix c ^ i) 0

/-- Packed value with one in every retained coefficient lane. -/
def repunit (c : Config) : ℕ :=
  (List.range (2 * c.window + 1)).foldl
    (fun acc _ => acc * radix c + 1) 0

/-- Mask retaining the low 129 bits of every packed coefficient lane. -/
def mask (c : Config) : ℕ := (2 ^ 129 - 1) * repunit c

/-- One cropped, downward-rounded step of the packed recurrence. -/
def step (c : Config) (x : ℕ) : ℕ :=
  ((x * productPack c) >>>
      (c.a ^ 2 * bits c + 2 * c.seedBits)) &&& mask c

/-- Packed recurrence value after the configured number of steps. -/
def run (c : Config) : ℕ :=
  (List.range (2 * c.n)).foldl (fun x _ => step c x)
    (2 ^ 128 * radix c ^ c.window)

/-- Center index of the final product with one source measure. -/
def center (c : Config) : ℕ := c.window + c.a

/-- Packed reconciliation-ramp weights for the final coefficient interval. -/
def weightPack (c : Config) : ℕ :=
  (List.range (2 * center c + 1)).foldl (fun acc i =>
    acc * radix c + min (2 * c.radius)
      ((if i ≤ center c then center c - i else i - center c) - c.radius)) 0

/-- Internal definitional decomposition used by the fixed-row arithmetic bridges. -/
theorem certificateValues_eq_components (c : Config) :
    certificateValues c =
      (((run c * extraPack c * weightPack c) >>>
          (bits c * (2 * center c))) % radix c,
        2 ^ 128 - run c % (radix c - 1)) := by
  rfl

private theorem extraPack_eq_measurePack' (c : Config) :
    extraPack c = MLKEM.measurePack (radix c) (-(c.a : ℤ)) (counts c) := by
  simpa only [extraPack, radix, bits] using extraPack_eq_measurePack c

private theorem repunit_eq_sum (c : Config) :
    repunit c = ∑ i ∈ Finset.range (2 * c.window + 1), radix c ^ i := by
  unfold repunit
  exact ChallengeCertificatePacking.foldl_range_mul_add_one_eq_pack
    (radix c) (2 * c.window + 1)

private theorem mask_eq_sum (c : Config) :
    mask c = (2 ^ (bits c - 2 * c.seedBits) - 1) *
      ∑ i ∈ Finset.range (2 * c.window + 1),
        (2 ^ bits c) ^ i := by
  rw [mask, repunit_eq_sum]
  simp only [radix, bits]
  rw [show 129 + 2 * c.seedBits - 2 * c.seedBits = 129 by omega]

private theorem counts_eq_indexed_sum (c : Config) :
    counts c = ∑ i ∈ Finset.range (2 * c.a + 1),
      AddMonoidAlgebra.single ((i : ℤ) - c.a) (c.weight ((i : ℤ) - c.a)) := by
  rw [counts, ← rangeImage_eq_Icc]
  rw [Finset.sum_image]
  intro i _ j _ h
  have hz : (i : ℤ) = (j : ℤ) := sub_left_injective h
  exact_mod_cast hz

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

private theorem measurePack_zero (R : ℕ) (lo : ℤ) :
    MLKEM.measurePack R lo 0 = 0 := by
  exact Finsupp.sum_zero_index

private theorem measurePack_add (R : ℕ) (lo : ℤ)
    (F G : ToVCVio.IntMeasure) :
    MLKEM.measurePack R lo (F + G) =
      MLKEM.measurePack R lo F + MLKEM.measurePack R lo G := by
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) fun _ _ _ => add_mul _ _ _

private theorem measurePack_finset_sum
    {ι : Type} (R : ℕ) (lo : ℤ)
    (s : Finset ι) (F : ι → ToVCVio.IntMeasure) :
    MLKEM.measurePack R lo (∑ i ∈ s, F i) =
      ∑ i ∈ s, MLKEM.measurePack R lo (F i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [measurePack_zero]
  | cons a s ha ih => simp [ha, measurePack_add, ih]

private theorem productPack_eq_measurePack (c : Config) :
    productPack c = MLKEM.measurePack (radix c) (-((c.a : ℤ) ^ 2))
      (ToVCVio.productMeasure (counts c) (counts c)) := by
  unfold productPack
  simp_rw [foldl_range_add_eq_sum]
  simp only [zero_add]
  rw [productMeasure_counts_eq_sum, measurePack_finset_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [measurePack_finset_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [MLKEM.measurePack_single]
  congr 2
  ring

private def runN (c : Config) (k : ℕ) : ℕ :=
  (List.range k).foldl (fun x _ => step c x)
    (2 ^ 128 * radix c ^ c.window)

private theorem run_eq_runN (c : Config) : run c = runN c (2 * c.n) := rfl

private theorem runN_succ (c : Config) (k : ℕ) :
    runN c (k + 1) = step c (runN c k) := by
  rw [runN, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

private theorem measurePack_lowerCounts_zero (c : Config) :
    MLKEM.measurePack (radix c) (-(c.window : ℤ)) (lowerCounts c 0) =
      2 ^ 128 * radix c ^ c.window := by
  rw [lowerCounts, MLKEM.measurePack_single]
  congr 2
  omega

private theorem measurePack_lowerCounts_mod_pred
    (c : Config) (hbits : 0 < c.seedBits)
    (hmass : ToVCVio.totalMass (counts c) = 2 ^ c.seedBits) (k : ℕ) :
    MLKEM.measurePack (radix c) (-(c.window : ℤ)) (lowerCounts c k) %
        (radix c - 1) = ToVCVio.totalMass (lowerCounts c k) := by
  apply ChallengeCertificatePacking.measurePack_mod_pred_eq_totalMass
    (n := 2 * c.window + 1)
  · convert measureWindow_lowerCounts c k using 1
    all_goals push_cast
    all_goals omega
  · calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (129 + 2 * c.seedBits) :=
        Nat.pow_le_pow_right (by omega) (by omega)
  · have hle := totalMass_lowerCounts_le c hmass k
    have hpow : 2 ^ 129 ≤ radix c := by
      apply Nat.pow_le_pow_right (by omega)
      simp only [bits]
      omega
    have hgap : 2 ^ 128 < 2 ^ 129 - 1 := by norm_num
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
    MLKEM.measurePack (radix c) (-(c.window : ℤ)) (lowerCounts c (k + 1)) =
      ∑ i ∈ Finset.range (2 * c.window + 1),
        ((lowerCounts c k * ToVCVio.productMeasure (counts c) (counts c))
          (-(c.window : ℤ) + i) / 2 ^ (2 * c.seedBits)) * radix c ^ i := by
  rw [MLKEM.measurePack_eq_range_sum
    (show ToVCVio.MeasureWindow (lowerCounts c (k + 1))
        (-(c.window : ℤ))
        (-(c.window : ℤ) + (2 * c.window + 1 : ℕ) - 1) by
      convert measureWindow_lowerCounts c (k + 1) using 1
      all_goals push_cast
      all_goals omega)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [lowerCounts_succ_apply, if_pos]
  simpa only [Finset.mem_Icc] using
    (show -(c.window : ℤ) ≤ -(c.window : ℤ) + (i : ℤ) ∧
        -(c.window : ℤ) + (i : ℤ) ≤ c.window by
      have := Finset.mem_range.mp hi
      omega)

private theorem measurePack_lower_product_sum (c : Config) (k : ℕ) :
    MLKEM.measurePack (radix c) (-((c.window : ℤ) + (c.a : ℤ) ^ 2))
        (lowerCounts c k * ToVCVio.productMeasure (counts c) (counts c)) =
      ∑ i ∈ Finset.range (2 * (c.window + c.a ^ 2) + 1),
        (lowerCounts c k * ToVCVio.productMeasure (counts c) (counts c))
          (-((c.window : ℤ) + (c.a : ℤ) ^ 2) + i) * radix c ^ i := by
  apply MLKEM.measurePack_eq_range_sum
  convert measureWindow_lower_product c k using 1
  all_goals push_cast
  all_goals ring_nf

private theorem measurePack_lower_product_mul (c : Config) (k : ℕ) :
    MLKEM.measurePack (radix c) (-((c.window : ℤ) + (c.a : ℤ) ^ 2))
        (lowerCounts c k * ToVCVio.productMeasure (counts c) (counts c)) =
      MLKEM.measurePack (radix c) (-(c.window : ℤ)) (lowerCounts c k) *
        productPack c := by
  calc
    _ = MLKEM.measurePack (radix c) (-(c.window : ℤ)) (lowerCounts c k) *
        MLKEM.measurePack (radix c) (-((c.a : ℤ) ^ 2))
          (ToVCVio.productMeasure (counts c) (counts c)) := by
      convert MLKEM.measurePack_mul (R := radix c)
        (measureWindow_lowerCounts c k) (measureWindow_products c) using 1
      all_goals ring
    _ = _ := by rw [← productPack_eq_measurePack]

private theorem packed_crop_step (c : Config) (f : ℕ → ℕ)
    (hf : ∀ i < 2 * (c.window + c.a ^ 2) + 1, f i < radix c) :
    (((∑ i ∈ Finset.range (2 * (c.window + c.a ^ 2) + 1),
          f i * radix c ^ i) >>>
        (c.a ^ 2 * bits c + 2 * c.seedBits)) &&& mask c) =
      ∑ i ∈ Finset.range (2 * c.window + 1),
        (f (c.a ^ 2 + i) / 2 ^ (2 * c.seedBits)) * radix c ^ i := by
  have h := ChallengeCertificatePacking.packed_bitSlice
    (b := bits c) (k := c.a ^ 2) (t := 2 * c.seedBits)
    (n := 2 * c.window + 1) (m := 2 * (c.window + c.a ^ 2) + 1)
    (by simp [bits]) (by simp [bits]) (by omega) f (by simpa [radix] using hf)
  simpa only [radix, mask_eq_sum,
    show bits c - 2 * c.seedBits = 129 by simp [bits],
    show c.a ^ 2 * bits c + 2 * c.seedBits =
      bits c * c.a ^ 2 + 2 * c.seedBits by ring] using h

private theorem measurePack_lowerCounts_succ
    (c : Config) (hmass : ToVCVio.totalMass (counts c) = 2 ^ c.seedBits)
    (k : ℕ) :
    MLKEM.measurePack (radix c) (-(c.window : ℤ)) (lowerCounts c (k + 1)) =
      step c (MLKEM.measurePack (radix c) (-(c.window : ℤ)) (lowerCounts c k)) := by
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
    MLKEM.measurePack (radix c) (-(c.window : ℤ)) (lowerCounts c k) =
      runN c k := by
  induction k with
  | zero => exact measurePack_lowerCounts_zero c
  | succ k ih => rw [measurePack_lowerCounts_succ c hmass k, ih, ← runN_succ]

private theorem indexWeight_eq (c : Config) (i : ℕ) :
    min (2 * c.radius)
        ((-(center c : ℤ) + (i : ℤ)).natAbs - c.radius) =
      min (2 * c.radius)
        ((if i ≤ center c then center c - i else i - center c) - c.radius) := by
  congr 2
  rw [show -(center c : ℤ) + (i : ℤ) = (i : ℤ) - center c by ring]
  by_cases hi : i ≤ center c
  · rw [Int.natAbs_natCast_sub_natCast_of_le hi, if_pos hi]
  · rw [Int.natAbs_natCast_sub_natCast_of_ge (by omega), if_neg hi]

private theorem indexedWeight_le_center (c : Config) (i : ℕ)
    (hi : i < 2 * center c + 1) :
    min (2 * c.radius)
        ((-(center c : ℤ) + (i : ℤ)).natAbs - c.radius) ≤ center c := by
  rw [indexWeight_eq]
  apply (min_le_right _ _).trans
  split_ifs <;> omega

private theorem weightPack_eq_sum (c : Config) :
    weightPack c =
      ∑ i ∈ Finset.range (2 * center c + 1),
        min (2 * c.radius)
          ((-(center c : ℤ) + ((2 * center c + 1 - 1 - i : Nat) : ℤ)).natAbs -
            c.radius) * radix c ^ i := by
  rw [weightPack, ChallengeCertificatePacking.foldl_range_mul_add_eq_reversePack]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [indexWeight_eq]

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
      2 ^ 128 * 2 ^ c.seedBits := by
  rw [ToVCVio.totalMass_mul, hmass]
  exact Nat.mul_le_mul_right _ (totalMass_lowerCounts_le c hmass k)

private theorem measurePack_approxCounts
    (c : Config) (hmass : ToVCVio.totalMass (counts c) = 2 ^ c.seedBits) :
    MLKEM.measurePack (radix c) (-(center c : ℤ))
        (lowerCounts c (2 * c.n) * counts c) =
      run c * extraPack c := by
  calc
    _ = MLKEM.measurePack (radix c) (-(c.window : ℤ))
          (lowerCounts c (2 * c.n)) *
        MLKEM.measurePack (radix c) (-(c.a : ℤ)) (counts c) := by
      convert MLKEM.measurePack_mul (R := radix c)
        (measureWindow_lowerCounts c (2 * c.n)) (measureWindow_counts c) using 1
      simp only [center, Nat.cast_add]
      ring
    _ = run c * extraPack c := by
      rw [measurePack_lowerCounts_runN c hmass, ← run_eq_runN,
        ← extraPack_eq_measurePack']

private theorem weightedMass_eq_packExtract
    (c : Config) (hmass : ToVCVio.totalMass (counts c) = 2 ^ c.seedBits)
    (hpack : c.window + c.a < 2 ^ (c.seedBits + 1)) :
    Finsupp.sum (lowerCounts c (2 * c.n) * counts c)
        (fun (z : ℤ) (m : Nat) =>
          m * min (2 * c.radius) (z.natAbs - c.radius)) =
      MLKEM.measurePack (radix c) (-(center c : ℤ))
          (lowerCounts c (2 * c.n) * counts c) * weightPack c /
            radix c ^ (2 * center c) % radix c := by
  let A := lowerCounts c (2 * c.n) * counts c
  have hwindow : ToVCVio.MeasureWindow A
      (-(center c : ℤ)) (-(center c : ℤ) + (2 * center c + 1 : ℕ) - 1) := by
    convert measureWindow_approxCounts c (2 * c.n) using 1
    all_goals push_cast
    all_goals omega
  have hsum :
      ∑ i ∈ Finset.range (2 * center c + 1), A (-(center c : ℤ) + i) =
        ToVCVio.totalMass A :=
    (MLKEM.totalMass_eq_range_sum hwindow).symm
  have hcarry : center c *
      ∑ i ∈ Finset.range (2 * center c + 1), A (-(center c : ℤ) + i) <
        radix c := by
    rw [hsum]
    calc
      center c * ToVCVio.totalMass A ≤
          center c * (2 ^ 128 * 2 ^ c.seedBits) :=
        Nat.mul_le_mul_left _ (totalMass_approxCounts_le c hmass (2 * c.n))
      _ < 2 ^ (c.seedBits + 1) * (2 ^ 128 * 2 ^ c.seedBits) :=
        Nat.mul_lt_mul_of_pos_right (by simpa only [center] using hpack) (by positivity)
      _ = radix c := by
        simp only [radix, bits]
        rw [← pow_add, ← pow_add]
        congr 1
        omega
  have hdot := ChallengeCertificatePacking.dot_eq_pack_extract_bound
    (R := radix c) (q := 2 * center c + 1) (B := center c) (by omega)
    (fun i => A (-(center c : ℤ) + i))
    (fun i => min (2 * c.radius)
      ((-(center c : ℤ) + (i : ℤ)).natAbs - c.radius))
    (indexedWeight_le_center c) hcarry
  rw [← MLKEM.measurePack_eq_range_sum hwindow, ← weightPack_eq_sum] at hdot
  rw [ChallengeCertificatePacking.finsuppWeightedSum_eq_range_sum A
    (-(center c : ℤ)) (2 * center c + 1)
    (fun z => min (2 * c.radius) (z.natAbs - c.radius)) hwindow]
  simpa only [show 2 * center c + 1 - 1 = 2 * center c by omega] using hdot

private theorem shift_extract_eq_div
    (x e w r k n : Nat) (hr : r = 2 ^ k) :
    ((x * e * w) >>> (k * n)) % r =
      (x * e * w / r ^ n) % r := by
  rw [Nat.shiftRight_eq_div_pow, pow_mul, ← hr]

/-- The packed recurrence equals its semantic rounded count and missing-mass pair. -/
theorem certificateValues_eq_counts
    (c : Config) (hbits : 0 < c.seedBits)
    (hmass : ToVCVio.totalMass (counts c) = 2 ^ c.seedBits)
    (hpack : c.window + c.a < 2 ^ (c.seedBits + 1)) :
    certificateValues c =
      (let A := lowerCounts c (2 * c.n) * counts c
       ∑ z ∈ A.coeff.support,
         A z * min (2 * c.radius) (z.natAbs - c.radius),
       2 ^ 128 - ToVCVio.totalMass (lowerCounts c (2 * c.n))) := by
  rw [certificateValues_eq_components]
  dsimp only
  apply Prod.ext_iff.mpr
  constructor
  · have hweighted := weightedMass_eq_packExtract c hmass hpack
    rw [measurePack_approxCounts c hmass] at hweighted
    rw [shift_extract_eq_div _ _ _ (radix c) (bits c) (2 * center c)
      (by rfl)]
    exact hweighted.symm
  · rw [← measurePack_lowerCounts_mod_pred c hbits hmass (2 * c.n),
      measurePack_lowerCounts_runN c hmass, ← run_eq_runN]

private theorem counts_neg (c : Config)
    (hsym : ∀ z : ℤ, c.weight (-z) = c.weight z) (z : ℤ) :
    counts c (-z) = counts c z := by
  by_cases hz : z ∈ Finset.Icc (-(c.a : ℤ)) (c.a : ℤ)
  · have hnz : -z ∈ Finset.Icc (-(c.a : ℤ)) (c.a : ℤ) := by
      simpa only [Finset.mem_Icc] using
        (show -(c.a : ℤ) ≤ -z ∧ -z ≤ c.a by
          have := Finset.mem_Icc.mp hz
          omega)
    rw [counts_apply_of_mem c (-z) hnz, counts_apply_of_mem c z hz, hsym]
  · have hnz : -z ∉ Finset.Icc (-(c.a : ℤ)) (c.a : ℤ) := by
      intro h
      apply hz
      simpa only [Finset.mem_Icc] using
        (show -(c.a : ℤ) ≤ z ∧ z ≤ c.a by
          have := Finset.mem_Icc.mp h
          omega)
    rw [counts_apply_of_not_mem c (-z) hnz, counts_apply_of_not_mem c z hz]

private def productExp (χ : ProbComp ℤ) : ProbComp ℤ := do
  let x ← χ
  let y ← χ
  return x * y

private def negProductExp (χ : ProbComp ℤ) : ProbComp ℤ := do
  let x ← (-·) <$> χ
  let y ← χ
  return x * y

private theorem probOutput_mul_counts
    (mx my : ProbComp ℤ) (F G : ToVCVio.IntMeasure) (D E : Nat)
    (hmx : ∀ z, Pr[= z | mx] = (F z : ℝ≥0∞) / D)
    (hmy : ∀ z, Pr[= z | my] = (G z : ℝ≥0∞) / E)
    (z : ℤ) :
    Pr[= z | (fun x y : ℤ => x * y) <$> mx <*> my] =
      (ToVCVio.productMeasure F G z : ℝ≥0∞) / (D * E) := by
  rw [probOutput_seq_map_eq_tsum_ite]
  rw [tsum_eq_sum (s := F.coeff.support)]
  · have hinner (x : ℤ) :
        (∑' y : ℤ, if z = x * y then Pr[= x | mx] * Pr[= y | my] else 0) =
          ∑ y ∈ G.coeff.support,
            if z = x * y then Pr[= x | mx] * Pr[= y | my] else 0 := by
      rw [tsum_eq_sum (s := G.coeff.support)]
      intro y hy
      have hzero : G y = 0 := Finsupp.notMem_support_iff.mp hy
      simp [hmy, hzero]
    simp_rw [hinner, hmx, hmy]
    rw [ToVCVio.productMeasure_apply]
    simp only [Finsupp.sum]
    push_cast
    simp only [div_eq_mul_inv]
    have hinv : ((D : ℝ≥0∞) * E)⁻¹ =
        (D : ℝ≥0∞)⁻¹ * (E : ℝ≥0∞)⁻¹ :=
      ENNReal.mul_inv (Or.inr ENNReal.coe_ne_top) (Or.inl ENNReal.coe_ne_top)
    rw [hinv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun y hy => ?_
    by_cases hxy : z = x * y
    · rw [if_pos hxy, if_pos hxy.symm]
      ac_rfl
    · rw [if_neg hxy, if_neg (fun h => hxy h.symm)]
      simp only [zero_mul]
  · intro x hx
    have hzero : F x = 0 := Finsupp.notMem_support_iff.mp hx
    simp [hmx, hzero]

private theorem probOutput_productExp
    (c : Config) (χ : ProbComp ℤ)
    (hlaw : ∀ z : ℤ, Pr[= z | χ] = (counts c z : ℝ≥0∞) / 2 ^ c.seedBits)
    (z : ℤ) :
    Pr[= z | productExp χ] =
      (ToVCVio.productMeasure (counts c) (counts c) z : ℝ≥0∞) /
        (2 ^ c.seedBits) ^ 2 := by
  have hlawNat (u : ℤ) :
      Pr[= u | χ] =
        (counts c u : ℝ≥0∞) / (((2 ^ c.seedBits : Nat) : ℝ≥0∞)) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hlaw u
  simpa only [productExp, map_eq_bind_pure_comp, seq_eq_bind_map,
    Function.comp_def, bind_assoc, pure_bind, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, pow_two] using
    probOutput_mul_counts χ χ (counts c) (counts c)
      (2 ^ c.seedBits) (2 ^ c.seedBits) hlawNat hlawNat z

private theorem probOutput_neg_map
    (c : Config) (χ : ProbComp ℤ)
    (hlaw : ∀ z : ℤ, Pr[= z | χ] = (counts c z : ℝ≥0∞) / 2 ^ c.seedBits)
    (hsym : ∀ z : ℤ, c.weight (-z) = c.weight z) (z : ℤ) :
    Pr[= z | (-·) <$> χ] = (counts c z : ℝ≥0∞) / 2 ^ c.seedBits := by
  calc
    Pr[= z | (-·) <$> χ] = Pr[= -z | χ] := by
      convert probOutput_map_injective χ (fun _ _ h => neg_inj.mp h) (-z) using 1
      all_goals simp
    _ = (counts c (-z) : ℝ≥0∞) / 2 ^ c.seedBits := hlaw (-z)
    _ = (counts c z : ℝ≥0∞) / 2 ^ c.seedBits := by rw [counts_neg c hsym]

private theorem probOutput_negProductExp
    (c : Config) (χ : ProbComp ℤ)
    (hlaw : ∀ z : ℤ, Pr[= z | χ] = (counts c z : ℝ≥0∞) / 2 ^ c.seedBits)
    (hsym : ∀ z : ℤ, c.weight (-z) = c.weight z) (z : ℤ) :
    Pr[= z | negProductExp χ] =
      (ToVCVio.productMeasure (counts c) (counts c) z : ℝ≥0∞) /
        (2 ^ c.seedBits) ^ 2 := by
  have hnegNat (u : ℤ) :
      Pr[= u | (-·) <$> χ] =
        (counts c u : ℝ≥0∞) / (((2 ^ c.seedBits : Nat) : ℝ≥0∞)) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      probOutput_neg_map c χ hlaw hsym u
  have hlawNat (u : ℤ) :
      Pr[= u | χ] =
        (counts c u : ℝ≥0∞) / (((2 ^ c.seedBits : Nat) : ℝ≥0∞)) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hlaw u
  simpa only [negProductExp, map_eq_bind_pure_comp, seq_eq_bind_map,
    Function.comp_def, bind_assoc, pure_bind, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, pow_two] using
    probOutput_mul_counts ((-·) <$> χ) χ (counts c) (counts c)
      (2 ^ c.seedBits) (2 ^ c.seedBits)
      hnegNat hlawNat z

private theorem probOutput_add_counts
    (mx my : ProbComp ℤ) (F G : ToVCVio.IntMeasure) (D E : Nat)
    (hmx : ∀ z, Pr[= z | mx] = (F z : ℝ≥0∞) / D)
    (hmy : ∀ z, Pr[= z | my] = (G z : ℝ≥0∞) / E)
    (z : ℤ) :
    Pr[= z | (fun x y : ℤ => x + y) <$> mx <*> my] =
      ((F * G) z : ℝ≥0∞) / (D * E) := by
  rw [probOutput_seq_map_eq_tsum_ite]
  have hinner (x : ℤ) :
      (∑' y : ℤ, if z = x + y then Pr[= x | mx] * Pr[= y | my] else 0) =
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
        (D : ℝ≥0∞)⁻¹ * (E : ℝ≥0∞)⁻¹ :=
      ENNReal.mul_inv (Or.inr ENNReal.coe_ne_top) (Or.inl ENNReal.coe_ne_top)
    rw [hinv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [show -x + z = z - x by ring]
    ac_rfl
  · intro x hx
    have hzero : F x = 0 := Finsupp.notMem_support_iff.mp hx
    simp [hmx, hzero]

private def differenceBlock (χ : ProbComp ℤ) : ProbComp ℤ := do
  let s0 ← χ
  let e0 ← χ
  let s1 ← χ
  let e1 ← χ
  return s1 * e0 - e1 * s0

private theorem evalDist_differenceBlock_grouped (χ : ProbComp ℤ) :
    evalDist (differenceBlock χ) =
      evalDist ((fun x y : ℤ => x + y) <$> productExp χ <*> negProductExp χ) := by
  simp only [differenceBlock, productExp, negProductExp,
    map_eq_bind_pure_comp, seq_eq_bind_map, Function.comp_apply, bind_assoc, pure_bind]
  calc
    _ = evalDist (do
          let e0 ← χ
          let s0 ← χ
          let s1 ← χ
          let e1 ← χ
          return s1 * e0 - e1 * s0) := evalDist_bind_bind_swap _ _ _
    _ = evalDist (do
          let e0 ← χ
          let s1 ← χ
          let s0 ← χ
          let e1 ← χ
          return s1 * e0 - e1 * s0) := by
        refine evalDist_bind_congr' χ fun _ => ?_
        exact evalDist_bind_bind_swap _ _ _
    _ = evalDist (do
          let s1 ← χ
          let e0 ← χ
          let s0 ← χ
          let e1 ← χ
          return s1 * e0 - e1 * s0) := evalDist_bind_bind_swap _ _ _
    _ = evalDist (do
          let s1 ← χ
          let e0 ← χ
          let e1 ← χ
          let s0 ← χ
          return s1 * e0 - e1 * s0) := by
        refine evalDist_bind_congr' χ fun _ => ?_
        refine evalDist_bind_congr' χ fun _ => ?_
        exact evalDist_bind_bind_swap _ _ _
    _ = _ := by
      refine evalDist_bind_congr' χ fun s1 => ?_
      refine evalDist_bind_congr' χ fun e0 => ?_
      refine evalDist_bind_congr' χ fun e1 => ?_
      refine evalDist_bind_congr' χ fun s0 => ?_
      simp only [evalDist_pure]
      congr 1
      ring

private theorem probOutput_differenceBlock
    (c : Config) (χ : ProbComp ℤ)
    (hlaw : ∀ z : ℤ, Pr[= z | χ] = (counts c z : ℝ≥0∞) / 2 ^ c.seedBits)
    (hsym : ∀ z : ℤ, c.weight (-z) = c.weight z) (z : ℤ) :
    Pr[= z | differenceBlock χ] =
      (((ToVCVio.productMeasure (counts c) (counts c)) ^ 2) z : ℝ≥0∞) /
        (2 ^ c.seedBits) ^ 4 := by
  rw [(evalDist_ext_iff.mp (evalDist_differenceBlock_grouped χ)) z]
  have hprodNat (u : ℤ) :
      Pr[= u | productExp χ] =
        (ToVCVio.productMeasure (counts c) (counts c) u : ℝ≥0∞) /
          ((((2 ^ c.seedBits) ^ 2 : Nat) : ℝ≥0∞)) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      probOutput_productExp c χ hlaw u
  have hnegProdNat (u : ℤ) :
      Pr[= u | negProductExp χ] =
        (ToVCVio.productMeasure (counts c) (counts c) u : ℝ≥0∞) /
          ((((2 ^ c.seedBits) ^ 2 : Nat) : ℝ≥0∞)) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      probOutput_negProductExp c χ hlaw hsym u
  have h := probOutput_add_counts (productExp χ) (negProductExp χ)
    (ToVCVio.productMeasure (counts c) (counts c))
    (ToVCVio.productMeasure (counts c) (counts c))
    ((2 ^ c.seedBits) ^ 2) ((2 ^ c.seedBits) ^ 2)
    hprodNat hnegProdNat z
  have hden : (2 : ℝ≥0∞) ^
        (c.seedBits + c.seedBits + (c.seedBits + c.seedBits)) =
      ((2 : ℝ≥0∞) ^ c.seedBits) ^ 4 := by
    rw [← pow_mul]
    congr 1
    omega
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_two, ← pow_add,
    hden] using h

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
    _ = _ := evalDist_bind_congr' mb fun _ => evalDist_bind_bind_swap ma mc _

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

private theorem evalDist_entryNoiseIntExp_succ (n : ℕ) (χ : ProbComp ℤ) :
    evalDist (entryNoiseIntExp (n + 1) χ) =
      evalDist (do
        let rest ← entryNoiseIntExp n χ
        let delta ← differenceBlock χ
        return rest + delta) := by
  let tail : ProbComp (Fin n → ℤ) := Fin.mOfFn n fun _ => χ
  let finish (s0 : ℤ) (s0s : Fin n → ℤ) (e0 : ℤ) (e0s : Fin n → ℤ)
      (s1 : ℤ) (s1s : Fin n → ℤ) (e1 : ℤ) (e1s : Fin n → ℤ)
      (extra : ℤ) : ProbComp ℤ :=
    pure ((∑ k, Fin.cons s1 s1s k * Fin.cons e0 e0s k) -
      (∑ k, Fin.cons e1 e1s k * Fin.cons s0 s0s k) + extra)
  simp only [entryNoiseIntExp, differenceBlock, ProbComp.sampleIID,
    Fin.mOfFn, bind_assoc, pure_bind]
  change evalDist (do
      let s0 ← χ
      let s0s ← tail
      let e0 ← χ
      let e0s ← tail
      let s1 ← χ
      let s1s ← tail
      let e1 ← χ
      let e1s ← tail
      let extra ← χ
      finish s0 s0s e0 e0s s1 s1s e1 e1s extra) = _
  calc
    _ = evalDist (do
          let s0s ← tail
          let e0s ← tail
          let s1s ← tail
          let e1s ← tail
          let extra ← χ
          let s0 ← χ
          let e0 ← χ
          let s1 ← χ
          let e1 ← χ
          finish s0 s0s e0 e0s s1 s1s e1 e1s extra) :=
        evalDist_bind_rotate_four_heads χ tail χ tail χ tail χ tail χ finish
    _ = _ := by
      refine evalDist_bind_congr' tail fun s0s => ?_
      refine evalDist_bind_congr' tail fun e0s => ?_
      refine evalDist_bind_congr' tail fun s1s => ?_
      refine evalDist_bind_congr' tail fun e1s => ?_
      refine evalDist_bind_congr' χ fun extra => ?_
      refine evalDist_bind_congr' χ fun s0 => ?_
      refine evalDist_bind_congr' χ fun e0 => ?_
      refine evalDist_bind_congr' χ fun s1 => ?_
      refine evalDist_bind_congr' χ fun e1 => ?_
      simp only [finish, evalDist_pure]
      congr 1
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      ring

private theorem probOutput_entryNoiseIntExp_counts
    (c : Config) (χ : ProbComp ℤ)
    (hlaw : ∀ z : ℤ, Pr[= z | χ] = (counts c z : ℝ≥0∞) / 2 ^ c.seedBits)
    (hsym : ∀ z : ℤ, c.weight (-z) = c.weight z)
    (n : ℕ) (z : ℤ) :
    Pr[= z | entryNoiseIntExp n χ] =
      (((ToVCVio.productMeasure (counts c) (counts c)) ^ (2 * n) * counts c) z :
          ℝ≥0∞) /
        (2 ^ c.seedBits) ^ (4 * n + 1) := by
  induction n generalizing z with
  | zero =>
      simp [entryNoiseIntExp, ProbComp.sampleIID, Fin.mOfFn, hlaw,
        AddMonoidAlgebra.one_def]
  | succ n ih =>
      rw [(evalDist_ext_iff.mp (evalDist_entryNoiseIntExp_succ n χ)) z]
      rw [show (do
          let rest ← entryNoiseIntExp n χ
          let delta ← differenceBlock χ
          return rest + delta) =
          (fun x y : ℤ => x + y) <$> entryNoiseIntExp n χ <*> differenceBlock χ by
        simp only [map_eq_bind_pure_comp, seq_eq_bind_map,
          Function.comp_def, bind_assoc, pure_bind]]
      have ihNat (u : ℤ) :
          Pr[= u | entryNoiseIntExp n χ] =
            (((ToVCVio.productMeasure (counts c) (counts c)) ^ (2 * n) *
                counts c) u : ℝ≥0∞) /
              (((2 ^ c.seedBits) ^ (4 * n + 1) : Nat) : ℝ≥0∞) := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using ih u
      have hstepNat (u : ℤ) :
          Pr[= u | differenceBlock χ] =
            ((((ToVCVio.productMeasure (counts c) (counts c)) ^ 2) u : ℝ≥0∞) /
              (((2 ^ c.seedBits) ^ 4 : Nat) : ℝ≥0∞)) := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using
          probOutput_differenceBlock c χ hlaw hsym u
      calc
        _ = ((((ToVCVio.productMeasure (counts c) (counts c)) ^ (2 * n) *
                counts c) *
              (ToVCVio.productMeasure (counts c) (counts c)) ^ 2) z : ℝ≥0∞) /
            ((((2 ^ c.seedBits) ^ (4 * n + 1)) *
                (2 ^ c.seedBits) ^ 4 : Nat) : ℝ≥0∞) := by
          simpa only [Nat.cast_mul] using probOutput_add_counts
            (entryNoiseIntExp n χ) (differenceBlock χ)
            ((ToVCVio.productMeasure (counts c) (counts c)) ^ (2 * n) * counts c)
            ((ToVCVio.productMeasure (counts c) (counts c)) ^ 2)
            ((2 ^ c.seedBits) ^ (4 * n + 1)) ((2 ^ c.seedBits) ^ 4)
            ihNat hstepNat z
        _ = (((ToVCVio.productMeasure (counts c) (counts c)) ^ (2 * (n + 1)) *
              counts c) z : ℝ≥0∞) /
            (2 ^ c.seedBits) ^ (4 * (n + 1) + 1) := by
          have hmeasure :
              ((ToVCVio.productMeasure (counts c) (counts c)) ^ (2 * n) *
                  counts c) *
                (ToVCVio.productMeasure (counts c) (counts c)) ^ 2 =
              (ToVCVio.productMeasure (counts c) (counts c)) ^ (2 * (n + 1)) *
                counts c := by
            rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
            ring
          rw [hmeasure]
          simp only [Nat.cast_pow, Nat.cast_ofNat, ← pow_add]
          congr 2

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
        simp [lowerCounts, AddMonoidAlgebra.one_def, hz]
  | succ k ih =>
      let P := ToVCVio.productMeasure (counts c) (counts c)
      by_cases hz : z ∈ Finset.Icc (-(c.window : ℤ)) (c.window : ℤ)
      · rw [lowerCounts_succ_apply, if_pos hz]
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
      · rw [lowerCounts_succ_apply, if_neg hz]
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
      rw [hneg, ZMod.neg_val, if_neg hsub]
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
  · change z * 2 ∈ Set.Ioc (-(p.q : ℤ)) p.q
    simp only [Set.mem_Ioc]
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
    (hlaw : ∀ z : ℤ, Pr[= z | χ] = (counts c z : ℝ≥0∞) / 2 ^ c.seedBits)
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
    (χ : ProbComp ℤ) (hχ : Pr[⊥ | χ] = 0)
    (hn : p.n = c.n) (hr : 2 ^ (p.discardBits - 2) = c.radius)
    (hbits : 0 < c.seedBits)
    (hmass : ToVCVio.totalMass (counts c) = 2 ^ c.seedBits)
    (hlaw : ∀ z : ℤ, Pr[= z | χ] = (counts c z : ℝ≥0∞) / 2 ^ c.seedBits)
    (hsym : ∀ z : ℤ, c.weight (-z) = c.weight z)
    (hwindow : 2 * (c.window + c.a) < p.q)
    (hpack : c.window + c.a < 2 ^ (c.seedBits + 1)) :
    expectedValue (entryNoiseIntExp p.n χ) (reconciliationFailureRamp p) ≤
      ((certificateValues c).1 : ℝ≥0∞) /
        (2 ^ 128 * 2 ^ c.seedBits * (2 * c.radius)) +
      ((certificateValues c).2 : ℝ≥0∞) / 2 ^ 128 := by
  have hχ0 : Pr[⊥ | χ] = 0 := hχ
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

end lweCKA.HistoricalCertificate
