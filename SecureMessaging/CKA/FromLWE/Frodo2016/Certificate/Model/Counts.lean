/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Packing
import SecureMessaging.KEM.MLKEM.Correctness.FailureCertificate.Radix
import VCVio.EvalDist.Expectation
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Nat.Bitwise

/-!
# Count model and packed arithmetic for the historical Frodo parameter sets

The rounded integer measure and its radix implementation are parameterized
here once for all three historical rows. The final domination and missing-mass
enclosure remain in `Certificate.Model`.
-/

open OracleComp OracleComp.EvalDist
open scoped BigOperators ENNReal

namespace lweCKA.Frodo2016.Certificate

namespace SharedModelInternal
end SharedModelInternal

open SharedModelInternal

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

theorem SharedModelInternal.counts_apply_of_mem (c : Config) (z : ℤ)
    (hz : z ∈ Finset.Icc (-(c.a : ℤ)) (c.a : ℤ)) :
    counts c z = c.weight z := by
  classical
  rw [counts, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    Finset.sum_eq_single z]
  · simp
  · intro y hy hne
    simp [hne]
  · exact fun h => (h hz).elim

theorem SharedModelInternal.counts_apply_of_not_mem (c : Config) (z : ℤ)
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

theorem SharedModelInternal.lowerCounts_succ_apply (c : Config) (k : ℕ) (z : ℤ) :
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

theorem SharedModelInternal.measureWindow_lowerCounts (c : Config) (k : ℕ) :
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
  ring_nf

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
      all_goals ring_nf
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

theorem SharedModelInternal.measureWindow_approxCounts (c : Config) (k : ℕ) :
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
      ring_nf
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


end

end lweCKA.Frodo2016.Certificate
