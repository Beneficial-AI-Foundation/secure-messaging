/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Sampling
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

/-!
# Original Frodo recommended parameters and D3 sampling

The historical Recommended row in Table 2 of the original Frodo paper fixes the dimensions and
modulus parameters below. Claim 3.2 gives the strict reconciliation radius `512`, using the width
defined in Section 3.2. Table 1 gives the signed D3 weights.

The repeated-value decoder models exactly that source distribution by mapping a uniform
`Fin 4096` seed to one of eleven signed integers. It does not model the paper implementation's bit
ordering, memory access, or timing. This file states no moment, tail, or concrete CKA failure bound.
-/

open OracleComp ENNReal
open scoped BigOperators

namespace lweCKA

/-- The original Frodo paper's historical Recommended parameter row. -/
def recommendedParams : Params :=
  { n := 752, nbar := 8, logQ := 15, keyBits := 4 }

/-- The signed integer weights of the original Frodo D3 distribution. -/
def d3Weight (z : ℤ) : ℕ :=
  match z.natAbs with
  | 0 => 1206
  | 1 => 919
  | 2 => 406
  | 3 => 104
  | 4 => 15
  | 5 => 1
  | _ => 0

private def d3Values : List ℤ :=
  List.replicate 1206 0 ++
    List.replicate 919 1 ++ List.replicate 919 (-1) ++
    List.replicate 406 2 ++ List.replicate 406 (-2) ++
    List.replicate 104 3 ++ List.replicate 104 (-3) ++
    List.replicate 15 4 ++ List.replicate 15 (-4) ++
    List.replicate 1 5 ++ List.replicate 1 (-5)

private theorem d3Values_length :
    d3Values.length = 4096 := by
  norm_num [d3Values]

private def d3Table : List.Vector ℤ 4096 :=
  ⟨d3Values, d3Values_length⟩

/-- Decode a uniform twelve-bit seed using the repeated-value D3 table. -/
def d3Value (u : Fin 4096) : ℤ :=
  d3Table.get u

/-- Sample the exact signed D3 integer distribution from a uniform seed. -/
def d3IntSampler : ProbComp ℤ :=
  d3Value <$> ($ᵗ (Fin 4096) : ProbComp (Fin 4096))

/-- Cast the signed D3 draw into the scalar ring used by the recommended parameters. -/
def d3Sampler : ProbComp (Scalar recommendedParams) :=
  (fun z : ℤ => (z : Scalar recommendedParams)) <$> d3IntSampler

private theorem d3Values_count (z : ℤ) :
    d3Values.count z = d3Weight z := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · by_cases hn : n ≤ 5
    · interval_cases n <;>
        norm_num [d3Values, d3Weight, List.count_append, List.count_replicate]
    · have hn6 : 6 ≤ n := by omega
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn6
      have hweight : d3Weight (↑(k + 6) : ℤ) = 0 := by
        change (match (↑(k + 6) : ℤ).natAbs with
          | 0 => 1206 | 1 => 919 | 2 => 406 | 3 => 104
          | 4 => 15 | 5 => 1 | _ => 0) = 0
        rw [Int.natAbs_natCast]
        simp
      rw [hweight]
      simp only [d3Values, List.count_append, List.count_replicate, beq_iff_eq]
      norm_num
      all_goals omega
  · by_cases hn : n ≤ 5
    · interval_cases n <;>
        norm_num [d3Values, d3Weight, List.count_append, List.count_replicate]
    · have hn6 : 6 ≤ n := by omega
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn6
      have hweight : d3Weight (-(↑(k + 6) : ℤ)) = 0 := by
        change (match (-(↑(k + 6) : ℤ)).natAbs with
          | 0 => 1206 | 1 => 919 | 2 => 406 | 3 => 104
          | 4 => 15 | 5 => 1 | _ => 0) = 0
        rw [Int.natAbs_neg, Int.natAbs_natCast]
        simp
      rw [hweight]
      simp only [d3Values, List.count_append, List.count_replicate, beq_iff_eq]
      norm_num
      all_goals omega

private theorem d3Weight_pos_iff (z : ℤ) :
    0 < d3Weight z ↔ z ∈ Set.Icc (-5 : ℤ) 5 := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  all_goals
    unfold d3Weight
    split <;> simp_all [Set.mem_Icc]
    all_goals omega

/-- The historical Recommended row satisfies the construction's parameter constraints. -/
theorem recommendedParams_wellFormed :
    recommendedParams.WellFormed := by
  constructor <;> norm_num [recommendedParams]

/-- Claim 3.2's strict reconciliation radius at the Recommended parameters is `512`. -/
theorem recommendedParams_radius :
    2 ^ (recommendedParams.discardBits - 2) = 512 := by
  norm_num [recommendedParams, Params.discardBits]

/-- The eleven signed D3 weights form a distribution with denominator `4096`. -/
theorem sum_d3Weight :
    ∑ z ∈ Finset.Icc (-5 : ℤ) 5, d3Weight z = 4096 := by
  decide

/-- Every decoded D3 integer lies between `-5` and `5`. -/
theorem d3Value_mem_Icc (u : Fin 4096) :
    d3Value u ∈ Set.Icc (-5 : ℤ) 5 := by
  have hmem : d3Value u ∈ d3Values := by
    change d3Values.get (u.cast d3Values_length.symm) ∈ d3Values
    exact List.get_mem _ _
  have hcount : 0 < d3Values.count (d3Value u) := List.count_pos_iff.mpr hmem
  rw [d3Values_count] at hcount
  exact (d3Weight_pos_iff _).mp hcount

/-- Every integer's D3 point mass is its source-table weight divided by `4096`. -/
theorem probOutput_d3IntSampler (z : ℤ) :
    Pr[= z | d3IntSampler] = (d3Weight z : ℝ≥0∞) / 4096 := by
  have hcount : d3Table.toList.count z = d3Weight z := by
    change d3Values.count z = d3Weight z
    exact d3Values_count z
  change Pr[= z | $! d3Table] = (d3Weight z : ℝ≥0∞) / 4096
  rw [ProbComp.probOutput_uniformSelectListVector, hcount]
  norm_num

/-- Uniform seed sampling and deterministic decoding never fail. -/
theorem probFailure_d3IntSampler :
    Pr[⊥ | d3IntSampler] = 0 := by
  simp [d3IntSampler]

/-- The exact support of the signed D3 sampler is the integer interval from `-5` to `5`. -/
theorem support_d3IntSampler :
    support d3IntSampler = Set.Icc (-5 : ℤ) 5 := by
  ext z
  rw [mem_support_iff, probOutput_d3IntSampler]
  simpa [Nat.pos_iff_ne_zero] using d3Weight_pos_iff z

/-- The signed D3 distribution is invariant under integer negation. -/
theorem evalDist_neg_d3IntSampler :
    evalDist ((fun z : ℤ => -z) <$> d3IntSampler) =
      evalDist d3IntSampler := by
  apply evalDist_ext_iff.mpr
  intro z
  calc
    Pr[= z | (fun t : ℤ => -t) <$> d3IntSampler] = Pr[= -z | d3IntSampler] := by
      simpa only [neg_neg] using
        (probOutput_map_injective d3IntSampler (f := fun t : ℤ => -t) neg_injective (-z))
    _ = (d3Weight (-z) : ℝ≥0∞) / 4096 := probOutput_d3IntSampler (-z)
    _ = (d3Weight z : ℝ≥0∞) / 4096 := by simp [d3Weight]
    _ = Pr[= z | d3IntSampler] := (probOutput_d3IntSampler z).symm

/-- Scalar point masses are the finite pushforward of the eleven signed integer masses. -/
theorem probOutput_d3Sampler (x : Scalar recommendedParams) :
    Pr[= x | d3Sampler] =
      ∑ z ∈ Finset.Icc (-5 : ℤ) 5,
        if x = (z : Scalar recommendedParams) then
          (d3Weight z : ℝ≥0∞) / 4096
        else 0 := by
  have hfin : finSupport d3IntSampler = Finset.Icc (-5 : ℤ) 5 := by
    apply (finSupport_eq_iff_support_eq_coe d3IntSampler _).2
    simpa using support_d3IntSampler
  simp only [d3Sampler, probOutput_map_eq_sum_finSupport_ite, hfin,
    probOutput_d3IntSampler]

end lweCKA
