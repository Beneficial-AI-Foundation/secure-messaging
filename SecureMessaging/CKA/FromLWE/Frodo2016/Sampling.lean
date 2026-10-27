/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Sampling
import VCVio.OracleComp.Constructions.UniformSelectMeasure
import VCVio.OracleComp.EvalDist.Sum

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
  simp only [d3Values, List.length_append, List.length_replicate]

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
        simp only [d3Values, List.count_append, List.count_replicate, beq_iff_eq]
        <;> norm_num [d3Weight]
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
        simp only [d3Values, List.count_append, List.count_replicate, beq_iff_eq]
        <;> norm_num [d3Weight]
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
    Pr{let x ← d3IntSampler}[x = z] = (d3Weight z : ℝ≥0∞) / 4096 := by
  have hcount : d3Table.toList.count z = d3Weight z := by
    change d3Values.count z = d3Weight z
    exact d3Values_count z
  change Pr{let x ← $! d3Table}[x = z] = (d3Weight z : ℝ≥0∞) / 4096
  rw [uniformSelectListVector_mass, hcount]
  norm_num

/-- Uniform seed sampling and deterministic decoding never fail. -/
theorem probFailure_d3IntSampler :
    prFail d3IntSampler = 0 := by
  simp [d3IntSampler]

/-- The exact support of the signed D3 sampler is the integer interval from `-5` to `5`. -/
theorem support_d3IntSampler :
    support d3IntSampler = Set.Icc (-5 : ℤ) 5 := by
  ext z
  rw [OracleComp.mem_support_iff_prEvent_ne_zero, probOutput_d3IntSampler]
  simpa [Nat.pos_iff_ne_zero] using d3Weight_pos_iff z

/-- The signed D3 distribution is invariant under integer negation. -/
theorem evalDist_neg_d3IntSampler :
    finiteLaw ((fun z : ℤ => -z) <$> d3IntSampler) =
      finiteLaw d3IntSampler := by
  apply EvalDistEq.evalDist_eq
  apply OracleComp.evalDistEq_of_forall_prEvent_eq_output
  intro z
  calc
    Pr{let x ← (fun t : ℤ => -t) <$> d3IntSampler}[x = z] = Pr{let x ← d3IntSampler}[x = -z] := by
      simpa only [neg_neg] using
        (prEvent_map_injective d3IntSampler (f := fun t : ℤ => -t) neg_injective (-z))
    _ = (d3Weight (-z) : ℝ≥0∞) / 4096 := probOutput_d3IntSampler (-z)
    _ = (d3Weight z : ℝ≥0∞) / 4096 := by simp [d3Weight]
    _ = Pr{let x ← d3IntSampler}[x = z] := (probOutput_d3IntSampler z).symm

/-- Scalar point masses are the finite pushforward of the eleven signed integer masses. -/
theorem probOutput_d3Sampler (x : Scalar recommendedParams) :
    Pr{let y ← d3Sampler}[y = x] =
      ∑ z ∈ Finset.Icc (-5 : ℤ) 5,
        if x = (z : Scalar recommendedParams) then
          (d3Weight z : ℝ≥0∞) / 4096
        else 0 := by
  have hfin : finSupport d3IntSampler = Finset.Icc (-5 : ℤ) 5 := by
    apply (finSupport_eq_iff_support_eq_coe d3IntSampler _).2
    simpa using support_d3IntSampler
  rw [d3Sampler, prEvent_map, OracleComp.prEvent_eq_tsum_ite]
  rw [tsum_eq_sum (s := Finset.Icc (-5 : ℤ) 5)]
  · apply Finset.sum_congr rfl
    intro z hz
    rw [probOutput_d3IntSampler]
    simp only [eq_comm]
  · intro z hz
    have hzero : Pr{let x ← d3IntSampler}[x = z] = 0 := by
      apply prEvent_eq_zero_of_not_mem_support
      simpa [support_d3IntSampler] using hz
    simp [hzero]

end lweCKA

/-!
# Original Frodo historical parameters and exact sampling

Tables 1 and 2 of the original Frodo paper give four parameter rows and four discrete noise
distributions. `Frodo2016/Recommended/Sampling.lean` covers the Recommended row and D3.
This file covers the remaining Challenge/D1, Classical/D2, and Paranoid/D4 rows.

Each repeated-value decoder maps a uniform seed of the source-specified bit width to the signed
integer masses in Table 1. It models that probability distribution exactly. It does not model the
implementation's bit ordering, CDF scan, memory access, or timing. The definitions and proofs here
make no claim about the paper's concrete security or numerical failure estimates.

Source: Bos, Costello, Ducas, Mironov, Naehrig, Nikolaenko, Raghunathan, and Stebila,
*Frodo: Take off the ring! Practical, Quantum-Secure Key Exchange from LWE*, CCS 2016,
Tables 1 and 2.
-/

open OracleComp ENNReal
open scoped BigOperators

namespace lweCKA

/-- The original Frodo paper's historical Challenge parameter row. -/
def challengeParams : Params :=
  { n := 352, nbar := 8, logQ := 11, keyBits := 1 }

/-- The original Frodo paper's historical Classical parameter row. -/
def classicalParams : Params :=
  { n := 592, nbar := 8, logQ := 12, keyBits := 2 }

/-- The original Frodo paper's historical Paranoid parameter row. -/
def paranoidParams : Params :=
  { n := 864, nbar := 8, logQ := 15, keyBits := 4 }

/-- The signed integer weights of the original Frodo D1 distribution. -/
def d1Weight (z : ℤ) : ℕ :=
  match z.natAbs with
  | 0 => 88
  | 1 => 61
  | 2 => 20
  | 3 => 3
  | _ => 0

/-- The signed integer weights of the original Frodo D2 distribution. -/
def d2Weight (z : ℤ) : ℕ :=
  match z.natAbs with
  | 0 => 1570
  | 1 => 990
  | 2 => 248
  | 3 => 24
  | 4 => 1
  | _ => 0

/-- The signed integer weights of the original Frodo D4 distribution. -/
def d4Weight (z : ℤ) : ℕ :=
  match z.natAbs with
  | 0 => 19304
  | 1 => 14700
  | 2 => 6490
  | 3 => 1659
  | 4 => 245
  | 5 => 21
  | 6 => 1
  | _ => 0

private def d1Values : List ℤ :=
  List.replicate 88 0 ++
    List.replicate 61 1 ++ List.replicate 61 (-1) ++
    List.replicate 20 2 ++ List.replicate 20 (-2) ++
    List.replicate 3 3 ++ List.replicate 3 (-3)

private def d2Values : List ℤ :=
  List.replicate 1570 0 ++
    List.replicate 990 1 ++ List.replicate 990 (-1) ++
    List.replicate 248 2 ++ List.replicate 248 (-2) ++
    List.replicate 24 3 ++ List.replicate 24 (-3) ++
    List.replicate 1 4 ++ List.replicate 1 (-4)

private def d4Values : List ℤ :=
  List.replicate 19304 0 ++
    List.replicate 14700 1 ++ List.replicate 14700 (-1) ++
    List.replicate 6490 2 ++ List.replicate 6490 (-2) ++
    List.replicate 1659 3 ++ List.replicate 1659 (-3) ++
    List.replicate 245 4 ++ List.replicate 245 (-4) ++
    List.replicate 21 5 ++ List.replicate 21 (-5) ++
    List.replicate 1 6 ++ List.replicate 1 (-6)

private theorem d1Values_length :
    d1Values.length = 256 := by
  simp only [d1Values, List.length_append, List.length_replicate]

private theorem d2Values_length :
    d2Values.length = 4096 := by
  simp only [d2Values, List.length_append, List.length_replicate]

private theorem d4Values_length :
    d4Values.length = 65536 := by
  simp only [d4Values, List.length_append, List.length_replicate]

private def d1Table : List.Vector ℤ 256 :=
  ⟨d1Values, d1Values_length⟩

private def d2Table : List.Vector ℤ 4096 :=
  ⟨d2Values, d2Values_length⟩

private def d4Table : List.Vector ℤ 65536 :=
  ⟨d4Values, d4Values_length⟩

/-- Decode a uniform eight-bit seed using the repeated-value D1 table. -/
def d1Value (u : Fin 256) : ℤ :=
  d1Table.get u

/-- Decode a uniform twelve-bit seed using the repeated-value D2 table. -/
def d2Value (u : Fin 4096) : ℤ :=
  d2Table.get u

/-- Decode a uniform sixteen-bit seed using the repeated-value D4 table. -/
def d4Value (u : Fin 65536) : ℤ :=
  d4Table.get u

/-- Sample the exact signed D1 integer distribution from a uniform seed. -/
def d1IntSampler : ProbComp ℤ :=
  d1Value <$> ($ᵗ (Fin 256) : ProbComp (Fin 256))

/-- Sample the exact signed D2 integer distribution from a uniform seed. -/
def d2IntSampler : ProbComp ℤ :=
  d2Value <$> ($ᵗ (Fin 4096) : ProbComp (Fin 4096))

/-- Sample the exact signed D4 integer distribution from a uniform seed. -/
def d4IntSampler : ProbComp ℤ :=
  d4Value <$> ($ᵗ (Fin 65536) : ProbComp (Fin 65536))

/-- Cast a signed D1 draw into the scalar ring used by the Challenge parameters. -/
def d1Sampler : ProbComp (Scalar challengeParams) :=
  (fun z : ℤ => (z : Scalar challengeParams)) <$> d1IntSampler

/-- Cast a signed D2 draw into the scalar ring used by the Classical parameters. -/
def d2Sampler : ProbComp (Scalar classicalParams) :=
  (fun z : ℤ => (z : Scalar classicalParams)) <$> d2IntSampler

/-- Cast a signed D4 draw into the scalar ring used by the Paranoid parameters. -/
def d4Sampler : ProbComp (Scalar paranoidParams) :=
  (fun z : ℤ => (z : Scalar paranoidParams)) <$> d4IntSampler

private theorem d1Values_count (z : ℤ) :
    d1Values.count z = d1Weight z := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · by_cases hn : n ≤ 3
    · interval_cases n <;>
        simp only [d1Values, List.count_append, List.count_replicate, beq_iff_eq]
        <;> norm_num [d1Weight]
    · have hn4 : 4 ≤ n := by omega
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn4
      have hweight : d1Weight (↑(k + 4) : ℤ) = 0 := by
        change (match (↑(k + 4) : ℤ).natAbs with
          | 0 => 88 | 1 => 61 | 2 => 20 | 3 => 3 | _ => 0) = 0
        rw [Int.natAbs_natCast]
        simp
      rw [hweight]
      simp only [d1Values, List.count_append, List.count_replicate, beq_iff_eq]
      norm_num
      all_goals omega
  · by_cases hn : n ≤ 3
    · interval_cases n <;>
        simp only [d1Values, List.count_append, List.count_replicate, beq_iff_eq]
        <;> norm_num [d1Weight]
    · have hn4 : 4 ≤ n := by omega
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn4
      have hweight : d1Weight (-(↑(k + 4) : ℤ)) = 0 := by
        change (match (-(↑(k + 4) : ℤ)).natAbs with
          | 0 => 88 | 1 => 61 | 2 => 20 | 3 => 3 | _ => 0) = 0
        rw [Int.natAbs_neg, Int.natAbs_natCast]
        simp
      rw [hweight]
      simp only [d1Values, List.count_append, List.count_replicate, beq_iff_eq]
      norm_num
      all_goals omega

private theorem d2Values_count (z : ℤ) :
    d2Values.count z = d2Weight z := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · by_cases hn : n ≤ 4
    · interval_cases n <;>
        simp only [d2Values, List.count_append, List.count_replicate, beq_iff_eq]
        <;> norm_num [d2Weight]
    · have hn5 : 5 ≤ n := by omega
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn5
      have hweight : d2Weight (↑(k + 5) : ℤ) = 0 := by
        change (match (↑(k + 5) : ℤ).natAbs with
          | 0 => 1570 | 1 => 990 | 2 => 248 | 3 => 24 | 4 => 1 | _ => 0) = 0
        rw [Int.natAbs_natCast]
        simp
      rw [hweight]
      simp only [d2Values, List.count_append, List.count_replicate, beq_iff_eq]
      norm_num
      all_goals omega
  · by_cases hn : n ≤ 4
    · interval_cases n <;>
        simp only [d2Values, List.count_append, List.count_replicate, beq_iff_eq]
        <;> norm_num [d2Weight]
    · have hn5 : 5 ≤ n := by omega
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn5
      have hweight : d2Weight (-(↑(k + 5) : ℤ)) = 0 := by
        change (match (-(↑(k + 5) : ℤ)).natAbs with
          | 0 => 1570 | 1 => 990 | 2 => 248 | 3 => 24 | 4 => 1 | _ => 0) = 0
        rw [Int.natAbs_neg, Int.natAbs_natCast]
        simp
      rw [hweight]
      simp only [d2Values, List.count_append, List.count_replicate, beq_iff_eq]
      norm_num
      all_goals omega

private theorem d4Values_count (z : ℤ) :
    d4Values.count z = d4Weight z := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · by_cases hn : n ≤ 6
    · interval_cases n <;>
        simp only [d4Values, List.count_append, List.count_replicate, beq_iff_eq]
        <;> norm_num [d4Weight]
    · have hn7 : 7 ≤ n := by omega
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn7
      have hweight : d4Weight (↑(k + 7) : ℤ) = 0 := by
        change (match (↑(k + 7) : ℤ).natAbs with
          | 0 => 19304 | 1 => 14700 | 2 => 6490 | 3 => 1659
          | 4 => 245 | 5 => 21 | 6 => 1 | _ => 0) = 0
        rw [Int.natAbs_natCast]
        simp
      rw [hweight]
      simp only [d4Values, List.count_append, List.count_replicate, beq_iff_eq]
      norm_num
      all_goals omega
  · by_cases hn : n ≤ 6
    · interval_cases n <;>
        simp only [d4Values, List.count_append, List.count_replicate, beq_iff_eq]
        <;> norm_num [d4Weight]
    · have hn7 : 7 ≤ n := by omega
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn7
      have hweight : d4Weight (-(↑(k + 7) : ℤ)) = 0 := by
        change (match (-(↑(k + 7) : ℤ)).natAbs with
          | 0 => 19304 | 1 => 14700 | 2 => 6490 | 3 => 1659
          | 4 => 245 | 5 => 21 | 6 => 1 | _ => 0) = 0
        rw [Int.natAbs_neg, Int.natAbs_natCast]
        simp
      rw [hweight]
      simp only [d4Values, List.count_append, List.count_replicate, beq_iff_eq]
      norm_num
      all_goals omega

private theorem d1Weight_pos_iff (z : ℤ) :
    0 < d1Weight z ↔ z ∈ Set.Icc (-3 : ℤ) 3 := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  all_goals
    unfold d1Weight
    split <;> simp_all [Set.mem_Icc]
    all_goals omega

private theorem d2Weight_pos_iff (z : ℤ) :
    0 < d2Weight z ↔ z ∈ Set.Icc (-4 : ℤ) 4 := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  all_goals
    unfold d2Weight
    split <;> simp_all [Set.mem_Icc]
    all_goals omega

private theorem d4Weight_pos_iff (z : ℤ) :
    0 < d4Weight z ↔ z ∈ Set.Icc (-6 : ℤ) 6 := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  all_goals
    unfold d4Weight
    split <;> simp_all [Set.mem_Icc]
    all_goals omega

/-- The historical Challenge row satisfies the construction's parameter constraints. -/
theorem challengeParams_wellFormed :
    challengeParams.WellFormed := by
  constructor <;> norm_num [challengeParams]

/-- The historical Classical row satisfies the construction's parameter constraints. -/
theorem classicalParams_wellFormed :
    classicalParams.WellFormed := by
  constructor <;> norm_num [classicalParams]

/-- The historical Paranoid row satisfies the construction's parameter constraints. -/
theorem paranoidParams_wellFormed :
    paranoidParams.WellFormed := by
  constructor <;> norm_num [paranoidParams]

/-- Every integer's D1 point mass is its source-table weight divided by `256`. -/
theorem probOutput_d1IntSampler (z : ℤ) :
    Pr{let x ← d1IntSampler}[x = z] = (d1Weight z : ℝ≥0∞) / 256 := by
  have hcount : d1Table.toList.count z = d1Weight z := by
    change d1Values.count z = d1Weight z
    exact d1Values_count z
  change Pr{let x ← $! d1Table}[x = z] = (d1Weight z : ℝ≥0∞) / 256
  rw [uniformSelectListVector_mass, hcount]
  norm_num

/-- Every integer's D2 point mass is its source-table weight divided by `4096`. -/
theorem probOutput_d2IntSampler (z : ℤ) :
    Pr{let x ← d2IntSampler}[x = z] = (d2Weight z : ℝ≥0∞) / 4096 := by
  have hcount : d2Table.toList.count z = d2Weight z := by
    change d2Values.count z = d2Weight z
    exact d2Values_count z
  change Pr{let x ← $! d2Table}[x = z] = (d2Weight z : ℝ≥0∞) / 4096
  rw [uniformSelectListVector_mass, hcount]
  norm_num

/-- Every integer's D4 point mass is its source-table weight divided by `65536`. -/
theorem probOutput_d4IntSampler (z : ℤ) :
    Pr{let x ← d4IntSampler}[x = z] = (d4Weight z : ℝ≥0∞) / 65536 := by
  have hcount : d4Table.toList.count z = d4Weight z := by
    change d4Values.count z = d4Weight z
    exact d4Values_count z
  change Pr{let x ← $! d4Table}[x = z] = (d4Weight z : ℝ≥0∞) / 65536
  rw [uniformSelectListVector_mass, hcount]
  norm_num

/-- The exact support of D1 is the integer interval from `-3` to `3`. -/
theorem support_d1IntSampler :
    support d1IntSampler = Set.Icc (-3 : ℤ) 3 := by
  ext z
  rw [OracleComp.mem_support_iff_prEvent_ne_zero, probOutput_d1IntSampler]
  simpa [Nat.pos_iff_ne_zero] using d1Weight_pos_iff z

/-- The exact support of D2 is the integer interval from `-4` to `4`. -/
theorem support_d2IntSampler :
    support d2IntSampler = Set.Icc (-4 : ℤ) 4 := by
  ext z
  rw [OracleComp.mem_support_iff_prEvent_ne_zero, probOutput_d2IntSampler]
  simpa [Nat.pos_iff_ne_zero] using d2Weight_pos_iff z

/-- The exact support of D4 is the integer interval from `-6` to `6`. -/
theorem support_d4IntSampler :
    support d4IntSampler = Set.Icc (-6 : ℤ) 6 := by
  ext z
  rw [OracleComp.mem_support_iff_prEvent_ne_zero, probOutput_d4IntSampler]
  simpa [Nat.pos_iff_ne_zero] using d4Weight_pos_iff z

end lweCKA
