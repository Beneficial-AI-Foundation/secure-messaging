/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Recommended.Sampling

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
  norm_num [d1Values]

private theorem d2Values_length :
    d2Values.length = 4096 := by
  norm_num [d2Values]

private theorem d4Values_length :
    d4Values.length = 65536 := by
  norm_num [d4Values]

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
        norm_num [d1Values, d1Weight, List.count_append, List.count_replicate]
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
        norm_num [d1Values, d1Weight, List.count_append, List.count_replicate]
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
        norm_num [d2Values, d2Weight, List.count_append, List.count_replicate]
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
        norm_num [d2Values, d2Weight, List.count_append, List.count_replicate]
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
        norm_num [d4Values, d4Weight, List.count_append, List.count_replicate]
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
        norm_num [d4Values, d4Weight, List.count_append, List.count_replicate]
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
    Pr[= z | d1IntSampler] = (d1Weight z : ℝ≥0∞) / 256 := by
  have hcount : d1Table.toList.count z = d1Weight z := by
    change d1Values.count z = d1Weight z
    exact d1Values_count z
  change Pr[= z | $! d1Table] = (d1Weight z : ℝ≥0∞) / 256
  rw [ProbComp.probOutput_uniformSelectListVector, hcount]
  norm_num

/-- Every integer's D2 point mass is its source-table weight divided by `4096`. -/
theorem probOutput_d2IntSampler (z : ℤ) :
    Pr[= z | d2IntSampler] = (d2Weight z : ℝ≥0∞) / 4096 := by
  have hcount : d2Table.toList.count z = d2Weight z := by
    change d2Values.count z = d2Weight z
    exact d2Values_count z
  change Pr[= z | $! d2Table] = (d2Weight z : ℝ≥0∞) / 4096
  rw [ProbComp.probOutput_uniformSelectListVector, hcount]
  norm_num

/-- Every integer's D4 point mass is its source-table weight divided by `65536`. -/
theorem probOutput_d4IntSampler (z : ℤ) :
    Pr[= z | d4IntSampler] = (d4Weight z : ℝ≥0∞) / 65536 := by
  have hcount : d4Table.toList.count z = d4Weight z := by
    change d4Values.count z = d4Weight z
    exact d4Values_count z
  change Pr[= z | $! d4Table] = (d4Weight z : ℝ≥0∞) / 65536
  rw [ProbComp.probOutput_uniformSelectListVector, hcount]
  norm_num

/-- The exact support of D1 is the integer interval from `-3` to `3`. -/
theorem support_d1IntSampler :
    support d1IntSampler = Set.Icc (-3 : ℤ) 3 := by
  ext z
  rw [mem_support_iff, probOutput_d1IntSampler]
  simpa [Nat.pos_iff_ne_zero] using d1Weight_pos_iff z

/-- The exact support of D2 is the integer interval from `-4` to `4`. -/
theorem support_d2IntSampler :
    support d2IntSampler = Set.Icc (-4 : ℤ) 4 := by
  ext z
  rw [mem_support_iff, probOutput_d2IntSampler]
  simpa [Nat.pos_iff_ne_zero] using d2Weight_pos_iff z

/-- The exact support of D4 is the integer interval from `-6` to `6`. -/
theorem support_d4IntSampler :
    support d4IntSampler = Set.Icc (-6 : ℤ) 6 := by
  ext z
  rw [mem_support_iff, probOutput_d4IntSampler]
  simpa [Nat.pos_iff_ne_zero] using d4Weight_pos_iff z

end lweCKA
