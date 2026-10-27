/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Sampling

/-!
# Exact moments of the Frodo D3 sampler

This file computes the first five raw moments of the signed D3 distribution and connects the
finite rational calculation to the point masses of `d3IntSampler`. The infinite sum is reduced to
the sampler's exact finite support before its coefficients are converted to real numbers.
-/

open OracleComp ENNReal
open scoped BigOperators

namespace lweCKA

/-- The raw moment of order `k` for the signed D3 distribution. -/
noncomputable def d3Moment (k : ℕ) : ℚ :=
  ∑ z ∈ Finset.Icc (-5 : ℤ) 5,
    ((d3Weight z : ℚ) / 4096) * (z : ℚ) ^ k

/-- The D3 weights have total mass one. -/
theorem d3Moment_zero :
    d3Moment 0 = 1 := by
  have hIcc : Finset.Icc (-5 : ℤ) 5 =
      {-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5} := by
    ext z
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [d3Moment, hIcc]
  norm_num [d3Weight]

/-- The signed D3 distribution is centered. -/
theorem d3Moment_one :
    d3Moment 1 = 0 := by
  have hIcc : Finset.Icc (-5 : ℤ) 5 =
      {-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5} := by
    ext z
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [d3Moment, hIcc]
  norm_num [d3Weight]

/-- The second raw D3 moment is `117 / 64`. -/
theorem d3Moment_two :
    d3Moment 2 = 117 / 64 := by
  have hIcc : Finset.Icc (-5 : ℤ) 5 =
      {-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5} := by
    ext z
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [d3Moment, hIcc]
  norm_num [d3Weight]

/-- The third raw D3 moment vanishes by sign symmetry. -/
theorem d3Moment_three :
    d3Moment 3 = 0 := by
  have hIcc : Finset.Icc (-5 : ℤ) 5 =
      {-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5} := by
    ext z
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [d3Moment, hIcc]
  norm_num [d3Weight]

/-- The fourth raw D3 moment is `1269 / 128`. -/
theorem d3Moment_four :
    d3Moment 4 = 1269 / 128 := by
  have hIcc : Finset.Icc (-5 : ℤ) 5 =
      {-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5} := by
    ext z
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [d3Moment, hIcc]
  norm_num [d3Weight]

/-- The rational D3 moment is the raw real moment of the actual integer sampler. -/
theorem tsum_probOutput_d3IntSampler_mul_pow (k : ℕ) :
    (∑' z : ℤ,
      (Pr{let x ← d3IntSampler}[x = z]).toReal * (z : ℝ) ^ k) =
      (d3Moment k : ℝ) := by
  rw [tsum_eq_sum (s := Finset.Icc (-5 : ℤ) 5)]
  · rw [d3Moment, Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [probOutput_d3IntSampler, ENNReal.toReal_div]
    norm_num
  · intro z hz
    have hz' : z ∉ support d3IntSampler := by
      rw [support_d3IntSampler]
      simpa [Set.mem_Icc] using hz
    rw [(prEvent_eq_zero_of_not_mem_support _) hz']
    simp

end lweCKA
