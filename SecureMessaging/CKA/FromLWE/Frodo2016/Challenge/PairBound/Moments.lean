/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Sampling
import VCVio.EvalDist.Expectation
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.BigOperators
import VCVio.EvalDist.Prod
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.NormNum

/-!
# Scalar and IID moment tools for the Frodo Challenge pair bound

This module contains the exact scalar moments, expectation identities, and IID moment tools used
by the integer-coin and joint-tail layers. It also checks the exact rational tail inequalities.
-/

open OracleComp OracleComp.EvalDist
open scoped BigOperators ENNReal

namespace lweCKA

namespace PairBoundInternal

/-- The base `6 / 5` used to exponentiate signed noise in the joint Chernoff estimates. -/
noncomputable def challengeChernoffBase : ℝ≥0∞ := (6 : ℝ≥0∞) / 5

/-- The exact exponential moment of one signed Challenge `D₁` sample. -/
noncomputable def challengeOneMoment : ℝ≥0∞ :=
  (784927 : ℝ≥0∞) / 768000

/-- The exact exponential moment of the product of two independent Challenge `D₁` samples. -/
noncomputable def challengeProductMoment : ℝ≥0∞ :=
  (73796729825894041 : ℝ≥0∞) / 71663616000000000

/-- The exact exponential moment of one shared-coordinate Challenge noise contribution. -/
noncomputable def challengeSharedMoment : ℝ≥0∞ :=
  (127847491742921604065083548949681 : ℝ≥0∞) /
    120367356051456000000000000000000

private lemma d1_support_finset :
    Finset.Icc (-3 : ℤ) 3 = {-3, -2, -1, 0, 1, 2, 3} := by
  ext z
  simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  omega

private theorem expectedValue_d1IntSampler_eq_sum (f : ℤ → ℝ≥0∞) :
    expectedValue d1IntSampler f =
      ∑ z ∈ Finset.Icc (-3 : ℤ) 3,
        ((d1Weight z : ℝ≥0∞) / 256) * f z := by
  rw [expectedValue_def, tsum_eq_sum (s := Finset.Icc (-3 : ℤ) 3)]
  · apply Finset.sum_congr rfl
    intro z _
    rw [probOutput_d1IntSampler]
  · intro z hz
    have hz' : z ∉ support d1IntSampler := by
      rw [support_d1IntSampler]
      simpa [Set.mem_Icc] using hz
    rw [probOutput_eq_zero_of_not_mem_support hz']
    simp

private noncomputable def d1MomentNN (a : ℤ) : NNReal :=
  ∑ z ∈ Finset.Icc (-3 : ℤ) 3,
    ((d1Weight z : NNReal) / 256) * ((6 : NNReal) / 5) ^ (a * z)

private theorem d1MomentNN_neg_three :
    d1MomentNN (-3) =
      (2041700049914041 : NNReal) / 1679616000000000 := by
  rw [d1MomentNN, d1_support_finset]
  norm_num [d1Weight, zpow_neg]

private theorem d1MomentNN_neg_two :
    d1MomentNN (-2) = (67865238961 : NNReal) / 62208000000 := by
  rw [d1MomentNN, d1_support_finset]
  norm_num [d1Weight, zpow_neg]

private theorem d1MomentNN_neg_one :
    d1MomentNN (-1) = (784927 : NNReal) / 768000 := by
  rw [d1MomentNN, d1_support_finset]
  norm_num [d1Weight, zpow_neg]

private theorem d1MomentNN_zero : d1MomentNN 0 = 1 := by
  rw [d1MomentNN, d1_support_finset]
  norm_num [d1Weight]

private theorem d1MomentNN_one :
    d1MomentNN 1 = (784927 : NNReal) / 768000 := by
  rw [d1MomentNN, d1_support_finset]
  norm_num [d1Weight, zpow_neg]

private theorem d1MomentNN_two :
    d1MomentNN 2 = (67865238961 : NNReal) / 62208000000 := by
  rw [d1MomentNN, d1_support_finset]
  norm_num [d1Weight, zpow_neg]

private theorem d1MomentNN_three :
    d1MomentNN 3 =
      (2041700049914041 : NNReal) / 1679616000000000 := by
  rw [d1MomentNN, d1_support_finset]
  norm_num [d1Weight, zpow_neg]

private theorem one_moment_nnreal (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    d1MomentNN σ = (784927 : NNReal) / 768000 := by
  rcases hσ with rfl | rfl
  · exact d1MomentNN_one
  · exact d1MomentNN_neg_one

private theorem product_moment_nnreal (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    (∑ x ∈ Finset.Icc (-3 : ℤ) 3,
      ((d1Weight x : NNReal) / 256) * d1MomentNN (σ * x)) =
        (73796729825894041 : NNReal) / 71663616000000000 := by
  rcases hσ with rfl | rfl <;>
    rw [d1_support_finset] <;>
    norm_num [d1Weight] <;>
    rw [d1MomentNN_neg_three, d1MomentNN_neg_two, d1MomentNN_neg_one,
      d1MomentNN_zero, d1MomentNN_one, d1MomentNN_two, d1MomentNN_three] <;>
    norm_num

private theorem shared_inner_factor (x σ τ : ℤ) :
    (∑ y ∈ Finset.Icc (-3 : ℤ) 3,
      ((d1Weight y : NNReal) / 256) *
        ∑ z ∈ Finset.Icc (-3 : ℤ) 3,
          ((d1Weight z : NNReal) / 256) *
            ((6 : NNReal) / 5) ^ (x * (σ * y + τ * z))) =
      d1MomentNN (σ * x) * d1MomentNN (τ * x) := by
  have hb : (6 : NNReal) / 5 ≠ 0 := by norm_num
  unfold d1MomentNN
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  have hexp : x * (σ * y + τ * z) = σ * x * y + τ * x * z := by ring
  rw [hexp, zpow_add₀ hb]
  ring

private theorem shared_moment_nnreal
    (σ τ : ℤ) (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    (∑ x ∈ Finset.Icc (-3 : ℤ) 3,
      ((d1Weight x : NNReal) / 256) *
        ∑ y ∈ Finset.Icc (-3 : ℤ) 3,
          ((d1Weight y : NNReal) / 256) *
            ∑ z ∈ Finset.Icc (-3 : ℤ) 3,
              ((d1Weight z : NNReal) / 256) *
                ((6 : NNReal) / 5) ^ (x * (σ * y + τ * z))) =
      (127847491742921604065083548949681 : NNReal) /
        120367356051456000000000000000000 := by
  calc
    (∑ x ∈ Finset.Icc (-3 : ℤ) 3,
      ((d1Weight x : NNReal) / 256) *
        ∑ y ∈ Finset.Icc (-3 : ℤ) 3,
          ((d1Weight y : NNReal) / 256) *
            ∑ z ∈ Finset.Icc (-3 : ℤ) 3,
              ((d1Weight z : NNReal) / 256) *
                ((6 : NNReal) / 5) ^ (x * (σ * y + τ * z))) =
        ∑ x ∈ Finset.Icc (-3 : ℤ) 3,
          ((d1Weight x : NNReal) / 256) *
            (d1MomentNN (σ * x) * d1MomentNN (τ * x)) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [shared_inner_factor]
    _ = (127847491742921604065083548949681 : NNReal) /
          120367356051456000000000000000000 := by
      rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;>
        rw [d1_support_finset] <;>
        norm_num [d1Weight] <;>
        rw [d1MomentNN_neg_three, d1MomentNN_neg_two, d1MomentNN_neg_one,
          d1MomentNN_zero, d1MomentNN_one, d1MomentNN_two,
          d1MomentNN_three] <;>
        norm_num

private theorem coe_one_moment_sum (σ : ℤ) :
    (↑(∑ x ∈ Finset.Icc (-3 : ℤ) 3,
      ((d1Weight x : NNReal) / 256) *
        ((6 : NNReal) / 5) ^ (σ * x)) : ℝ≥0∞) =
      ∑ x ∈ Finset.Icc (-3 : ℤ) 3,
        ((d1Weight x : ℝ≥0∞) / 256) *
          (↑(((6 : NNReal) / 5) ^ (σ * x)) : ℝ≥0∞) := by
  simp only [ENNReal.ofNNReal_finsetSum, ENNReal.coe_mul,
    ENNReal.coe_div (by norm_num : (256 : NNReal) ≠ 0), ENNReal.coe_natCast,
    ENNReal.coe_ofNat]

private theorem coe_product_moment_sum (σ : ℤ) :
    (↑(∑ x ∈ Finset.Icc (-3 : ℤ) 3,
      ((d1Weight x : NNReal) / 256) *
        ∑ y ∈ Finset.Icc (-3 : ℤ) 3,
          ((d1Weight y : NNReal) / 256) *
            ((6 : NNReal) / 5) ^ (σ * (x * y))) : ℝ≥0∞) =
      ∑ x ∈ Finset.Icc (-3 : ℤ) 3,
        ((d1Weight x : ℝ≥0∞) / 256) *
          ∑ y ∈ Finset.Icc (-3 : ℤ) 3,
            ((d1Weight y : ℝ≥0∞) / 256) *
              (↑(((6 : NNReal) / 5) ^ (σ * (x * y))) : ℝ≥0∞) := by
  simp only [ENNReal.ofNNReal_finsetSum, ENNReal.coe_mul,
    ENNReal.coe_div (by norm_num : (256 : NNReal) ≠ 0), ENNReal.coe_natCast,
    ENNReal.coe_ofNat]

private theorem coe_shared_moment_sum (σ τ : ℤ) :
    (↑(∑ x ∈ Finset.Icc (-3 : ℤ) 3,
      ((d1Weight x : NNReal) / 256) *
        ∑ y ∈ Finset.Icc (-3 : ℤ) 3,
          ((d1Weight y : NNReal) / 256) *
            ∑ z ∈ Finset.Icc (-3 : ℤ) 3,
              ((d1Weight z : NNReal) / 256) *
                ((6 : NNReal) / 5) ^ (x * (σ * y + τ * z))) : ℝ≥0∞) =
      ∑ x ∈ Finset.Icc (-3 : ℤ) 3,
        ((d1Weight x : ℝ≥0∞) / 256) *
          ∑ y ∈ Finset.Icc (-3 : ℤ) 3,
            ((d1Weight y : ℝ≥0∞) / 256) *
              ∑ z ∈ Finset.Icc (-3 : ℤ) 3,
                ((d1Weight z : ℝ≥0∞) / 256) *
                  (↑(((6 : NNReal) / 5) ^
                    (x * (σ * y + τ * z))) : ℝ≥0∞) := by
  simp only [ENNReal.ofNNReal_finsetSum, ENNReal.coe_mul,
    ENNReal.coe_div (by norm_num : (256 : NNReal) ≠ 0), ENNReal.coe_natCast,
    ENNReal.coe_ofNat]

theorem challenge_one_moment (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    expectedValue d1IntSampler
        (fun x => challengeChernoffBase ^ (σ * x)) =
      challengeOneMoment := by
  rw [expectedValue_d1IntSampler_eq_sum]
  unfold challengeChernoffBase challengeOneMoment
  have hb : (6 : NNReal) / 5 ≠ 0 := by norm_num
  have hbase : (6 : ℝ≥0∞) / 5 = ((↑((6 : NNReal) / 5) : ℝ≥0∞)) := by
    rw [ENNReal.coe_div (by norm_num)]
    norm_num
  rw [hbase]
  simp_rw [← ENNReal.coe_zpow hb]
  have h := one_moment_nnreal σ hσ
  unfold d1MomentNN at h
  calc
    (∑ x ∈ Finset.Icc (-3 : ℤ) 3,
      ((d1Weight x : ℝ≥0∞) / 256) *
        (↑(((6 : NNReal) / 5) ^ (σ * x)) : ℝ≥0∞)) =
        (↑(∑ x ∈ Finset.Icc (-3 : ℤ) 3,
          ((d1Weight x : NNReal) / 256) *
            ((6 : NNReal) / 5) ^ (σ * x)) : ℝ≥0∞) :=
      (coe_one_moment_sum σ).symm
    _ = (↑((784927 : NNReal) / 768000) : ℝ≥0∞) := congrArg _ h
    _ = (784927 : ℝ≥0∞) / 768000 := by
      rw [ENNReal.coe_div (by norm_num : (768000 : NNReal) ≠ 0)]
      norm_num

theorem challenge_product_moment (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    expectedValue d1IntSampler (fun x =>
      expectedValue d1IntSampler (fun y =>
        challengeChernoffBase ^ (σ * (x * y)))) =
      challengeProductMoment := by
  simp_rw [expectedValue_d1IntSampler_eq_sum]
  unfold challengeChernoffBase challengeProductMoment
  have hb : (6 : NNReal) / 5 ≠ 0 := by norm_num
  have hbase : (6 : ℝ≥0∞) / 5 = ((↑((6 : NNReal) / 5) : ℝ≥0∞)) := by
    rw [ENNReal.coe_div (by norm_num)]
    norm_num
  rw [hbase]
  simp_rw [← ENNReal.coe_zpow hb]
  have h := product_moment_nnreal σ hσ
  unfold d1MomentNN at h
  simp only [mul_assoc] at h ⊢
  calc
    (∑ x ∈ Finset.Icc (-3 : ℤ) 3,
      ((d1Weight x : ℝ≥0∞) / 256) *
        ∑ y ∈ Finset.Icc (-3 : ℤ) 3,
          ((d1Weight y : ℝ≥0∞) / 256) *
            (↑(((6 : NNReal) / 5) ^ (σ * (x * y))) : ℝ≥0∞)) =
        (↑(∑ x ∈ Finset.Icc (-3 : ℤ) 3,
          ((d1Weight x : NNReal) / 256) *
            ∑ y ∈ Finset.Icc (-3 : ℤ) 3,
              ((d1Weight y : NNReal) / 256) *
                ((6 : NNReal) / 5) ^ (σ * (x * y))) : ℝ≥0∞) :=
      (coe_product_moment_sum σ).symm
    _ = (↑((73796729825894041 : NNReal) /
          71663616000000000) : ℝ≥0∞) := congrArg _ h
    _ = (73796729825894041 : ℝ≥0∞) / 71663616000000000 := by
      rw [ENNReal.coe_div (by norm_num : (71663616000000000 : NNReal) ≠ 0)]
      norm_num

theorem challenge_shared_moment
    (σ τ : ℤ) (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    expectedValue d1IntSampler (fun x =>
      expectedValue d1IntSampler (fun y =>
        expectedValue d1IntSampler (fun z =>
          challengeChernoffBase ^ (x * (σ * y + τ * z))))) =
      challengeSharedMoment := by
  simp_rw [expectedValue_d1IntSampler_eq_sum]
  unfold challengeChernoffBase challengeSharedMoment
  have hb : (6 : NNReal) / 5 ≠ 0 := by norm_num
  have hbase : (6 : ℝ≥0∞) / 5 = ((↑((6 : NNReal) / 5) : ℝ≥0∞)) := by
    rw [ENNReal.coe_div (by norm_num)]
    norm_num
  rw [hbase]
  simp_rw [← ENNReal.coe_zpow hb]
  have h := shared_moment_nnreal σ τ hσ hτ
  calc
    (∑ x ∈ Finset.Icc (-3 : ℤ) 3,
      ((d1Weight x : ℝ≥0∞) / 256) *
        ∑ y ∈ Finset.Icc (-3 : ℤ) 3,
          ((d1Weight y : ℝ≥0∞) / 256) *
            ∑ z ∈ Finset.Icc (-3 : ℤ) 3,
              ((d1Weight z : ℝ≥0∞) / 256) *
                (↑(((6 : NNReal) / 5) ^
                  (x * (σ * y + τ * z))) : ℝ≥0∞)) =
        (↑(∑ x ∈ Finset.Icc (-3 : ℤ) 3,
          ((d1Weight x : NNReal) / 256) *
            ∑ y ∈ Finset.Icc (-3 : ℤ) 3,
              ((d1Weight y : NNReal) / 256) *
                ∑ z ∈ Finset.Icc (-3 : ℤ) 3,
                  ((d1Weight z : NNReal) / 256) *
                    ((6 : NNReal) / 5) ^
                      (x * (σ * y + τ * z))) : ℝ≥0∞) :=
      (coe_shared_moment_sum σ τ).symm
    _ = (↑((127847491742921604065083548949681 : NNReal) /
          120367356051456000000000000000000) : ℝ≥0∞) := congrArg _ h
    _ = (127847491742921604065083548949681 : ℝ≥0∞) /
          120367356051456000000000000000000 := by
      rw [ENNReal.coe_div
        (by norm_num : (120367356051456000000000000000000 : NNReal) ≠ 0)]
      norm_num

theorem expectedValue_congr_evalDist
    {α : Type} {mx my : ProbComp α} (h : evalDist mx = evalDist my)
    (f : α → ℝ≥0∞) : expectedValue mx f = expectedValue my f := by
  apply expectedValue_congr
  intro x
  exact (evalDist_ext_iff.mp h x)

theorem expectedValue_const_mul_left
    {α : Type} (mx : ProbComp α) (a : ℝ≥0∞) (f : α → ℝ≥0∞) :
    expectedValue mx (fun x => a * f x) = a * expectedValue mx f := by
  rw [expectedValue_def, expectedValue_def]
  calc
    (∑' x, Pr[= x | mx] * (a * f x)) =
        ∑' x, a * (Pr[= x | mx] * f x) := by
      apply tsum_congr
      intro x
      ac_rfl
    _ = a * ∑' x, Pr[= x | mx] * f x := ENNReal.tsum_mul_left

theorem expectedValue_const_mul_right
    {α : Type} (mx : ProbComp α) (f : α → ℝ≥0∞) (a : ℝ≥0∞) :
    expectedValue mx (fun x => f x * a) = expectedValue mx f * a := by
  rw [expectedValue_def, expectedValue_def]
  calc
    (∑' x, Pr[= x | mx] * (f x * a)) =
        ∑' x, (Pr[= x | mx] * f x) * a := by
      apply tsum_congr
      intro x
      ac_rfl
    _ = (∑' x, Pr[= x | mx] * f x) * a := ENNReal.tsum_mul_right

private theorem expectedValue_cons_zpow
    {α : Type} (r : ℝ≥0∞) (hr_zero : r ≠ 0) (hr_top : r ≠ ∞)
    (mx : ProbComp α) (n : ℕ)
    (f : (i : Fin (n + 1)) → α → ℤ) :
    expectedValue mx (fun a =>
        expectedValue (Fin.mOfFn n fun _ => mx) (fun rest =>
          r ^ ∑ i, f i (@Fin.cons n (fun _ => α) a rest i))) =
      expectedValue mx (fun a => r ^ f 0 a) *
        expectedValue (Fin.mOfFn n fun _ => mx) (fun rest =>
          r ^ ∑ i, f i.succ (rest i)) := by
  calc
    expectedValue mx (fun a =>
        expectedValue (Fin.mOfFn n fun _ => mx) (fun rest =>
          r ^ ∑ i, f i (@Fin.cons n (fun _ => α) a rest i))) =
        expectedValue mx (fun a =>
          expectedValue (Fin.mOfFn n fun _ => mx) (fun rest =>
            r ^ f 0 a * r ^ ∑ i, f i.succ (rest i))) := by
      congr 1
      funext a
      congr 1
      funext rest
      rw [Fin.sum_univ_succ, ENNReal.zpow_add hr_zero hr_top]
      rfl
    _ = expectedValue mx (fun a =>
          r ^ f 0 a *
            expectedValue (Fin.mOfFn n fun _ => mx) (fun rest =>
              r ^ ∑ i, f i.succ (rest i))) := by
      congr 1
      funext a
      exact expectedValue_const_mul_left _ _ _
    _ = expectedValue mx (fun a => r ^ f 0 a) *
          expectedValue (Fin.mOfFn n fun _ => mx) (fun rest =>
            r ^ ∑ i, f i.succ (rest i)) :=
      expectedValue_const_mul_right _ _ _

private theorem expectedValue_sampleIID_zpow_sum_generic
    {α : Type} (r : ℝ≥0∞) (hr_zero : r ≠ 0) (hr_top : r ≠ ∞)
    (mx : ProbComp α) (n : ℕ)
    (f : (i : Fin n) → α → ℤ) :
    expectedValue (ProbComp.sampleIID n mx)
        (fun v => r ^ ∑ i, f i (v i)) =
      ∏ i, expectedValue mx (fun x => r ^ f i x) := by
  induction n with
  | zero =>
      simp [ProbComp.sampleIID, Fin.mOfFn]
  | succ n ih =>
      simp only [ProbComp.sampleIID, Fin.mOfFn, expectedValue_bind,
        expectedValue_pure]
      rw [Fin.prod_univ_succ]
      rw [expectedValue_cons_zpow r hr_zero hr_top]
      have htail := ih (fun i : Fin n => f i.succ)
      simpa only [ProbComp.sampleIID] using
        congrArg (fun t => expectedValue mx (fun a => r ^ f 0 a) * t) htail

theorem expectedValue_sampleIID_zpow_sum
    {α : Type} (mx : ProbComp α) (n : ℕ)
    (f : (i : Fin n) → α → ℤ) :
    expectedValue (ProbComp.sampleIID n mx)
        (fun v => challengeChernoffBase ^ ∑ i, f i (v i)) =
      ∏ i, expectedValue mx (fun x => challengeChernoffBase ^ f i x) := by
  apply expectedValue_sampleIID_zpow_sum_generic
  · norm_num [challengeChernoffBase]
  · unfold challengeChernoffBase
    exact ENNReal.div_ne_top (by norm_num) (by norm_num)

end PairBoundInternal

/-- Exact rational bounds for the shared-coordinate and disjoint-coordinate Chernoff estimates.
`ChallengePairBound` applies these inequalities to the first-exchange, uniform-public-matrix model
with the exact Challenge D1 sampler; this theorem itself is solely an arithmetic statement. -/
theorem challenge_pair_chernoff_arithmetic :
    (4 * ((5 : ℚ) / 6) ^ 512 *
        ((127847491742921604065083548949681 : ℚ) /
          120367356051456000000000000000000) ^ 704 *
        ((784927 : ℚ) / 768000) ^ 2 ≤ (1 : ℚ) / 2 ^ 70) ∧
    (4 * ((5 : ℚ) / 6) ^ 512 *
        ((73796729825894041 : ℚ) / 71663616000000000) ^ 1408 *
        ((784927 : ℚ) / 768000) ^ 2 ≤ (1 : ℚ) / 2 ^ 70) := by
  constructor <;> norm_num [div_pow] <;> decide +kernel

end lweCKA
