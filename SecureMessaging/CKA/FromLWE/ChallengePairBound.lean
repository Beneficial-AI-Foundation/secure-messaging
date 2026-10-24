/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.ChallengeExperiment
import SecureMessaging.CKA.FromLWE.ChallengeTailArithmetic
import VCVio.EvalDist.Prod

/-!
# Joint Challenge-parameter entry tails

The two centered entry noises have three dependence patterns.  A shared row or column contributes
two independent `X * (Y + Z)` blocks per inner coordinate; disjoint coordinates contribute four
independent `X * Y` blocks.  The two extra errors are always distinct.  Four signed Markov bounds
cover the two absolute-value tails.
-/

open OracleComp OracleComp.EvalDist
open scoped BigOperators ENNReal

namespace lweCKA

private noncomputable def challengeChernoffBase : ℝ≥0∞ := (6 : ℝ≥0∞) / 5

private noncomputable def challengeOneMoment : ℝ≥0∞ :=
  (784927 : ℝ≥0∞) / 768000

private noncomputable def challengeProductMoment : ℝ≥0∞ :=
  (73796729825894041 : ℝ≥0∞) / 71663616000000000

private noncomputable def challengeSharedMoment : ℝ≥0∞ :=
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

private theorem challenge_one_moment (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
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

private theorem challenge_product_moment (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
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

private theorem challenge_shared_moment
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

private theorem expectedValue_congr_evalDist
    {α : Type} {mx my : ProbComp α} (h : evalDist mx = evalDist my)
    (f : α → ℝ≥0∞) : expectedValue mx f = expectedValue my f := by
  apply expectedValue_congr
  intro x
  exact (evalDist_ext_iff.mp h x)

private theorem expectedValue_const_mul_left
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

private theorem expectedValue_const_mul_right
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

private theorem expectedValue_sampleIID_zpow_sum
    {α : Type} (mx : ProbComp α) (n : ℕ)
    (f : (i : Fin n) → α → ℤ) :
    expectedValue (ProbComp.sampleIID n mx)
        (fun v => challengeChernoffBase ^ ∑ i, f i (v i)) =
      ∏ i, expectedValue mx (fun x => challengeChernoffBase ^ f i x) := by
  apply expectedValue_sampleIID_zpow_sum_generic
  · norm_num [challengeChernoffBase]
  · unfold challengeChernoffBase
    exact ENNReal.div_ne_top (by norm_num) (by norm_num)

private theorem evalDist_sampleIID_two_coords
    {α : Type} (mx : ProbComp α) (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    evalDist ((fun v : Fin n → α => (v i, v j)) <$> ProbComp.sampleIID n mx) =
      evalDist (Prod.mk <$> mx <*> mx) := by
  apply evalDist_ext
  intro z
  rw [probOutput_map]
  change Pr[fun v : Fin n → α => (v i, v j) = z |
      Fin.mOfFn n fun _ => mx] = Pr[= z | Prod.mk <$> mx <*> mx]
  have hevent :
      (fun v : Fin n → α => (v i, v j) = z) =
        fun v => ∀ k,
          (fun x => if k = i then x = z.1 else if k = j then x = z.2 else True)
            (v k) := by
    funext v
    apply propext
    constructor
    · intro hv k
      have hi : v i = z.1 := congrArg Prod.fst hv
      have hj : v j = z.2 := congrArg Prod.snd hv
      by_cases hki : k = i
      · simpa [hki] using hi
      · by_cases hkj : k = j
        · simpa [hki, hkj, Ne.symm hij] using hj
        · simp [hki, hkj]
    · intro hv
      apply Prod.ext
      · simpa using hv i
      · simpa [Ne.symm hij] using hv j
  rw [hevent]
  calc
    Pr[fun v : Fin n → α => ∀ k,
          (fun x => if k = i then x = z.1 else if k = j then x = z.2 else True)
            (v k) | Fin.mOfFn n fun _ => mx] =
        ∏ k, Pr[fun x =>
          if k = i then x = z.1 else if k = j then x = z.2 else True | mx] :=
      probEvent_forall_coord_mOfFn n (fun _ => mx)
        (fun k x => if k = i then x = z.1 else if k = j then x = z.2 else True)
    _ = Pr[= z | Prod.mk <$> mx <*> mx] := by
      rw [probOutput_seq_map_prod_mk_eq_mul]
      classical
      rw [Finset.prod_eq_mul_of_mem i j (by simp) (by simp) hij]
      · simp [Ne.symm hij]
      · intro k _ hk
        simp [hk.1, hk.2]

private theorem evalDist_sampleIID_map_local
    {α β : Type} (n : ℕ) (mx : ProbComp α) (f : α → β) :
    evalDist
        ((fun xs : Fin n → α => fun i => f (xs i)) <$>
          ProbComp.sampleIID n mx) =
      evalDist (ProbComp.sampleIID n (f <$> mx)) := by
  induction n with
  | zero =>
      simp only [ProbComp.sampleIID, Fin.mOfFn, map_pure]
      congr 2
      funext i
      exact i.elim0
  | succ n ih =>
      simp only [ProbComp.sampleIID, Fin.mOfFn, map_eq_bind_pure_comp,
        Function.comp_apply, bind_assoc, pure_bind]
      refine evalDist_bind_congr' mx fun a => ?_
      have htail := evalDist_map_eq_of_evalDist_eq ih
        (fun rest : Fin n → β => @Fin.cons n (fun _ => β) (f a) rest)
      convert htail using 1
      · simp only [ProbComp.sampleIID, map_eq_bind_pure_comp, bind_assoc, pure_bind,
          Function.comp_apply]
        refine evalDist_bind_congr' (Fin.mOfFn n fun _ => mx) fun rest => ?_
        congr 2
        funext i
        exact Fin.cases (by simp) (fun j => by simp) i
      · simp only [ProbComp.sampleIID, map_eq_bind_pure_comp, Function.comp_def]

private theorem evalDist_sampleIID_congr_local
    {α : Type} (n : ℕ) (mx my : ProbComp α) (h : evalDist mx = evalDist my) :
    evalDist (ProbComp.sampleIID n mx) = evalDist (ProbComp.sampleIID n my) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [ProbComp.sampleIID, Fin.mOfFn]
      rw [evalDist_bind, evalDist_bind, h]
      apply congrArg
      funext a
      have ih' : evalDist (Fin.mOfFn n fun _ => mx) =
          evalDist (Fin.mOfFn n fun _ => my) := by
        simpa only [ProbComp.sampleIID] using ih
      rw [evalDist_bind, evalDist_bind, ih']

private def challengeIntMatrix (rows cols : ℕ) :
    ProbComp (Matrix (Fin rows) (Fin cols) ℤ) :=
  ProbComp.sampleIID rows (ProbComp.sampleIID cols d1IntSampler)

private theorem evalDist_sampleMatrix_valMinAbs (rows cols : ℕ) :
    evalDist
        ((fun m : Matrix (Fin rows) (Fin cols) (Scalar challengeParams) =>
            fun i j => (m i j).valMinAbs) <$>
          sampleMatrix d1Sampler rows cols) =
      evalDist (challengeIntMatrix rows cols) := by
  have hinner := (evalDist_sampleIID_map_local cols d1Sampler
    (fun x : Scalar challengeParams => x.valMinAbs)).trans
      (evalDist_sampleIID_congr_local cols
        ((fun x : Scalar challengeParams => x.valMinAbs) <$> d1Sampler)
        d1IntSampler evalDist_valMinAbs_d1Sampler)
  have houter := (evalDist_sampleIID_map_local rows
    (ProbComp.sampleIID cols d1Sampler)
    (fun row : Fin cols → Scalar challengeParams =>
      fun j => (row j).valMinAbs)).trans
        (evalDist_sampleIID_congr_local rows _ _ hinner)
  unfold sampleMatrix challengeIntMatrix
  have hfun :
      (fun m : Matrix (Fin rows) (Fin cols) (Scalar challengeParams) =>
        fun i j => (m i j).valMinAbs) =
      (fun xs : Fin rows → Fin cols → Scalar challengeParams =>
        fun i j => (xs i j).valMinAbs) := by
    funext m i j
    rfl
  rw [hfun]
  exact houter

private structure ChallengeIntCoins where
  s0 : Matrix (Fin challengeParams.n) (Fin challengeParams.nbar) ℤ
  e0 : Matrix (Fin challengeParams.n) (Fin challengeParams.nbar) ℤ
  s1 : Matrix (Fin challengeParams.nbar) (Fin challengeParams.n) ℤ
  e1 : Matrix (Fin challengeParams.nbar) (Fin challengeParams.n) ℤ
  extra : Matrix (Fin challengeParams.nbar) (Fin challengeParams.nbar) ℤ

private def challengeCenteredCoinsExp : ProbComp ChallengeIntCoins := do
  let s0 ←
    (fun m : Matrix (Fin challengeParams.n) (Fin challengeParams.nbar)
        (Scalar challengeParams) => fun i j => (m i j).valMinAbs) <$>
      sampleMatrix d1Sampler challengeParams.n challengeParams.nbar
  let e0 ←
    (fun m : Matrix (Fin challengeParams.n) (Fin challengeParams.nbar)
        (Scalar challengeParams) => fun i j => (m i j).valMinAbs) <$>
      sampleMatrix d1Sampler challengeParams.n challengeParams.nbar
  let s1 ←
    (fun m : Matrix (Fin challengeParams.nbar) (Fin challengeParams.n)
        (Scalar challengeParams) => fun i j => (m i j).valMinAbs) <$>
      sampleMatrix d1Sampler challengeParams.nbar challengeParams.n
  let e1 ←
    (fun m : Matrix (Fin challengeParams.nbar) (Fin challengeParams.n)
        (Scalar challengeParams) => fun i j => (m i j).valMinAbs) <$>
      sampleMatrix d1Sampler challengeParams.nbar challengeParams.n
  let extra ←
    (fun m : Matrix (Fin challengeParams.nbar) (Fin challengeParams.nbar)
        (Scalar challengeParams) => fun i j => (m i j).valMinAbs) <$>
      sampleMatrix d1Sampler challengeParams.nbar challengeParams.nbar
  return ⟨s0, e0, s1, e1, extra⟩

private def challengeIntCoinsExp : ProbComp ChallengeIntCoins := do
  let s0 ← challengeIntMatrix challengeParams.n challengeParams.nbar
  let e0 ← challengeIntMatrix challengeParams.n challengeParams.nbar
  let s1 ← challengeIntMatrix challengeParams.nbar challengeParams.n
  let e1 ← challengeIntMatrix challengeParams.nbar challengeParams.n
  let extra ← challengeIntMatrix challengeParams.nbar challengeParams.nbar
  return ⟨s0, e0, s1, e1, extra⟩

private def centerChallengeCoins
    (t : InitKey challengeParams × SendACoins challengeParams) : ChallengeIntCoins :=
  ⟨(fun i j => (t.1.secret i j).valMinAbs),
    (fun i j => (t.1.error i j).valMinAbs),
    (fun i j => (t.2.secret i j).valMinAbs),
    (fun i j => (t.2.error i j).valMinAbs),
    (fun i j => (t.2.extra i j).valMinAbs)⟩

private def challengeEntryNoiseAux
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (t : ChallengeIntCoins) : ℤ :=
  (∑ k : Fin challengeParams.n, t.s1 c.1 k * t.e0 k c.2) -
    (∑ k : Fin challengeParams.n, t.e1 c.1 k * t.s0 k c.2) +
    t.extra c.1 c.2

private theorem challengeEntryNoiseAux_center
    (c : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (t : InitKey challengeParams × SendACoins challengeParams) :
    challengeEntryNoiseAux c (centerChallengeCoins t) = challengeEntryNoiseInt c t := rfl

private theorem evalDist_centerChallengeCoins :
    evalDist (centerChallengeCoins <$> challengeCoinsExp) =
      evalDist challengeIntCoinsExp := by
  have hcentered :
      evalDist (centerChallengeCoins <$> challengeCoinsExp) =
        evalDist challengeCenteredCoinsExp := by
    simp only [challengeCoinsExp, challengeCenteredCoinsExp, centerChallengeCoins,
      initKeyGen, sampleSendACoins, map_eq_bind_pure_comp, bind_assoc, pure_bind,
      Function.comp_apply]
    exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
      (($ᵗ (BaseMatrix challengeParams) : ProbComp (BaseMatrix challengeParams)))
      (probFailure_eq_zero
        (mx := ($ᵗ (BaseMatrix challengeParams) : ProbComp (BaseMatrix challengeParams))))
      _
  have hHead {α β : Type} {mx my : ProbComp α}
      (h : evalDist mx = evalDist my) (f : α → ProbComp β) :
      evalDist (mx >>= f) = evalDist (my >>= f) := by
    simp only [evalDist_bind, h]
  apply hcentered.trans
  simp only [challengeCenteredCoinsExp, challengeIntCoinsExp]
  refine (hHead (evalDist_sampleMatrix_valMinAbs _ _) _).trans ?_
  refine evalDist_bind_congr' _ fun _ => ?_
  refine (hHead (evalDist_sampleMatrix_valMinAbs _ _) _).trans ?_
  refine evalDist_bind_congr' _ fun _ => ?_
  refine (hHead (evalDist_sampleMatrix_valMinAbs _ _) _).trans ?_
  refine evalDist_bind_congr' _ fun _ => ?_
  refine (hHead (evalDist_sampleMatrix_valMinAbs _ _) _).trans ?_
  refine evalDist_bind_congr' _ fun _ => ?_
  exact hHead (evalDist_sampleMatrix_valMinAbs _ _) _

private def challengeProductExponent (σ : ℤ) : ProbComp ℤ := do
  let x ← d1IntSampler
  let y ← d1IntSampler
  return σ * (x * y)

private def challengeSharedExponent (σ τ : ℤ) : ProbComp ℤ := do
  let x ← d1IntSampler
  let y ← d1IntSampler
  let z ← d1IntSampler
  return x * (σ * y + τ * z)

private def challengeAddExponents (mx my : ProbComp ℤ) : ProbComp ℤ := do
  let x ← mx
  let y ← my
  return x + y

private def challengeSharedBlock (σ τ : ℤ) : ProbComp ℤ :=
  challengeAddExponents (challengeSharedExponent σ τ)
    (challengeSharedExponent (-σ) (-τ))

private def challengeDisjointBlock (σ τ : ℤ) : ProbComp ℤ :=
  challengeAddExponents
    (challengeAddExponents (challengeProductExponent σ) (challengeProductExponent τ))
    (challengeAddExponents (challengeProductExponent (-σ))
      (challengeProductExponent (-τ)))

private def challengeBlockSum (block : ProbComp ℤ) : ProbComp ℤ :=
  (fun v : Fin challengeParams.n → ℤ => ∑ i, v i) <$>
    ProbComp.sampleIID challengeParams.n block

private def challengePairExponentExp (shared : Bool) (σ τ : ℤ) : ProbComp ℤ :=
  let block := if shared then challengeSharedBlock σ τ else challengeDisjointBlock σ τ
  challengeAddExponents (challengeAddExponents (challengeBlockSum block)
    ((fun z => σ * z) <$> d1IntSampler)) ((fun z => τ * z) <$> d1IntSampler)

private theorem expectedValue_add_exponents (mx my : ProbComp ℤ) :
    expectedValue (challengeAddExponents mx my)
        (fun z => challengeChernoffBase ^ z) =
      expectedValue mx (fun z => challengeChernoffBase ^ z) *
        expectedValue my (fun z => challengeChernoffBase ^ z) := by
  have hbase_zero : challengeChernoffBase ≠ 0 := by
    norm_num [challengeChernoffBase]
  have hbase_top : challengeChernoffBase ≠ ∞ := by
    unfold challengeChernoffBase
    exact ENNReal.div_ne_top (by norm_num) (by norm_num)
  simp only [challengeAddExponents, expectedValue_bind, expectedValue_pure]
  calc
    expectedValue mx (fun x =>
        expectedValue my (fun y => challengeChernoffBase ^ (x + y))) =
        expectedValue mx (fun x =>
          expectedValue my (fun y =>
            challengeChernoffBase ^ x * challengeChernoffBase ^ y)) := by
      congr 1
      funext x
      congr 1
      funext y
      rw [ENNReal.zpow_add hbase_zero hbase_top]
    _ = expectedValue mx (fun x =>
          challengeChernoffBase ^ x *
            expectedValue my (fun y => challengeChernoffBase ^ y)) := by
      congr 1
      funext x
      exact expectedValue_const_mul_left _ _ _
    _ = expectedValue mx (fun x => challengeChernoffBase ^ x) *
          expectedValue my (fun y => challengeChernoffBase ^ y) :=
      expectedValue_const_mul_right _ _ _

private theorem expectedValue_product_exponent
    (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    expectedValue (challengeProductExponent σ)
        (fun z => challengeChernoffBase ^ z) = challengeProductMoment := by
  simp only [challengeProductExponent, expectedValue_bind, expectedValue_pure]
  exact challenge_product_moment σ hσ

private theorem expectedValue_shared_exponent
    (σ τ : ℤ) (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    expectedValue (challengeSharedExponent σ τ)
        (fun z => challengeChernoffBase ^ z) = challengeSharedMoment := by
  simp only [challengeSharedExponent, expectedValue_bind, expectedValue_pure]
  exact challenge_shared_moment σ τ hσ hτ

private theorem expectedValue_shared_block
    (σ τ : ℤ) (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    expectedValue (challengeSharedBlock σ τ)
        (fun z => challengeChernoffBase ^ z) = challengeSharedMoment ^ 2 := by
  rw [challengeSharedBlock, expectedValue_add_exponents,
    expectedValue_shared_exponent σ τ hσ hτ,
    expectedValue_shared_exponent (-σ) (-τ)]
  · ring
  · rcases hσ with rfl | rfl <;> simp
  · rcases hτ with rfl | rfl <;> simp

private theorem expectedValue_disjoint_block
    (σ τ : ℤ) (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    expectedValue (challengeDisjointBlock σ τ)
        (fun z => challengeChernoffBase ^ z) = challengeProductMoment ^ 4 := by
  have hnσ : -σ = 1 ∨ -σ = -1 := by
    rcases hσ with rfl | rfl <;> simp
  have hnτ : -τ = 1 ∨ -τ = -1 := by
    rcases hτ with rfl | rfl <;> simp
  simp only [challengeDisjointBlock, expectedValue_add_exponents]
  rw [expectedValue_product_exponent σ hσ, expectedValue_product_exponent τ hτ,
    expectedValue_product_exponent (-σ) hnσ,
    expectedValue_product_exponent (-τ) hnτ]
  ring

private theorem expectedValue_block_sum (block : ProbComp ℤ) :
    expectedValue (challengeBlockSum block)
        (fun z => challengeChernoffBase ^ z) =
      expectedValue block (fun z => challengeChernoffBase ^ z) ^ challengeParams.n := by
  rw [challengeBlockSum, expectedValue_map]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    expectedValue_sampleIID_zpow_sum block challengeParams.n
      (fun _ z => z)

private theorem expectedValue_pair_exponent
    (shared : Bool) (σ τ : ℤ)
    (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    expectedValue (challengePairExponentExp shared σ τ)
        (fun z => challengeChernoffBase ^ z) =
      if shared then
        challengeSharedMoment ^ 704 * challengeOneMoment ^ 2
      else
        challengeProductMoment ^ 1408 * challengeOneMoment ^ 2 := by
  simp only [challengePairExponentExp, expectedValue_add_exponents,
    expectedValue_map, expectedValue_block_sum]
  rw [challenge_one_moment σ hσ, challenge_one_moment τ hτ]
  cases shared
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [expectedValue_disjoint_block σ τ hσ hτ]
    simp only [challengeParams]
    ring
  · simp only [↓reduceIte]
    rw [expectedValue_shared_block σ τ hσ hτ]
    simp only [challengeParams]
    ring

private theorem evalDist_sampleIID_coord
    {α : Type} (mx : ProbComp α) (hfail : Pr[⊥ | mx] = 0)
    (n : ℕ) (i : Fin n) :
    evalDist ((fun v : Fin n → α => v i) <$> ProbComp.sampleIID n mx) =
      evalDist mx := by
  apply evalDist_ext
  intro x
  rw [probOutput_map]
  exact (probEvent_coord_mOfFn n (fun _ => mx) (fun _ => hfail) i (· = x)).trans
    (probEvent_eq_eq_probOutput mx x)

private theorem evalDist_challengeIntMatrix_row
    (rows cols : ℕ) (i : Fin rows) :
    evalDist ((fun m : Matrix (Fin rows) (Fin cols) ℤ => m i) <$>
      challengeIntMatrix rows cols) =
      evalDist (ProbComp.sampleIID cols d1IntSampler) := by
  unfold challengeIntMatrix
  exact evalDist_sampleIID_coord _
    (probFailure_mOfFn cols (fun _ => d1IntSampler) fun _ => probFailure_eq_zero)
    rows i

private theorem evalDist_challengeIntMatrix_col
    (rows cols : ℕ) (j : Fin cols) :
    evalDist
        ((fun m : Matrix (Fin rows) (Fin cols) ℤ => fun i => m i j) <$>
          challengeIntMatrix rows cols) =
      evalDist (ProbComp.sampleIID rows d1IntSampler) := by
  unfold challengeIntMatrix
  calc
    evalDist
          ((fun m : Matrix (Fin rows) (Fin cols) ℤ => fun i => m i j) <$>
            ProbComp.sampleIID rows (ProbComp.sampleIID cols d1IntSampler)) =
        evalDist
          (ProbComp.sampleIID rows
            ((fun row : Fin cols → ℤ => row j) <$>
              ProbComp.sampleIID cols d1IntSampler)) :=
      evalDist_sampleIID_map_local rows _ (fun row : Fin cols → ℤ => row j)
    _ = evalDist (ProbComp.sampleIID rows d1IntSampler) := by
      apply evalDist_sampleIID_congr_local
      exact evalDist_sampleIID_coord d1IntSampler probFailure_eq_zero cols j

private theorem evalDist_challengeIntMatrix_two_cols
    (rows cols : ℕ) (j l : Fin cols) (hjl : j ≠ l) :
    evalDist
        ((fun m : Matrix (Fin rows) (Fin cols) ℤ =>
            fun i => (m i j, m i l)) <$>
          challengeIntMatrix rows cols) =
      evalDist (ProbComp.sampleIID rows
        (Prod.mk <$> d1IntSampler <*> d1IntSampler)) := by
  unfold challengeIntMatrix
  calc
    evalDist
          ((fun m : Matrix (Fin rows) (Fin cols) ℤ =>
              fun i => (m i j, m i l)) <$>
            ProbComp.sampleIID rows (ProbComp.sampleIID cols d1IntSampler)) =
        evalDist
          (ProbComp.sampleIID rows
            ((fun row : Fin cols → ℤ => (row j, row l)) <$>
              ProbComp.sampleIID cols d1IntSampler)) :=
      evalDist_sampleIID_map_local rows _
        (fun row : Fin cols → ℤ => (row j, row l))
    _ = evalDist (ProbComp.sampleIID rows
          (Prod.mk <$> d1IntSampler <*> d1IntSampler)) := by
      apply evalDist_sampleIID_congr_local
      exact evalDist_sampleIID_two_coords d1IntSampler cols j l hjl

private theorem evalDist_sampleIID_zip
    {α β : Type} (mx : ProbComp α) (my : ProbComp β) (n : ℕ) :
    evalDist
        (do
          let xs ← ProbComp.sampleIID n mx
          let ys ← ProbComp.sampleIID n my
          return fun i => (xs i, ys i)) =
      evalDist (ProbComp.sampleIID n (Prod.mk <$> mx <*> my)) := by
  induction n with
  | zero =>
      simp only [ProbComp.sampleIID, Fin.mOfFn, pure_bind]
      congr 2
      funext i
      exact i.elim0
  | succ n ih =>
      simp only [ProbComp.sampleIID, Fin.mOfFn, bind_assoc, pure_bind,
        seq_eq_bind_map, map_eq_bind_pure_comp, Function.comp_apply]
      refine evalDist_bind_congr' mx fun x => ?_
      rw [evalDist_bind_bind_swap]
      refine evalDist_bind_congr' my fun y => ?_
      have htail := evalDist_map_eq_of_evalDist_eq ih
        (fun rest : Fin n → α × β => @Fin.cons n (fun _ => α × β) (x, y) rest)
      convert htail using 1
      · simp only [ProbComp.sampleIID, map_eq_bind_pure_comp, bind_assoc,
          pure_bind, Function.comp_apply]
        refine evalDist_bind_congr' (Fin.mOfFn n fun _ => mx) fun xs => ?_
        refine evalDist_bind_congr' (Fin.mOfFn n fun _ => my) fun ys => ?_
        congr 2
        funext i
        exact Fin.cases (by simp) (fun j => by simp) i
      · simp only [ProbComp.sampleIID, map_eq_bind_pure_comp]
        simp only [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc,
          pure_bind, Function.comp_apply]
        congr 1

private theorem evalDist_challengeIntMatrix_two_rows
    (rows cols : ℕ) (i k : Fin rows) (hik : i ≠ k) :
    evalDist
        ((fun m : Matrix (Fin rows) (Fin cols) ℤ =>
            fun j => (m i j, m k j)) <$>
          challengeIntMatrix rows cols) =
      evalDist (ProbComp.sampleIID cols
        (Prod.mk <$> d1IntSampler <*> d1IntSampler)) := by
  calc
    evalDist
          ((fun m : Matrix (Fin rows) (Fin cols) ℤ =>
              fun j => (m i j, m k j)) <$>
            challengeIntMatrix rows cols) =
        evalDist
          ((fun rows : (Fin cols → ℤ) × (Fin cols → ℤ) =>
              fun j => (rows.1 j, rows.2 j)) <$>
            ((fun m : Matrix (Fin rows) (Fin cols) ℤ => (m i, m k)) <$>
              challengeIntMatrix rows cols)) := by
      rw [Functor.map_map]
    _ = evalDist
          ((fun rows : (Fin cols → ℤ) × (Fin cols → ℤ) =>
              fun j => (rows.1 j, rows.2 j)) <$>
            (Prod.mk <$>
              ProbComp.sampleIID cols d1IntSampler <*>
              ProbComp.sampleIID cols d1IntSampler)) :=
      evalDist_map_eq_of_evalDist_eq
        (by
          unfold challengeIntMatrix
          exact evalDist_sampleIID_two_coords _ rows i k hik)
        _
    _ = evalDist (ProbComp.sampleIID cols
          (Prod.mk <$> d1IntSampler <*> d1IntSampler)) := by
      simpa only [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
        using evalDist_sampleIID_zip d1IntSampler d1IntSampler cols

private theorem evalDist_challengeIntMatrix_two_entries
    (rows cols : ℕ) (i k : Fin rows) (j l : Fin cols)
    (hentry : (i, j) ≠ (k, l)) :
    evalDist
        ((fun m : Matrix (Fin rows) (Fin cols) ℤ => (m i j, m k l)) <$>
          challengeIntMatrix rows cols) =
      evalDist (Prod.mk <$> d1IntSampler <*> d1IntSampler) := by
  by_cases hik : i = k
  · subst k
    have hjl : j ≠ l := by
      intro h
      exact hentry (Prod.ext rfl h)
    calc
      evalDist
            ((fun m : Matrix (Fin rows) (Fin cols) ℤ => (m i j, m i l)) <$>
              challengeIntMatrix rows cols) =
          evalDist
            ((fun v : Fin rows → ℤ × ℤ => v i) <$>
              ((fun m : Matrix (Fin rows) (Fin cols) ℤ =>
                  fun r => (m r j, m r l)) <$>
                challengeIntMatrix rows cols)) := by
        rw [Functor.map_map]
      _ = evalDist
            ((fun v : Fin rows → ℤ × ℤ => v i) <$>
              ProbComp.sampleIID rows
                (Prod.mk <$> d1IntSampler <*> d1IntSampler)) :=
        evalDist_map_eq_of_evalDist_eq
          (evalDist_challengeIntMatrix_two_cols rows cols j l hjl) _
      _ = evalDist (Prod.mk <$> d1IntSampler <*> d1IntSampler) :=
        evalDist_sampleIID_coord _ (by simp) rows i
  · calc
      evalDist
            ((fun m : Matrix (Fin rows) (Fin cols) ℤ => (m i j, m k l)) <$>
              challengeIntMatrix rows cols) =
          evalDist
            ((fun rs : (Fin cols → ℤ) × (Fin cols → ℤ) =>
                (rs.1 j, rs.2 l)) <$>
              ((fun m : Matrix (Fin rows) (Fin cols) ℤ => (m i, m k)) <$>
                challengeIntMatrix rows cols)) := by
        rw [Functor.map_map]
      _ = evalDist
            ((fun rs : (Fin cols → ℤ) × (Fin cols → ℤ) =>
                (rs.1 j, rs.2 l)) <$>
              (Prod.mk <$>
                ProbComp.sampleIID cols d1IntSampler <*>
                ProbComp.sampleIID cols d1IntSampler)) :=
        evalDist_map_eq_of_evalDist_eq
          (by
            unfold challengeIntMatrix
            exact evalDist_sampleIID_two_coords _ rows i k hik) _
      _ = evalDist
            (Prod.mk <$>
              ((fun row : Fin cols → ℤ => row j) <$>
                ProbComp.sampleIID cols d1IntSampler) <*>
              ((fun row : Fin cols → ℤ => row l) <$>
                ProbComp.sampleIID cols d1IntSampler)) := by
        simp only [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc, pure_bind,
          Function.comp_apply]
      _ = evalDist (Prod.mk <$> d1IntSampler <*> d1IntSampler) := by
        simp only [evalDist_seq_map,
          evalDist_sampleIID_coord d1IntSampler probFailure_eq_zero cols j,
          evalDist_sampleIID_coord d1IntSampler probFailure_eq_zero cols l]

private theorem evalDist_sampleIID_map_four
    {α β γ δ ε : Type}
    (mx : ProbComp α) (my : ProbComp β) (mz : ProbComp γ) (mw : ProbComp δ)
    (n : ℕ) (f : α → β → γ → δ → ε) :
    evalDist
        (do
          let xs ← ProbComp.sampleIID n mx
          let ys ← ProbComp.sampleIID n my
          let zs ← ProbComp.sampleIID n mz
          let ws ← ProbComp.sampleIID n mw
          return fun i => f (xs i) (ys i) (zs i) (ws i)) =
      evalDist
        (ProbComp.sampleIID n (do
          let x ← mx
          let y ← my
          let z ← mz
          let w ← mw
          return f x y z w)) := by
  let mxy : ProbComp (α × β) := Prod.mk <$> mx <*> my
  let mxyz : ProbComp ((α × β) × γ) := Prod.mk <$> mxy <*> mz
  let mxyzw : ProbComp (((α × β) × γ) × δ) := Prod.mk <$> mxyz <*> mw
  have hHead {κ ρ : Type} {ma mb : ProbComp κ}
      (h : evalDist ma = evalDist mb) (g : κ → ProbComp ρ) :
      evalDist (ma >>= g) = evalDist (mb >>= g) := by
    simp only [evalDist_bind, h]
  have hxy := evalDist_sampleIID_zip mx my n
  have hxyz := evalDist_sampleIID_zip mxy mz n
  have hxyzw := evalDist_sampleIID_zip mxyz mw n
  calc
    evalDist
          (do
            let xs ← ProbComp.sampleIID n mx
            let ys ← ProbComp.sampleIID n my
            let zs ← ProbComp.sampleIID n mz
            let ws ← ProbComp.sampleIID n mw
            return fun i => f (xs i) (ys i) (zs i) (ws i)) =
        evalDist
          (do
            let xys ← ProbComp.sampleIID n mxy
            let zs ← ProbComp.sampleIID n mz
            let ws ← ProbComp.sampleIID n mw
            return fun i => f (xys i).1 (xys i).2 (zs i) (ws i)) := by
      simpa only [mxy, bind_assoc, pure_bind, seq_eq_bind_map,
        map_eq_bind_pure_comp, Function.comp_apply] using
        hHead hxy (fun xys => do
          let zs ← ProbComp.sampleIID n mz
          let ws ← ProbComp.sampleIID n mw
          return fun i => f (xys i).1 (xys i).2 (zs i) (ws i))
    _ = evalDist
          (do
            let xyzs ← ProbComp.sampleIID n mxyz
            let ws ← ProbComp.sampleIID n mw
            return fun i => f (xyzs i).1.1 (xyzs i).1.2 (xyzs i).2 (ws i)) := by
      simpa only [mxyz, bind_assoc, pure_bind, seq_eq_bind_map,
        map_eq_bind_pure_comp, Function.comp_apply] using
        hHead hxyz (fun xyzs => do
          let ws ← ProbComp.sampleIID n mw
          return fun i => f (xyzs i).1.1 (xyzs i).1.2 (xyzs i).2 (ws i))
    _ = evalDist
          ((fun xyzw : Fin n → (((α × β) × γ) × δ) =>
              fun i => f (xyzw i).1.1.1 (xyzw i).1.1.2
                (xyzw i).1.2 (xyzw i).2) <$>
            ProbComp.sampleIID n mxyzw) := by
      simpa only [mxyzw, bind_assoc, pure_bind, seq_eq_bind_map,
        map_eq_bind_pure_comp, Function.comp_apply] using
        evalDist_map_eq_of_evalDist_eq hxyzw
          (fun xyzw : Fin n → (((α × β) × γ) × δ) =>
            fun i => f (xyzw i).1.1.1 (xyzw i).1.1.2
              (xyzw i).1.2 (xyzw i).2)
    _ = evalDist
          (ProbComp.sampleIID n (do
            let x ← mx
            let y ← my
            let z ← mz
            let w ← mw
            return f x y z w)) := by
      calc
        evalDist
              ((fun xyzw : Fin n → (((α × β) × γ) × δ) =>
                  fun i => f (xyzw i).1.1.1 (xyzw i).1.1.2
                    (xyzw i).1.2 (xyzw i).2) <$>
                ProbComp.sampleIID n mxyzw) =
            evalDist
              (ProbComp.sampleIID n
                ((fun xyzw : (((α × β) × γ) × δ) =>
                    f xyzw.1.1.1 xyzw.1.1.2 xyzw.1.2 xyzw.2) <$> mxyzw)) :=
          evalDist_sampleIID_map_local n mxyzw
            (fun xyzw : (((α × β) × γ) × δ) =>
              f xyzw.1.1.1 xyzw.1.1.2 xyzw.1.2 xyzw.2)
        _ = evalDist
              (ProbComp.sampleIID n (do
                let x ← mx
                let y ← my
                let z ← mz
                let w ← mw
                return f x y z w)) := by
          apply evalDist_sampleIID_congr_local
          simp only [mxyzw, mxyz, mxy, seq_eq_bind_map,
            map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]

private def challengePairSampler : ProbComp (ℤ × ℤ) :=
  Prod.mk <$> d1IntSampler <*> d1IntSampler

private def challengeProjectedRowExponentExp
    (c d : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (σ τ : ℤ) : ProbComp ℤ := do
  let s0 ←
    (fun m : Matrix (Fin challengeParams.n) (Fin challengeParams.nbar) ℤ =>
      fun k => (m k c.2, m k d.2)) <$>
      challengeIntMatrix challengeParams.n challengeParams.nbar
  let e0 ←
    (fun m : Matrix (Fin challengeParams.n) (Fin challengeParams.nbar) ℤ =>
      fun k => (m k c.2, m k d.2)) <$>
      challengeIntMatrix challengeParams.n challengeParams.nbar
  let s1 ←
    (fun m : Matrix (Fin challengeParams.nbar) (Fin challengeParams.n) ℤ => m c.1) <$>
      challengeIntMatrix challengeParams.nbar challengeParams.n
  let e1 ←
    (fun m : Matrix (Fin challengeParams.nbar) (Fin challengeParams.n) ℤ => m c.1) <$>
      challengeIntMatrix challengeParams.nbar challengeParams.n
  let extra ←
    (fun m : Matrix (Fin challengeParams.nbar) (Fin challengeParams.nbar) ℤ =>
      (m c.1 c.2, m d.1 d.2)) <$>
      challengeIntMatrix challengeParams.nbar challengeParams.nbar
  return Finset.univ.sum (fun k =>
      s1 k * (σ * (e0 k).1 + τ * (e0 k).2) +
        e1 k * ((-σ) * (s0 k).1 + (-τ) * (s0 k).2)) +
    σ * extra.1 + τ * extra.2

private def challengeProjectedColExponentExp
    (c d : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (σ τ : ℤ) : ProbComp ℤ := do
  let s0 ←
    (fun m : Matrix (Fin challengeParams.n) (Fin challengeParams.nbar) ℤ =>
      fun k => m k c.2) <$>
      challengeIntMatrix challengeParams.n challengeParams.nbar
  let e0 ←
    (fun m : Matrix (Fin challengeParams.n) (Fin challengeParams.nbar) ℤ =>
      fun k => m k c.2) <$>
      challengeIntMatrix challengeParams.n challengeParams.nbar
  let s1 ←
    (fun m : Matrix (Fin challengeParams.nbar) (Fin challengeParams.n) ℤ =>
      fun k => (m c.1 k, m d.1 k)) <$>
      challengeIntMatrix challengeParams.nbar challengeParams.n
  let e1 ←
    (fun m : Matrix (Fin challengeParams.nbar) (Fin challengeParams.n) ℤ =>
      fun k => (m c.1 k, m d.1 k)) <$>
      challengeIntMatrix challengeParams.nbar challengeParams.n
  let extra ←
    (fun m : Matrix (Fin challengeParams.nbar) (Fin challengeParams.nbar) ℤ =>
      (m c.1 c.2, m d.1 d.2)) <$>
      challengeIntMatrix challengeParams.nbar challengeParams.nbar
  return Finset.univ.sum (fun k =>
      e0 k * (σ * (s1 k).1 + τ * (s1 k).2) +
        s0 k * ((-σ) * (e1 k).1 + (-τ) * (e1 k).2)) +
    σ * extra.1 + τ * extra.2

private def challengeProjectedDisjointExponentExp
    (c d : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (σ τ : ℤ) : ProbComp ℤ := do
  let s0 ←
    (fun m : Matrix (Fin challengeParams.n) (Fin challengeParams.nbar) ℤ =>
      fun k => (m k c.2, m k d.2)) <$>
      challengeIntMatrix challengeParams.n challengeParams.nbar
  let e0 ←
    (fun m : Matrix (Fin challengeParams.n) (Fin challengeParams.nbar) ℤ =>
      fun k => (m k c.2, m k d.2)) <$>
      challengeIntMatrix challengeParams.n challengeParams.nbar
  let s1 ←
    (fun m : Matrix (Fin challengeParams.nbar) (Fin challengeParams.n) ℤ =>
      fun k => (m c.1 k, m d.1 k)) <$>
      challengeIntMatrix challengeParams.nbar challengeParams.n
  let e1 ←
    (fun m : Matrix (Fin challengeParams.nbar) (Fin challengeParams.n) ℤ =>
      fun k => (m c.1 k, m d.1 k)) <$>
      challengeIntMatrix challengeParams.nbar challengeParams.n
  let extra ←
    (fun m : Matrix (Fin challengeParams.nbar) (Fin challengeParams.nbar) ℤ =>
      (m c.1 c.2, m d.1 d.2)) <$>
      challengeIntMatrix challengeParams.nbar challengeParams.nbar
  return Finset.univ.sum (fun k =>
      σ * (s1 k).1 * (e0 k).1 + τ * (s1 k).2 * (e0 k).2 +
        (-σ) * (e1 k).1 * (s0 k).1 + (-τ) * (e1 k).2 * (s0 k).2) +
    σ * extra.1 + τ * extra.2

private theorem evalDist_bind_five_output_congr
    {α₁ α₂ α₃ α₄ α₅ ρ : Type}
    (m₁ : ProbComp α₁) (m₂ : ProbComp α₂) (m₃ : ProbComp α₃)
    (m₄ : ProbComp α₄) (m₅ : ProbComp α₅)
    (f g : α₁ → α₂ → α₃ → α₄ → α₅ → ProbComp ρ)
    (h : ∀ a₁ a₂ a₃ a₄ a₅, f a₁ a₂ a₃ a₄ a₅ = g a₁ a₂ a₃ a₄ a₅) :
    evalDist (do
      let a₁ ← m₁
      let a₂ ← m₂
      let a₃ ← m₃
      let a₄ ← m₄
      let a₅ ← m₅
      f a₁ a₂ a₃ a₄ a₅) =
    evalDist (do
      let a₁ ← m₁
      let a₂ ← m₂
      let a₃ ← m₃
      let a₄ ← m₄
      let a₅ ← m₅
      g a₁ a₂ a₃ a₄ a₅) := by
  simp only [evalDist_bind, h]

private theorem evalDist_challengeInt_to_row_projected
    (c d : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (hrow : c.1 = d.1) (σ τ : ℤ) :
    evalDist
        ((fun t => σ * challengeEntryNoiseAux c t + τ * challengeEntryNoiseAux d t) <$>
          challengeIntCoinsExp) =
      evalDist (challengeProjectedRowExponentExp c d σ τ) := by
  simp only [challengeIntCoinsExp, challengeProjectedRowExponentExp,
    challengeEntryNoiseAux, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  apply evalDist_bind_five_output_congr
  intro s0 e0 s1 e1 extra
  congr 1
  simp only [← hrow]
  ring_nf
  simp only [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring_nf

private theorem evalDist_challengeInt_to_col_projected
    (c d : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (hcol : c.2 = d.2) (σ τ : ℤ) :
    evalDist
        ((fun t => σ * challengeEntryNoiseAux c t + τ * challengeEntryNoiseAux d t) <$>
          challengeIntCoinsExp) =
      evalDist (challengeProjectedColExponentExp c d σ τ) := by
  simp only [challengeIntCoinsExp, challengeProjectedColExponentExp,
    challengeEntryNoiseAux, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  apply evalDist_bind_five_output_congr
  intro s0 e0 s1 e1 extra
  congr 1
  simp only [← hcol]
  ring_nf
  simp only [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hswap (r : ℤ) (a b : Fin challengeParams.n → ℤ) :
      (∑ k, r * a k * b k) = ∑ k, r * b k * a k := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hswap σ (fun k => e0 k c.2) (fun k => s1 c.1 k),
    hswap σ (fun k => s0 k c.2) (fun k => e1 c.1 k),
    hswap τ (fun k => e0 k c.2) (fun k => s1 d.1 k),
    hswap τ (fun k => s0 k c.2) (fun k => e1 d.1 k)]
  ring_nf

private theorem evalDist_challengeInt_to_disjoint_projected
    (c d : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (σ τ : ℤ) :
    evalDist
        ((fun t => σ * challengeEntryNoiseAux c t + τ * challengeEntryNoiseAux d t) <$>
          challengeIntCoinsExp) =
      evalDist (challengeProjectedDisjointExponentExp c d σ τ) := by
  simp only [challengeIntCoinsExp, challengeProjectedDisjointExponentExp,
    challengeEntryNoiseAux, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  apply evalDist_bind_five_output_congr
  intro s0 e0 s1 e1 extra
  congr 1
  ring_nf
  simp only [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring_nf

private def challengeRowBlock (σ τ : ℤ) : ProbComp ℤ := do
  let s0 ← challengePairSampler
  let e0 ← challengePairSampler
  let s1 ← d1IntSampler
  let e1 ← d1IntSampler
  return s1 * (σ * e0.1 + τ * e0.2) +
    e1 * ((-σ) * s0.1 + (-τ) * s0.2)

private def challengeColBlock (σ τ : ℤ) : ProbComp ℤ := do
  let s0 ← d1IntSampler
  let e0 ← d1IntSampler
  let s1 ← challengePairSampler
  let e1 ← challengePairSampler
  return e0 * (σ * s1.1 + τ * s1.2) +
    s0 * ((-σ) * e1.1 + (-τ) * e1.2)

private def challengeDisjointProjectedBlock (σ τ : ℤ) : ProbComp ℤ := do
  let s0 ← challengePairSampler
  let e0 ← challengePairSampler
  let s1 ← challengePairSampler
  let e1 ← challengePairSampler
  return σ * s1.1 * e0.1 + τ * s1.2 * e0.2 +
    (-σ) * e1.1 * s0.1 + (-τ) * e1.2 * s0.2

private def challengeSharedPairBlock (σ τ : ℤ) : ProbComp ℤ := do
  let s1 ← d1IntSampler
  let e0 ← challengePairSampler
  let e1 ← d1IntSampler
  let s0 ← challengePairSampler
  return s1 * (σ * e0.1 + τ * e0.2) +
    e1 * ((-σ) * s0.1 + (-τ) * s0.2)

private theorem evalDist_sharedPairBlock_eq
    (σ τ : ℤ) :
    evalDist (challengeSharedPairBlock σ τ) =
      evalDist (challengeSharedBlock σ τ) := by
  simp only [challengeSharedPairBlock, challengeSharedBlock, challengeSharedExponent,
    challengeAddExponents, challengePairSampler, seq_eq_bind_map,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]

private theorem evalDist_rowBlock_eq_sharedBlock (σ τ : ℤ) :
    evalDist (challengeRowBlock σ τ) = evalDist (challengeSharedBlock σ τ) := by
  apply (show evalDist (challengeRowBlock σ τ) =
      evalDist (challengeSharedPairBlock σ τ) by
    simp only [challengeRowBlock, challengeSharedPairBlock]
    calc
      evalDist
            (challengePairSampler >>= fun s0 =>
              challengePairSampler >>= fun e0 =>
              d1IntSampler >>= fun s1 =>
              d1IntSampler >>= fun e1 =>
              pure (s1 * (σ * e0.1 + τ * e0.2) +
                e1 * (-σ * s0.1 + -τ * s0.2))) =
          evalDist
            (challengePairSampler >>= fun s0 =>
              d1IntSampler >>= fun s1 =>
              challengePairSampler >>= fun e0 =>
              d1IntSampler >>= fun e1 =>
              pure (s1 * (σ * e0.1 + τ * e0.2) +
                e1 * (-σ * s0.1 + -τ * s0.2))) := by
        apply evalDist_bind_congr'
        intro s0
        rw [evalDist_bind_bind_swap]
      _ = evalDist
            (d1IntSampler >>= fun s1 =>
              challengePairSampler >>= fun s0 =>
              challengePairSampler >>= fun e0 =>
              d1IntSampler >>= fun e1 =>
              pure (s1 * (σ * e0.1 + τ * e0.2) +
                e1 * (-σ * s0.1 + -τ * s0.2))) := by
        exact evalDist_bind_bind_swap challengePairSampler d1IntSampler
          (fun s0 s1 =>
            challengePairSampler >>= fun e0 =>
            d1IntSampler >>= fun e1 =>
            pure (s1 * (σ * e0.1 + τ * e0.2) +
              e1 * (-σ * s0.1 + -τ * s0.2)))
      _ = evalDist
            (d1IntSampler >>= fun s1 =>
              challengePairSampler >>= fun e0 =>
              challengePairSampler >>= fun s0 =>
              d1IntSampler >>= fun e1 =>
              pure (s1 * (σ * e0.1 + τ * e0.2) +
                e1 * (-σ * s0.1 + -τ * s0.2))) := by
        apply evalDist_bind_congr'
        intro s1
        rw [evalDist_bind_bind_swap]
      _ = evalDist
            (d1IntSampler >>= fun s1 =>
              challengePairSampler >>= fun e0 =>
              d1IntSampler >>= fun e1 =>
              challengePairSampler >>= fun s0 =>
              pure (s1 * (σ * e0.1 + τ * e0.2) +
                e1 * (-σ * s0.1 + -τ * s0.2))) := by
        apply evalDist_bind_congr'
        intro s1
        apply evalDist_bind_congr'
        intro e0
        rw [evalDist_bind_bind_swap])

private theorem evalDist_colBlock_eq_sharedBlock (σ τ : ℤ) :
    evalDist (challengeColBlock σ τ) = evalDist (challengeSharedBlock σ τ) := by
  have hreorder : evalDist (challengeColBlock σ τ) =
      evalDist (challengeSharedPairBlock σ τ) := by
    simp only [challengeColBlock, challengeSharedPairBlock]
    calc
      evalDist
            (d1IntSampler >>= fun s0 =>
              d1IntSampler >>= fun e0 =>
              challengePairSampler >>= fun s1 =>
              challengePairSampler >>= fun e1 =>
              pure (e0 * (σ * s1.1 + τ * s1.2) +
                s0 * (-σ * e1.1 + -τ * e1.2))) =
          evalDist
            (d1IntSampler >>= fun s0 =>
              challengePairSampler >>= fun s1 =>
              d1IntSampler >>= fun e0 =>
              challengePairSampler >>= fun e1 =>
              pure (e0 * (σ * s1.1 + τ * s1.2) +
                s0 * (-σ * e1.1 + -τ * e1.2))) := by
        apply evalDist_bind_congr'
        intro s0
        rw [evalDist_bind_bind_swap]
      _ = evalDist
            (challengePairSampler >>= fun s1 =>
              d1IntSampler >>= fun s0 =>
              d1IntSampler >>= fun e0 =>
              challengePairSampler >>= fun e1 =>
              pure (e0 * (σ * s1.1 + τ * s1.2) +
                s0 * (-σ * e1.1 + -τ * e1.2))) := by
        exact evalDist_bind_bind_swap d1IntSampler challengePairSampler
          (fun s0 s1 =>
            d1IntSampler >>= fun e0 =>
            challengePairSampler >>= fun e1 =>
            pure (e0 * (σ * s1.1 + τ * s1.2) +
              s0 * (-σ * e1.1 + -τ * e1.2)))
      _ = evalDist
            (challengePairSampler >>= fun s1 =>
              d1IntSampler >>= fun e0 =>
              d1IntSampler >>= fun s0 =>
              challengePairSampler >>= fun e1 =>
              pure (e0 * (σ * s1.1 + τ * s1.2) +
                s0 * (-σ * e1.1 + -τ * e1.2))) := by
        apply evalDist_bind_congr'
        intro s1
        rw [evalDist_bind_bind_swap]
      _ = evalDist
            (d1IntSampler >>= fun e0 =>
              challengePairSampler >>= fun s1 =>
              d1IntSampler >>= fun s0 =>
              challengePairSampler >>= fun e1 =>
              pure (e0 * (σ * s1.1 + τ * s1.2) +
                s0 * (-σ * e1.1 + -τ * e1.2))) := by
        exact evalDist_bind_bind_swap challengePairSampler d1IntSampler
          (fun s1 e0 =>
            d1IntSampler >>= fun s0 =>
            challengePairSampler >>= fun e1 =>
            pure (e0 * (σ * s1.1 + τ * s1.2) +
              s0 * (-σ * e1.1 + -τ * e1.2)))
      _ = evalDist (challengeSharedPairBlock σ τ) := by
        simp only [challengeSharedPairBlock]
  exact hreorder.trans (evalDist_sharedPairBlock_eq σ τ)

private def challengeDoubleProductBlock (σ τ : ℤ) : ProbComp ℤ := do
  let x ← challengePairSampler
  let y ← challengePairSampler
  return σ * x.1 * y.1 + τ * x.2 * y.2

private def challengeDisjointPairBlock (σ τ : ℤ) : ProbComp ℤ :=
  challengeAddExponents (challengeDoubleProductBlock σ τ)
    (challengeDoubleProductBlock (-σ) (-τ))

private theorem evalDist_doubleProductBlock_eq (σ τ : ℤ) :
    evalDist (challengeDoubleProductBlock σ τ) =
      evalDist (challengeAddExponents (challengeProductExponent σ)
        (challengeProductExponent τ)) := by
  simp only [challengeDoubleProductBlock, challengePairSampler,
    challengeAddExponents, challengeProductExponent, seq_eq_bind_map,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  apply evalDist_bind_congr'
  intro x₁
  rw [evalDist_bind_bind_swap]
  apply evalDist_bind_congr'
  intro y₁
  apply evalDist_bind_congr'
  intro x₂
  apply evalDist_bind_congr'
  intro y₂
  congr 2
  ring

private theorem evalDist_disjointPairBlock_eq (σ τ : ℤ) :
    evalDist (challengeDisjointPairBlock σ τ) =
      evalDist (challengeDisjointBlock σ τ) := by
  have hHead {α β : Type} {mx my : ProbComp α}
      (h : evalDist mx = evalDist my) (f : α → ProbComp β) :
      evalDist (mx >>= f) = evalDist (my >>= f) := by
    simp only [evalDist_bind, h]
  simp only [challengeDisjointPairBlock, challengeDisjointBlock,
    challengeAddExponents]
  refine (hHead (evalDist_doubleProductBlock_eq σ τ) _).trans ?_
  refine evalDist_bind_congr' _ fun _ => ?_
  exact hHead (evalDist_doubleProductBlock_eq (-σ) (-τ)) _

private def disjointOrder0 (σ τ : ℤ) : ProbComp ℤ := do
  let s0 ← challengePairSampler
  let e0 ← challengePairSampler
  let s1 ← challengePairSampler
  let e1 ← challengePairSampler
  return σ * s1.1 * e0.1 + τ * s1.2 * e0.2 +
    (-σ) * e1.1 * s0.1 + (-τ) * e1.2 * s0.2

private def disjointOrder1 (σ τ : ℤ) : ProbComp ℤ := do
  let s0 ← challengePairSampler
  let s1 ← challengePairSampler
  let e0 ← challengePairSampler
  let e1 ← challengePairSampler
  return σ * s1.1 * e0.1 + τ * s1.2 * e0.2 +
    (-σ) * e1.1 * s0.1 + (-τ) * e1.2 * s0.2

private def disjointOrder2 (σ τ : ℤ) : ProbComp ℤ := do
  let s1 ← challengePairSampler
  let s0 ← challengePairSampler
  let e0 ← challengePairSampler
  let e1 ← challengePairSampler
  return σ * s1.1 * e0.1 + τ * s1.2 * e0.2 +
    (-σ) * e1.1 * s0.1 + (-τ) * e1.2 * s0.2

private def disjointOrder3 (σ τ : ℤ) : ProbComp ℤ := do
  let s1 ← challengePairSampler
  let e0 ← challengePairSampler
  let s0 ← challengePairSampler
  let e1 ← challengePairSampler
  return σ * s1.1 * e0.1 + τ * s1.2 * e0.2 +
    (-σ) * e1.1 * s0.1 + (-τ) * e1.2 * s0.2

private def disjointOrder4 (σ τ : ℤ) : ProbComp ℤ := do
  let s1 ← challengePairSampler
  let e0 ← challengePairSampler
  let e1 ← challengePairSampler
  let s0 ← challengePairSampler
  return σ * s1.1 * e0.1 + τ * s1.2 * e0.2 +
    (-σ) * e1.1 * s0.1 + (-τ) * e1.2 * s0.2

private theorem evalDist_disjointOrder01 (σ τ : ℤ) :
    evalDist (disjointOrder0 σ τ) = evalDist (disjointOrder1 σ τ) := by
  simp only [disjointOrder0, disjointOrder1]
  apply evalDist_bind_congr'
  intro s0
  rw [evalDist_bind_bind_swap]

private theorem evalDist_disjointOrder12 (σ τ : ℤ) :
    evalDist (disjointOrder1 σ τ) = evalDist (disjointOrder2 σ τ) := by
  simp only [disjointOrder1, disjointOrder2]
  exact evalDist_bind_bind_swap challengePairSampler challengePairSampler
    (fun s0 s1 =>
      challengePairSampler >>= fun e0 =>
      challengePairSampler >>= fun e1 =>
      pure (σ * s1.1 * e0.1 + τ * s1.2 * e0.2 +
        -σ * e1.1 * s0.1 + -τ * e1.2 * s0.2))

private theorem evalDist_disjointOrder23 (σ τ : ℤ) :
    evalDist (disjointOrder2 σ τ) = evalDist (disjointOrder3 σ τ) := by
  simp only [disjointOrder2, disjointOrder3]
  apply evalDist_bind_congr'
  intro s1
  rw [evalDist_bind_bind_swap]

private theorem evalDist_disjointOrder34 (σ τ : ℤ) :
    evalDist (disjointOrder3 σ τ) = evalDist (disjointOrder4 σ τ) := by
  simp only [disjointOrder3, disjointOrder4]
  apply evalDist_bind_congr'
  intro s1
  apply evalDist_bind_congr'
  intro e0
  rw [evalDist_bind_bind_swap]

private theorem evalDist_disjointOrder4_pair (σ τ : ℤ) :
    evalDist (disjointOrder4 σ τ) =
      evalDist (challengeDisjointPairBlock σ τ) := by
  have hout (s1 e0 e1 s0 : ℤ × ℤ) :
      σ * s1.1 * e0.1 + τ * s1.2 * e0.2 +
          -σ * e1.1 * s0.1 + -τ * e1.2 * s0.2 =
        (σ * s1.1 * e0.1 + τ * s1.2 * e0.2) +
          ((-σ) * e1.1 * s0.1 + (-τ) * e1.2 * s0.2) := by
    ring
  simp only [disjointOrder4, challengeDisjointPairBlock,
    challengeDoubleProductBlock, challengeAddExponents, bind_assoc, pure_bind]
  simp_rw [hout]

private theorem evalDist_disjointProjectedBlock_eq (σ τ : ℤ) :
    evalDist (challengeDisjointProjectedBlock σ τ) =
      evalDist (challengeDisjointBlock σ τ) := by
  change evalDist (disjointOrder0 σ τ) = _
  exact (evalDist_disjointOrder01 σ τ).trans
    ((evalDist_disjointOrder12 σ τ).trans
      ((evalDist_disjointOrder23 σ τ).trans
        ((evalDist_disjointOrder34 σ τ).trans
          ((evalDist_disjointOrder4_pair σ τ).trans
            (evalDist_disjointPairBlock_eq σ τ)))))

private theorem evalDist_bind_five_congr
    {α₁ α₂ α₃ α₄ α₅ ρ : Type}
    {ma₁ mb₁ : ProbComp α₁} {ma₂ mb₂ : ProbComp α₂}
    {ma₃ mb₃ : ProbComp α₃} {ma₄ mb₄ : ProbComp α₄}
    {ma₅ mb₅ : ProbComp α₅}
    (h₁ : evalDist ma₁ = evalDist mb₁)
    (h₂ : evalDist ma₂ = evalDist mb₂)
    (h₃ : evalDist ma₃ = evalDist mb₃)
    (h₄ : evalDist ma₄ = evalDist mb₄)
    (h₅ : evalDist ma₅ = evalDist mb₅)
    (f : α₁ → α₂ → α₃ → α₄ → α₅ → ProbComp ρ) :
    evalDist (do
      let a₁ ← ma₁
      let a₂ ← ma₂
      let a₃ ← ma₃
      let a₄ ← ma₄
      let a₅ ← ma₅
      f a₁ a₂ a₃ a₄ a₅) =
    evalDist (do
      let b₁ ← mb₁
      let b₂ ← mb₂
      let b₃ ← mb₃
      let b₄ ← mb₄
      let b₅ ← mb₅
      f b₁ b₂ b₃ b₄ b₅) := by
  simp only [evalDist_bind, h₁, h₂, h₃, h₄, h₅]

private theorem evalDist_bind_head_congr
    {α β : Type} {mx my : ProbComp α}
    (h : evalDist mx = evalDist my) (f : α → ProbComp β) :
    evalDist (mx >>= f) = evalDist (my >>= f) := by
  simp only [evalDist_bind, h]

private theorem evalDist_projected_row_pairExponent
    (c d : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (hcol : c.2 ≠ d.2) (σ τ : ℤ) :
    evalDist (challengeProjectedRowExponentExp c d σ τ) =
      evalDist (challengePairExponentExp true σ τ) := by
  let vectorExp : ProbComp (Fin challengeParams.n → ℤ) := do
    let s0 ← ProbComp.sampleIID challengeParams.n challengePairSampler
    let e0 ← ProbComp.sampleIID challengeParams.n challengePairSampler
    let s1 ← ProbComp.sampleIID challengeParams.n d1IntSampler
    let e1 ← ProbComp.sampleIID challengeParams.n d1IntSampler
    return fun k => s1 k * (σ * (e0 k).1 + τ * (e0 k).2) +
      e1 k * ((-σ) * (s0 k).1 + (-τ) * (s0 k).2)
  have hprojected : evalDist (challengeProjectedRowExponentExp c d σ τ) =
      evalDist (do
        let blocks ← vectorExp
        let extra ← challengePairSampler
        return (∑ k, blocks k) + σ * extra.1 + τ * extra.2) := by
    simp only [challengeProjectedRowExponentExp, vectorExp, bind_assoc, pure_bind]
    apply evalDist_bind_five_congr
    · exact evalDist_challengeIntMatrix_two_cols _ _ _ _ hcol
    · exact evalDist_challengeIntMatrix_two_cols _ _ _ _ hcol
    · exact evalDist_challengeIntMatrix_row _ _ c.1
    · exact evalDist_challengeIntMatrix_row _ _ c.1
    · exact evalDist_challengeIntMatrix_two_entries _ _ _ _ _ _
        (fun h => hcol (congrArg Prod.snd h))
  have hvector : evalDist vectorExp =
      evalDist (ProbComp.sampleIID challengeParams.n (challengeRowBlock σ τ)) := by
    simpa only [vectorExp, challengeRowBlock] using
      evalDist_sampleIID_map_four challengePairSampler challengePairSampler
        d1IntSampler d1IntSampler challengeParams.n
        (fun s0 e0 s1 e1 => s1 * (σ * e0.1 + τ * e0.2) +
          e1 * ((-σ) * s0.1 + (-τ) * s0.2))
  apply hprojected.trans
  refine (evalDist_bind_head_congr hvector _).trans ?_
  have hblocks := evalDist_sampleIID_congr_local challengeParams.n
    (challengeRowBlock σ τ) (challengeSharedBlock σ τ)
    (evalDist_rowBlock_eq_sharedBlock σ τ)
  refine (evalDist_bind_head_congr hblocks _).trans ?_
  simp only [challengePairExponentExp, challengeBlockSum, challengeAddExponents,
    challengePairSampler, seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc,
    pure_bind, Function.comp_apply]
  apply evalDist_bind_congr'
  intro blocks
  apply evalDist_bind_congr'
  intro x
  apply evalDist_bind_congr'
  intro y
  congr 2

private theorem evalDist_projected_col_pairExponent
    (c d : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (hrow : c.1 ≠ d.1) (σ τ : ℤ) :
    evalDist (challengeProjectedColExponentExp c d σ τ) =
      evalDist (challengePairExponentExp true σ τ) := by
  let vectorExp : ProbComp (Fin challengeParams.n → ℤ) := do
    let s0 ← ProbComp.sampleIID challengeParams.n d1IntSampler
    let e0 ← ProbComp.sampleIID challengeParams.n d1IntSampler
    let s1 ← ProbComp.sampleIID challengeParams.n challengePairSampler
    let e1 ← ProbComp.sampleIID challengeParams.n challengePairSampler
    return fun k => e0 k * (σ * (s1 k).1 + τ * (s1 k).2) +
      s0 k * ((-σ) * (e1 k).1 + (-τ) * (e1 k).2)
  have hprojected : evalDist (challengeProjectedColExponentExp c d σ τ) =
      evalDist (do
        let blocks ← vectorExp
        let extra ← challengePairSampler
        return (∑ k, blocks k) + σ * extra.1 + τ * extra.2) := by
    simp only [challengeProjectedColExponentExp, vectorExp, bind_assoc, pure_bind]
    apply evalDist_bind_five_congr
    · exact evalDist_challengeIntMatrix_col _ _ c.2
    · exact evalDist_challengeIntMatrix_col _ _ c.2
    · exact evalDist_challengeIntMatrix_two_rows _ _ _ _ hrow
    · exact evalDist_challengeIntMatrix_two_rows _ _ _ _ hrow
    · exact evalDist_challengeIntMatrix_two_entries _ _ _ _ _ _
        (fun h => hrow (congrArg Prod.fst h))
  have hvector : evalDist vectorExp =
      evalDist (ProbComp.sampleIID challengeParams.n (challengeColBlock σ τ)) := by
    simpa only [vectorExp, challengeColBlock] using
      evalDist_sampleIID_map_four d1IntSampler d1IntSampler
        challengePairSampler challengePairSampler challengeParams.n
        (fun s0 e0 s1 e1 => e0 * (σ * s1.1 + τ * s1.2) +
          s0 * ((-σ) * e1.1 + (-τ) * e1.2))
  apply hprojected.trans
  refine (evalDist_bind_head_congr hvector _).trans ?_
  have hblocks := evalDist_sampleIID_congr_local challengeParams.n
    (challengeColBlock σ τ) (challengeSharedBlock σ τ)
    (evalDist_colBlock_eq_sharedBlock σ τ)
  refine (evalDist_bind_head_congr hblocks _).trans ?_
  simp only [challengePairExponentExp, challengeBlockSum, challengeAddExponents,
    challengePairSampler, seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc,
    pure_bind, Function.comp_apply]
  apply evalDist_bind_congr'
  intro blocks
  apply evalDist_bind_congr'
  intro x
  apply evalDist_bind_congr'
  intro y
  congr 2

private theorem evalDist_projected_disjoint_pairExponent
    (c d : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (hrow : c.1 ≠ d.1) (hcol : c.2 ≠ d.2) (σ τ : ℤ) :
    evalDist (challengeProjectedDisjointExponentExp c d σ τ) =
      evalDist (challengePairExponentExp false σ τ) := by
  let vectorExp : ProbComp (Fin challengeParams.n → ℤ) := do
    let s0 ← ProbComp.sampleIID challengeParams.n challengePairSampler
    let e0 ← ProbComp.sampleIID challengeParams.n challengePairSampler
    let s1 ← ProbComp.sampleIID challengeParams.n challengePairSampler
    let e1 ← ProbComp.sampleIID challengeParams.n challengePairSampler
    return fun k => σ * (s1 k).1 * (e0 k).1 + τ * (s1 k).2 * (e0 k).2 +
      (-σ) * (e1 k).1 * (s0 k).1 + (-τ) * (e1 k).2 * (s0 k).2
  have hprojected : evalDist (challengeProjectedDisjointExponentExp c d σ τ) =
      evalDist (do
        let blocks ← vectorExp
        let extra ← challengePairSampler
        return (∑ k, blocks k) + σ * extra.1 + τ * extra.2) := by
    simp only [challengeProjectedDisjointExponentExp, vectorExp, bind_assoc, pure_bind]
    apply evalDist_bind_five_congr
    · exact evalDist_challengeIntMatrix_two_cols _ _ _ _ hcol
    · exact evalDist_challengeIntMatrix_two_cols _ _ _ _ hcol
    · exact evalDist_challengeIntMatrix_two_rows _ _ _ _ hrow
    · exact evalDist_challengeIntMatrix_two_rows _ _ _ _ hrow
    · exact evalDist_challengeIntMatrix_two_entries _ _ _ _ _ _
        (fun h => hcol (congrArg Prod.snd h))
  have hvector : evalDist vectorExp =
      evalDist (ProbComp.sampleIID challengeParams.n
        (challengeDisjointProjectedBlock σ τ)) := by
    simpa only [vectorExp, challengeDisjointProjectedBlock] using
      evalDist_sampleIID_map_four challengePairSampler challengePairSampler
        challengePairSampler challengePairSampler challengeParams.n
        (fun s0 e0 s1 e1 => σ * s1.1 * e0.1 + τ * s1.2 * e0.2 +
          (-σ) * e1.1 * s0.1 + (-τ) * e1.2 * s0.2)
  apply hprojected.trans
  refine (evalDist_bind_head_congr hvector _).trans ?_
  have hblocks := evalDist_sampleIID_congr_local challengeParams.n
    (challengeDisjointProjectedBlock σ τ) (challengeDisjointBlock σ τ)
    (evalDist_disjointProjectedBlock_eq σ τ)
  refine (evalDist_bind_head_congr hblocks _).trans ?_
  simp only [challengePairExponentExp, challengeBlockSum, challengeAddExponents,
    challengePairSampler, seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc,
    pure_bind, Function.comp_apply]
  apply evalDist_bind_congr'
  intro blocks
  apply evalDist_bind_congr'
  intro x
  apply evalDist_bind_congr'
  intro y
  congr 2

private theorem challenge_signed_joint_moment
    (c d : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (hcd : c ≠ d) (σ τ : ℤ)
    (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    expectedValue challengeCoinsExp (fun t =>
      challengeChernoffBase ^
        (σ * challengeEntryNoiseInt c t +
          τ * challengeEntryNoiseInt d t)) =
      if c.1 = d.1 ∨ c.2 = d.2 then
        challengeSharedMoment ^ 704 * challengeOneMoment ^ 2
      else
        challengeProductMoment ^ 1408 * challengeOneMoment ^ 2 := by
  let costAux := fun t : ChallengeIntCoins =>
    challengeChernoffBase ^
      (σ * challengeEntryNoiseAux c t + τ * challengeEntryNoiseAux d t)
  have hcenter :
      expectedValue challengeCoinsExp (fun t =>
          challengeChernoffBase ^
            (σ * challengeEntryNoiseInt c t +
              τ * challengeEntryNoiseInt d t)) =
        expectedValue (centerChallengeCoins <$> challengeCoinsExp) costAux := by
    rw [expectedValue_map]
    apply congrArg (expectedValue challengeCoinsExp)
    funext t
    simp only [costAux, challengeEntryNoiseAux_center]
  have hint :
      expectedValue (centerChallengeCoins <$> challengeCoinsExp) costAux =
        expectedValue challengeIntCoinsExp costAux :=
    expectedValue_congr_evalDist evalDist_centerChallengeCoins costAux
  have hmapped :
      expectedValue challengeIntCoinsExp costAux =
        expectedValue
          ((fun t =>
              σ * challengeEntryNoiseAux c t + τ * challengeEntryNoiseAux d t) <$>
            challengeIntCoinsExp)
          (fun z => challengeChernoffBase ^ z) := by
    rw [expectedValue_map]
  rw [hcenter, hint, hmapped]
  by_cases hrow : c.1 = d.1
  · have hcol : c.2 ≠ d.2 := by
      intro h
      exact hcd (Prod.ext hrow h)
    have hdist := (evalDist_challengeInt_to_row_projected c d hrow σ τ).trans
      (evalDist_projected_row_pairExponent c d hcol σ τ)
    rw [expectedValue_congr_evalDist hdist]
    rw [expectedValue_pair_exponent true σ τ hσ hτ]
    simp [hrow]
  · by_cases hcol : c.2 = d.2
    · have hdist := (evalDist_challengeInt_to_col_projected c d hcol σ τ).trans
        (evalDist_projected_col_pairExponent c d hrow σ τ)
      rw [expectedValue_congr_evalDist hdist]
      rw [expectedValue_pair_exponent true σ τ hσ hτ]
      simp [hcol]
    · have hdist :=
        (evalDist_challengeInt_to_disjoint_projected c d σ τ).trans
          (evalDist_projected_disjoint_pairExponent c d hrow hcol σ τ)
      rw [expectedValue_congr_evalDist hdist]
      rw [expectedValue_pair_exponent false σ τ hσ hτ]
      simp [hrow, hcol]

private lemma large_natAbs_sign (z : ℤ) (hz : 256 ≤ z.natAbs) :
    (256 : ℤ) ≤ z ∨ (256 : ℤ) ≤ -z := by
  have hz' : (256 : ℤ) ≤ (z.natAbs : ℤ) := by
    exact_mod_cast hz
  by_cases hnonneg : 0 ≤ z
  · left
    rw [Int.natAbs_of_nonneg hnonneg] at hz'
    exact hz'
  · right
    have hnonpos : z ≤ 0 := le_of_lt (lt_of_not_ge hnonneg)
    rw [Int.ofNat_natAbs_of_nonpos hnonpos] at hz'
    exact hz'

private def challengeSignedPairEvent
    (c d : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (σ τ : ℤ)
    (t : InitKey challengeParams × SendACoins challengeParams) : Prop :=
  256 ≤ σ * challengeEntryNoiseInt c t ∧
    256 ≤ τ * challengeEntryNoiseInt d t

private theorem challenge_signed_pair_tail_le
    (c d : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (hcd : c ≠ d) (σ τ : ℤ)
    (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    Pr[challengeSignedPairEvent c d σ τ | challengeCoinsExp] ≤
      ((5 : ℝ≥0∞) / 6) ^ 512 *
        (if c.1 = d.1 ∨ c.2 = d.2 then
          challengeSharedMoment ^ 704 * challengeOneMoment ^ 2
        else
          challengeProductMoment ^ 1408 * challengeOneMoment ^ 2) := by
  let K : ℝ≥0∞ := ((5 : ℝ≥0∞) / 6) ^ 512
  let cost := fun t : InitKey challengeParams × SendACoins challengeParams =>
    K * challengeChernoffBase ^
      (σ * challengeEntryNoiseInt c t + τ * challengeEntryNoiseInt d t)
  have hmarkov := probEvent_le_tsum_probOutput_mul_cost challengeCoinsExp
    (challengeSignedPairEvent c d σ τ) cost
  have hcost : ∀ t, challengeSignedPairEvent c d σ τ t → 1 ≤ cost t := by
    intro t ht
    have hexp : (512 : ℤ) ≤
        σ * challengeEntryNoiseInt c t + τ * challengeEntryNoiseInt d t := by
      exact add_le_add ht.1 ht.2
    have hpow := ENNReal.zpow_le_of_le
      (show 1 ≤ challengeChernoffBase by
        unfold challengeChernoffBase
        apply (ENNReal.le_div_iff_mul_le
          (Or.inl (by norm_num)) (Or.inl (by norm_num))).2
        norm_num) hexp
    dsimp [cost, K]
    calc
      (1 : ℝ≥0∞) = ((5 : ℝ≥0∞) / 6) ^ 512 *
          challengeChernoffBase ^ (512 : ℤ) := by
        symm
        rw [zpow_ofNat]
        rw [← mul_pow]
        have hratio : ((5 : ℝ≥0∞) / 6) * challengeChernoffBase = 1 := by
          unfold challengeChernoffBase
          calc
            ((5 : ℝ≥0∞) / 6) * ((6 : ℝ≥0∞) / 5) =
                (((5 : ℝ≥0∞) / 6) * 6) / 5 := by
              simp only [div_eq_mul_inv]
              ac_rfl
            _ = (5 : ℝ≥0∞) / 5 := by
              rw [ENNReal.div_mul_cancel]
              · norm_num
              · norm_num
            _ = 1 := ENNReal.div_self (by norm_num) (by norm_num)
        rw [hratio, one_pow]
      _ ≤ ((5 : ℝ≥0∞) / 6) ^ 512 *
          challengeChernoffBase ^
            (σ * challengeEntryNoiseInt c t + τ * challengeEntryNoiseInt d t) :=
        mul_le_mul_right hpow _
  specialize hmarkov hcost
  rw [← expectedValue_def] at hmarkov
  calc
    Pr[challengeSignedPairEvent c d σ τ | challengeCoinsExp] ≤
        expectedValue challengeCoinsExp cost := hmarkov
    _ = K * expectedValue challengeCoinsExp (fun t =>
        challengeChernoffBase ^
          (σ * challengeEntryNoiseInt c t + τ * challengeEntryNoiseInt d t)) := by
      dsimp only [cost]
      exact expectedValue_const_mul_left challengeCoinsExp K _
    _ = ((5 : ℝ≥0∞) / 6) ^ 512 *
        (if c.1 = d.1 ∨ c.2 = d.2 then
          challengeSharedMoment ^ 704 * challengeOneMoment ^ 2
        else
          challengeProductMoment ^ 1408 * challengeOneMoment ^ 2) := by
      rw [challenge_signed_joint_moment c d hcd σ τ hσ hτ]

private theorem challenge_four_signed_tails_le
    (c d : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (hcd : c ≠ d) :
    Pr[fun t =>
      challengeSignedPairEvent c d 1 1 t ∨
      challengeSignedPairEvent c d 1 (-1) t ∨
      challengeSignedPairEvent c d (-1) 1 t ∨
      challengeSignedPairEvent c d (-1) (-1) t |
      challengeCoinsExp] ≤ (1 : ℝ≥0∞) / 2 ^ 70 := by
  have hpp := challenge_signed_pair_tail_le c d hcd 1 1 (Or.inl rfl) (Or.inl rfl)
  have hpn := challenge_signed_pair_tail_le c d hcd 1 (-1) (Or.inl rfl) (Or.inr rfl)
  have hnp := challenge_signed_pair_tail_le c d hcd (-1) 1 (Or.inr rfl) (Or.inl rfl)
  have hnn := challenge_signed_pair_tail_le c d hcd (-1) (-1) (Or.inr rfl) (Or.inr rfl)
  have hlast := probEvent_or_le challengeCoinsExp
    (challengeSignedPairEvent c d (-1) 1)
    (challengeSignedPairEvent c d (-1) (-1))
  have hrest := (probEvent_or_le challengeCoinsExp
    (challengeSignedPairEvent c d 1 (-1))
    (fun t =>
      challengeSignedPairEvent c d (-1) 1 t ∨
      challengeSignedPairEvent c d (-1) (-1) t)).trans
    (add_le_add_right hlast _)
  have hunion := (probEvent_or_le challengeCoinsExp
    (challengeSignedPairEvent c d 1 1)
    (fun t =>
      challengeSignedPairEvent c d 1 (-1) t ∨
      challengeSignedPairEvent c d (-1) 1 t ∨
      challengeSignedPairEvent c d (-1) (-1) t)).trans
    (add_le_add_right hrest _)
  have hsum := hunion.trans
    (add_le_add hpp (add_le_add hpn (add_le_add hnp hnn)))
  by_cases hshare : c.1 = d.1 ∨ c.2 = d.2
  · rw [if_pos hshare] at hsum
    exact hsum.trans <| by
      have harith := challenge_pair_chernoff_arithmetic.1
      let q : ℝ≥0∞ := ((5 : ℝ≥0∞) / 6) ^ 512 *
        (challengeSharedMoment ^ 704 * challengeOneMoment ^ 2)
      change q + (q + (q + q)) ≤ (1 : ℝ≥0∞) / 2 ^ 70
      calc
        q + (q + (q + q)) = 4 * q := by ring
        _ ≤ (1 : ℝ≥0∞) / 2 ^ 70 := by
          dsimp only [q]
          unfold challengeSharedMoment challengeOneMoment
          have harith' :
              (4 : ℝ≥0∞) * ((5 : ℝ≥0∞) / 6) ^ 512 *
                  ((127847491742921604065083548949681 : ℝ≥0∞) /
                    120367356051456000000000000000000) ^ 704 *
                  ((784927 : ℝ≥0∞) / 768000) ^ 2 ≤
                (1 : ℝ≥0∞) / 2 ^ 70 := by
            apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
            simp only [ENNReal.toReal_mul, ENNReal.toReal_div,
              ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_one]
            simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
              Rat.cast_ofNat, Rat.cast_one] using (Rat.cast_le (K := ℝ)).2 harith
          simpa only [mul_assoc] using harith'
  · rw [if_neg hshare] at hsum
    exact hsum.trans <| by
      have harith := challenge_pair_chernoff_arithmetic.2
      let q : ℝ≥0∞ := ((5 : ℝ≥0∞) / 6) ^ 512 *
        (challengeProductMoment ^ 1408 * challengeOneMoment ^ 2)
      change q + (q + (q + q)) ≤ (1 : ℝ≥0∞) / 2 ^ 70
      calc
        q + (q + (q + q)) = 4 * q := by ring
        _ ≤ (1 : ℝ≥0∞) / 2 ^ 70 := by
          dsimp only [q]
          unfold challengeProductMoment challengeOneMoment
          have harith' :
              (4 : ℝ≥0∞) * ((5 : ℝ≥0∞) / 6) ^ 512 *
                  ((73796729825894041 : ℝ≥0∞) / 71663616000000000) ^ 1408 *
                  ((784927 : ℝ≥0∞) / 768000) ^ 2 ≤
                (1 : ℝ≥0∞) / 2 ^ 70 := by
            apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
            simp only [ENNReal.toReal_mul, ENNReal.toReal_div,
              ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_one]
            simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
              Rat.cast_ofNat, Rat.cast_one] using (Rat.cast_le (K := ℝ)).2 harith
          simpa only [mul_assoc] using harith'

/-- In the exact first-exchange model with a uniformly sampled public matrix and exact paper
`D₁` noise, the joint mismatch probability at any two distinct coordinates is at most `2⁻⁷⁰`.
This includes shared-row and shared-column pairs and accounts for their dependence. -/
theorem probEvent_challengeEntryMismatch_pair_le
    (c d : Fin challengeParams.nbar × Fin challengeParams.nbar)
    (hcd : c ≠ d) :
    Pr[fun t =>
      challengeEntryMismatch c t ∧ challengeEntryMismatch d t |
      challengeCoinsExp] ≤
      (1 : ℝ≥0∞) / 2 ^ 70 := by
  refine (probEvent_mono'' (mx := challengeCoinsExp) ?_).trans
    (challenge_four_signed_tails_le c d hcd)
  rintro t ⟨hc, hd⟩
  rcases large_natAbs_sign _ (challengeEntryMismatch_imp_large_int c t hc) with hc' | hc'
  · rcases large_natAbs_sign _ (challengeEntryMismatch_imp_large_int d t hd) with hd' | hd'
    · exact Or.inl ⟨by simpa [challengeSignedPairEvent] using hc',
        by simpa [challengeSignedPairEvent] using hd'⟩
    · exact Or.inr <| Or.inl ⟨by simpa [challengeSignedPairEvent] using hc',
        by simpa [challengeSignedPairEvent] using hd'⟩
  · rcases large_natAbs_sign _ (challengeEntryMismatch_imp_large_int d t hd) with hd' | hd'
    · exact Or.inr <| Or.inr <| Or.inl
        ⟨by simpa [challengeSignedPairEvent] using hc',
          by simpa [challengeSignedPairEvent] using hd'⟩
    · exact Or.inr <| Or.inr <| Or.inr
        ⟨by simpa [challengeSignedPairEvent] using hc',
          by simpa [challengeSignedPairEvent] using hd'⟩

end lweCKA
