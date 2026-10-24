/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.ConcreteMoments
import SecureMessaging.CKA.FromLWE.EntryNoise
import VCVio.EvalDist.Monad.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Exact fourth moment of first-exchange entry noise

This file proves the fourth moment of the actual integer experiment for one entry of the
first-exchange noise. The calculation uses the finite support of the concrete sampler and a
symbolic recurrence over the vector length.
-/

open OracleComp ENNReal
open scoped BigOperators

namespace lweCKA

private noncomputable def finiteRealExpectation
    (mx : ProbComp ℤ) (f : ℤ → ℝ) : ℝ :=
  ∑ z ∈ finSupport mx, (Pr[= z | mx]).toReal * f z

private def d3DifferenceBlock : ProbComp ℤ := do
  let s0 ← d3IntSampler
  let e0 ← d3IntSampler
  let s1 ← d3IntSampler
  let e1 ← d3IntSampler
  return s1 * e0 - e1 * s0

private def entryNoiseIntExpAux (n : ℕ) : ProbComp ℤ := do
  let s0 ← ProbComp.sampleIID n d3IntSampler
  let e0 ← ProbComp.sampleIID n d3IntSampler
  let s1 ← ProbComp.sampleIID n d3IntSampler
  let e1 ← ProbComp.sampleIID n d3IntSampler
  let extra ← d3IntSampler
  return (∑ k : Fin n, s1 k * e0 k) -
      (∑ k : Fin n, e1 k * s0 k) + extra

private lemma summable_probOutput_toReal_mul
    (mx : ProbComp ℤ) (f : ℤ → ℝ) :
    Summable (fun z : ℤ ↦ (Pr[= z | mx]).toReal * f z) := by
  apply summable_of_ne_finset_zero (s := finSupport mx)
  intro z hz
  rw [probOutput_eq_zero' mx z hz]
  simp

private theorem finiteRealExpectation_eq_tsum
    (mx : ProbComp ℤ) (f : ℤ → ℝ) :
    finiteRealExpectation mx f =
      ∑' z : ℤ, (Pr[= z | mx]).toReal * f z := by
  rw [finiteRealExpectation, tsum_eq_sum (s := finSupport mx)]
  intro z hz
  rw [probOutput_eq_zero' mx z hz]
  simp

private theorem finiteRealExpectation_bind
    (mx : ProbComp ℤ) (my : ℤ → ProbComp ℤ) (f : ℤ → ℝ) :
    finiteRealExpectation (mx >>= my) f =
      finiteRealExpectation mx
        (fun x => finiteRealExpectation (my x) f) := by
  have hToReal (z : ℤ) :
      (Pr[= z | mx >>= my]).toReal =
        ∑ x ∈ finSupport mx,
          (Pr[= x | mx]).toReal * (Pr[= z | my x]).toReal := by
    rw [probOutput_bind_eq_sum_finSupport, ENNReal.toReal_sum]
    · simp_rw [ENNReal.toReal_mul]
    · intro x _
      exact ENNReal.mul_ne_top probOutput_ne_top probOutput_ne_top
  rw [finiteRealExpectation_eq_tsum, finiteRealExpectation]
  simp_rw [hToReal]
  simp_rw [Finset.sum_mul]
  simp_rw [mul_assoc]
  rw [Summable.tsum_finsetSum]
  · apply Finset.sum_congr rfl
    intro x _
    rw [tsum_mul_left]
    congr 1
    exact finiteRealExpectation_eq_tsum (my x) f |>.symm
  · intro x hx
    exact (summable_probOutput_toReal_mul (my x) f).mul_left _

private theorem finiteRealExpectation_ofReal
    (mx : ProbComp ℤ) (f : ℤ → ℝ)
    (hf : ∀ z : ℤ, 0 ≤ f z) :
    OracleComp.EvalDist.expectedValue mx
        (fun z => ENNReal.ofReal (f z)) =
      ENNReal.ofReal (finiteRealExpectation mx f) := by
  rw [OracleComp.EvalDist.expectedValue_def,
    tsum_eq_sum (s := finSupport mx)]
  · rw [finiteRealExpectation, ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro z _
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal probOutput_ne_top]
    · intro z _
      exact mul_nonneg ENNReal.toReal_nonneg (hf z)
  · intro z hz
    rw [probOutput_eq_zero' mx z hz]
    simp

private lemma finiteRealExpectation_pure (x : ℤ) (f : ℤ → ℝ) :
    finiteRealExpectation (pure x : ProbComp ℤ) f = f x := by
  rw [finiteRealExpectation_eq_tsum]
  exact tsum_eq_single x (fun z hz => by simp [probOutput_pure, hz]) |>.trans (by simp)

private lemma finiteRealExpectation_congr
    {mx my : ProbComp ℤ} (h : evalDist mx = evalDist my) (f : ℤ → ℝ) :
    finiteRealExpectation mx f = finiteRealExpectation my f := by
  rw [finiteRealExpectation_eq_tsum, finiteRealExpectation_eq_tsum]
  apply tsum_congr
  intro z
  rw [(evalDist_ext_iff.mp h) z]

private lemma finiteRealExpectation_linear_two
    (mx : ProbComp ℤ) (f g : ℤ → ℝ) (a b c : ℝ) :
    finiteRealExpectation mx (fun z => a * f z + b * g z + c) =
      a * finiteRealExpectation mx f + b * finiteRealExpectation mx g + c := by
  have hmassENN : ∑ z ∈ finSupport mx, Pr[= z | mx] = 1 :=
    sum_finSupport_probOutput_of_liftM_PMF mx
  have hmass : ∑ z ∈ finSupport mx, (Pr[= z | mx]).toReal = 1 := by
    rw [← ENNReal.toReal_sum]
    · rw [hmassENN]
      simp
    · intro z _
      exact probOutput_ne_top
  unfold finiteRealExpectation
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  simp_rw [← mul_assoc, mul_comm _ a, mul_assoc,
    ← mul_assoc, mul_comm _ b, mul_assoc]
  rw [Finset.mul_sum, Finset.mul_sum, hmass]
  ring

private lemma finiteRealExpectation_d3_quartic
    (f : ℤ → ℝ) (c0 c1 c2 c3 c4 : ℝ)
    (hf : ∀ z : ℤ, f z =
      c0 + c1 * (z : ℝ) + c2 * (z : ℝ) ^ 2 +
        c3 * (z : ℝ) ^ 3 + c4 * (z : ℝ) ^ 4) :
    finiteRealExpectation d3IntSampler f =
      c0 + c2 * ((117 : ℝ) / 64) + c4 * ((1269 : ℝ) / 128) := by
  have hs (k : ℕ) :
      Summable (fun z : ℤ ↦ (Pr[= z | d3IntSampler]).toReal * (z : ℝ) ^ k) :=
    summable_probOutput_toReal_mul d3IntSampler (fun z => (z : ℝ) ^ k)
  have h0 := (hs 0).mul_right c0
  have h1 := (hs 1).mul_right c1
  have h2 := (hs 2).mul_right c2
  have h3 := (hs 3).mul_right c3
  have h4 := (hs 4).mul_right c4
  rw [finiteRealExpectation_eq_tsum]
  calc
    (∑' z : ℤ, (Pr[= z | d3IntSampler]).toReal * f z) =
        ∑' z : ℤ,
          (((((Pr[= z | d3IntSampler]).toReal * (z : ℝ) ^ 0 * c0 +
            (Pr[= z | d3IntSampler]).toReal * (z : ℝ) ^ 1 * c1) +
            (Pr[= z | d3IntSampler]).toReal * (z : ℝ) ^ 2 * c2) +
            (Pr[= z | d3IntSampler]).toReal * (z : ℝ) ^ 3 * c3) +
            (Pr[= z | d3IntSampler]).toReal * (z : ℝ) ^ 4 * c4) := by
          apply tsum_congr
          intro z
          rw [hf z]
          ring
    _ =
        (((∑' z : ℤ,
              (Pr[= z | d3IntSampler]).toReal * (z : ℝ) ^ 0) * c0 +
          (∑' z : ℤ,
              (Pr[= z | d3IntSampler]).toReal * (z : ℝ) ^ 1) * c1) +
          (∑' z : ℤ,
              (Pr[= z | d3IntSampler]).toReal * (z : ℝ) ^ 2) * c2) +
          (∑' z : ℤ,
              (Pr[= z | d3IntSampler]).toReal * (z : ℝ) ^ 3) * c3 +
          (∑' z : ℤ,
              (Pr[= z | d3IntSampler]).toReal * (z : ℝ) ^ 4) * c4 := by
          rw [(((h0.add h1).add h2).add h3).tsum_add h4,
            ((h0.add h1).add h2).tsum_add h3,
            (h0.add h1).tsum_add h2, h0.tsum_add h1,
            (hs 0).tsum_mul_right, (hs 1).tsum_mul_right,
            (hs 2).tsum_mul_right, (hs 3).tsum_mul_right,
            (hs 4).tsum_mul_right]
    _ = c0 + c2 * ((117 : ℝ) / 64) + c4 * ((1269 : ℝ) / 128) := by
          rw [tsum_probOutput_d3IntSampler_mul_pow 0,
            tsum_probOutput_d3IntSampler_mul_pow 1,
            tsum_probOutput_d3IntSampler_mul_pow 2,
            tsum_probOutput_d3IntSampler_mul_pow 3,
            tsum_probOutput_d3IntSampler_mul_pow 4,
            d3Moment_zero, d3Moment_one, d3Moment_two,
            d3Moment_three, d3Moment_four]
          ring

private theorem finiteRealExpectation_d3_affine_sq (a b : ℝ) :
    finiteRealExpectation d3IntSampler
        (fun z => (a + b * (z : ℝ)) ^ 2) =
      a ^ 2 + b ^ 2 * ((117 : ℝ) / 64) := by
  convert finiteRealExpectation_d3_quartic
      (fun z : ℤ => (a + b * (z : ℝ)) ^ 2)
      (a ^ 2) (2 * a * b) (b ^ 2) 0 0 (by
        intro z
        ring) using 1
  ring

private theorem finiteRealExpectation_d3_affine_fourth (a b : ℝ) :
    finiteRealExpectation d3IntSampler
        (fun z => (a + b * (z : ℝ)) ^ 4) =
      a ^ 4 +
        6 * a ^ 2 * b ^ 2 * ((117 : ℝ) / 64) +
        b ^ 4 * ((1269 : ℝ) / 128) := by
  convert finiteRealExpectation_d3_quartic
      (fun z : ℤ => (a + b * (z : ℝ)) ^ 4)
      (a ^ 4) (4 * a ^ 3 * b) (6 * a ^ 2 * b ^ 2)
      (4 * a * b ^ 3) (b ^ 4) (by
        intro z
        ring) using 1

private theorem finiteRealExpectation_block_shift_sq (a : ℝ) :
    finiteRealExpectation d3DifferenceBlock
        (fun z => (a + (z : ℝ)) ^ 2) =
      a ^ 2 + 2 * ((13689 : ℝ) / 4096) := by
  unfold d3DifferenceBlock
  simp_rw [finiteRealExpectation_bind, finiteRealExpectation_pure]
  simp only [Int.cast_sub, Int.cast_mul]
  calc
    _ = finiteRealExpectation d3IntSampler (fun s0 =>
          finiteRealExpectation d3IntSampler (fun e0 =>
            finiteRealExpectation d3IntSampler (fun s1 =>
              (a + (s1 : ℝ) * (e0 : ℝ)) ^ 2 +
                (s0 : ℝ) ^ 2 * ((117 : ℝ) / 64)))) := by
        apply congrArg (finiteRealExpectation d3IntSampler)
        funext s0
        apply congrArg (finiteRealExpectation d3IntSampler)
        funext e0
        apply congrArg (finiteRealExpectation d3IntSampler)
        funext s1
        convert finiteRealExpectation_d3_quartic
            (fun e1 : ℤ =>
              (a + ((s1 : ℝ) * (e0 : ℝ) - (e1 : ℝ) * (s0 : ℝ))) ^ 2)
            ((a + (s1 : ℝ) * (e0 : ℝ)) ^ 2)
            (-2 * (a + (s1 : ℝ) * (e0 : ℝ)) * (s0 : ℝ))
            ((s0 : ℝ) ^ 2) 0 0 (by
              intro z
              ring) using 1
        all_goals ring_nf
    _ = finiteRealExpectation d3IntSampler (fun s0 =>
          finiteRealExpectation d3IntSampler (fun e0 =>
            a ^ 2 + (e0 : ℝ) ^ 2 * ((117 : ℝ) / 64) +
              (s0 : ℝ) ^ 2 * ((117 : ℝ) / 64))) := by
        apply congrArg (finiteRealExpectation d3IntSampler)
        funext s0
        apply congrArg (finiteRealExpectation d3IntSampler)
        funext e0
        convert finiteRealExpectation_d3_quartic
            (fun s1 : ℤ =>
              (a + (s1 : ℝ) * (e0 : ℝ)) ^ 2 +
                (s0 : ℝ) ^ 2 * ((117 : ℝ) / 64))
            (a ^ 2 + (s0 : ℝ) ^ 2 * ((117 : ℝ) / 64))
            (2 * a * (e0 : ℝ)) ((e0 : ℝ) ^ 2) 0 0 (by
              intro z
              ring) using 1
        all_goals ring_nf
    _ = finiteRealExpectation d3IntSampler (fun s0 =>
          a ^ 2 + 2 * ((13689 : ℝ) / 4096) +
            ((s0 : ℝ) ^ 2 * ((117 : ℝ) / 64) -
              ((13689 : ℝ) / 4096))) := by
        apply congrArg (finiteRealExpectation d3IntSampler)
        funext s0
        convert finiteRealExpectation_d3_quartic
            (fun e0 : ℤ =>
              a ^ 2 + (e0 : ℝ) ^ 2 * ((117 : ℝ) / 64) +
                (s0 : ℝ) ^ 2 * ((117 : ℝ) / 64))
            (a ^ 2 + (s0 : ℝ) ^ 2 * ((117 : ℝ) / 64)) 0
            ((117 : ℝ) / 64) 0 0 (by
              intro z
              ring) using 1
        all_goals (norm_num; ring_nf)
    _ = a ^ 2 + 2 * ((13689 : ℝ) / 4096) := by
        convert finiteRealExpectation_d3_quartic
            (fun s0 : ℤ =>
              a ^ 2 + 2 * ((13689 : ℝ) / 4096) +
                ((s0 : ℝ) ^ 2 * ((117 : ℝ) / 64) -
                  ((13689 : ℝ) / 4096)))
            (a ^ 2 + ((13689 : ℝ) / 4096)) 0
            ((117 : ℝ) / 64) 0 0 (by
              intro z
              ring) using 1
        all_goals (norm_num; ring_nf)

private theorem finiteRealExpectation_block_shift_fourth (a : ℝ) :
    finiteRealExpectation d3DifferenceBlock
        (fun z => (a + (z : ℝ)) ^ 4) =
      a ^ 4 +
        12 * ((13689 : ℝ) / 4096) * a ^ 2 +
        2 * ((1610361 : ℝ) / 16384) +
        6 * (((13689 : ℝ) / 4096) ^ 2) := by
  let v : ℝ := 117 / 64
  let m : ℝ := 1269 / 128
  unfold d3DifferenceBlock
  simp_rw [finiteRealExpectation_bind, finiteRealExpectation_pure]
  simp only [Int.cast_sub, Int.cast_mul]
  calc
    _ = finiteRealExpectation d3IntSampler (fun s0 =>
          finiteRealExpectation d3IntSampler (fun e0 =>
            finiteRealExpectation d3IntSampler (fun s1 =>
              (a + (s1 : ℝ) * (e0 : ℝ)) ^ 4 +
                6 * (a + (s1 : ℝ) * (e0 : ℝ)) ^ 2 *
                  (s0 : ℝ) ^ 2 * v +
                (s0 : ℝ) ^ 4 * m))) := by
        apply congrArg (finiteRealExpectation d3IntSampler)
        funext s0
        apply congrArg (finiteRealExpectation d3IntSampler)
        funext e0
        apply congrArg (finiteRealExpectation d3IntSampler)
        funext s1
        convert finiteRealExpectation_d3_quartic
            (fun e1 : ℤ =>
              (a + ((s1 : ℝ) * (e0 : ℝ) - (e1 : ℝ) * (s0 : ℝ))) ^ 4)
            ((a + (s1 : ℝ) * (e0 : ℝ)) ^ 4)
            (-4 * (a + (s1 : ℝ) * (e0 : ℝ)) ^ 3 * (s0 : ℝ))
            (6 * (a + (s1 : ℝ) * (e0 : ℝ)) ^ 2 * (s0 : ℝ) ^ 2)
            (-4 * (a + (s1 : ℝ) * (e0 : ℝ)) * (s0 : ℝ) ^ 3)
            ((s0 : ℝ) ^ 4) (by
              intro z
              ring) using 1
    _ = finiteRealExpectation d3IntSampler (fun s0 =>
          finiteRealExpectation d3IntSampler (fun e0 =>
            a ^ 4 + 6 * a ^ 2 * (e0 : ℝ) ^ 2 * v +
              (e0 : ℝ) ^ 4 * m +
              6 * (s0 : ℝ) ^ 2 * v *
                (a ^ 2 + (e0 : ℝ) ^ 2 * v) +
              (s0 : ℝ) ^ 4 * m)) := by
        apply congrArg (finiteRealExpectation d3IntSampler)
        funext s0
        apply congrArg (finiteRealExpectation d3IntSampler)
        funext e0
        convert finiteRealExpectation_d3_quartic
            (fun s1 : ℤ =>
              (a + (s1 : ℝ) * (e0 : ℝ)) ^ 4 +
                6 * (a + (s1 : ℝ) * (e0 : ℝ)) ^ 2 *
                  (s0 : ℝ) ^ 2 * v +
                (s0 : ℝ) ^ 4 * m)
            (a ^ 4 + 6 * a ^ 2 * (s0 : ℝ) ^ 2 * v + (s0 : ℝ) ^ 4 * m)
            (4 * a ^ 3 * (e0 : ℝ) +
              12 * a * (e0 : ℝ) * (s0 : ℝ) ^ 2 * v)
            (6 * a ^ 2 * (e0 : ℝ) ^ 2 +
              6 * (e0 : ℝ) ^ 2 * (s0 : ℝ) ^ 2 * v)
            (4 * a * (e0 : ℝ) ^ 3) ((e0 : ℝ) ^ 4) (by
              intro z
              ring) using 1
        all_goals (dsimp [v, m]; ring)
    _ = finiteRealExpectation d3IntSampler (fun s0 =>
          a ^ 4 + 6 * a ^ 2 * v ^ 2 + m ^ 2 +
            6 * (s0 : ℝ) ^ 2 * v * (a ^ 2 + v ^ 2) +
            (s0 : ℝ) ^ 4 * m) := by
        apply congrArg (finiteRealExpectation d3IntSampler)
        funext s0
        convert finiteRealExpectation_d3_quartic
            (fun e0 : ℤ =>
              a ^ 4 + 6 * a ^ 2 * (e0 : ℝ) ^ 2 * v +
                (e0 : ℝ) ^ 4 * m +
                6 * (s0 : ℝ) ^ 2 * v *
                  (a ^ 2 + (e0 : ℝ) ^ 2 * v) +
                (s0 : ℝ) ^ 4 * m)
            (a ^ 4 + 6 * (s0 : ℝ) ^ 2 * v * a ^ 2 + (s0 : ℝ) ^ 4 * m)
            0 (6 * a ^ 2 * v + 6 * (s0 : ℝ) ^ 2 * v ^ 2) 0 m (by
              intro z
              ring) using 1
        all_goals (dsimp [v, m]; ring)
    _ = a ^ 4 + 12 * v ^ 2 * a ^ 2 + 2 * m ^ 2 + 6 * (v ^ 2) ^ 2 := by
        convert finiteRealExpectation_d3_quartic
            (fun s0 : ℤ =>
              a ^ 4 + 6 * a ^ 2 * v ^ 2 + m ^ 2 +
                6 * (s0 : ℝ) ^ 2 * v * (a ^ 2 + v ^ 2) +
                (s0 : ℝ) ^ 4 * m)
            (a ^ 4 + 6 * a ^ 2 * v ^ 2 + m ^ 2) 0
            (6 * v * (a ^ 2 + v ^ 2)) 0 m (by
              intro z
              ring) using 1
        all_goals (dsimp [v, m]; ring)
    _ = a ^ 4 +
        12 * ((13689 : ℝ) / 4096) * a ^ 2 +
        2 * ((1610361 : ℝ) / 16384) +
        6 * (((13689 : ℝ) / 4096) ^ 2) := by
      dsimp [v, m]
      norm_num

private lemma evalDist_bind_move_after_two
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
    _ = _ := evalDist_bind_congr' mb fun b =>
      evalDist_bind_bind_swap ma mc (fun a c => f a b c)

private lemma evalDist_bind_move_after_three
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

private lemma evalDist_bind_move_after_four
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

private lemma evalDist_bind_rotate_four_heads
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

private theorem evalDist_entryNoiseIntExpAux_succ (n : ℕ) :
    evalDist (entryNoiseIntExpAux (n + 1)) =
      evalDist (do
        let rest ← entryNoiseIntExpAux n
        let step ← d3DifferenceBlock
        return rest + step) := by
  let tail : ProbComp (Fin n → ℤ) := Fin.mOfFn n fun _ => d3IntSampler
  let finish (s0 : ℤ) (s0s : Fin n → ℤ) (e0 : ℤ) (e0s : Fin n → ℤ)
      (s1 : ℤ) (s1s : Fin n → ℤ) (e1 : ℤ) (e1s : Fin n → ℤ)
      (extra : ℤ) : ProbComp ℤ :=
    pure ((∑ k, Fin.cons s1 s1s k * Fin.cons e0 e0s k) -
      (∑ k, Fin.cons e1 e1s k * Fin.cons s0 s0s k) + extra)
  simp only [entryNoiseIntExpAux, d3DifferenceBlock, ProbComp.sampleIID,
    Fin.mOfFn, bind_assoc, pure_bind]
  change evalDist (do
      let s0 ← d3IntSampler
      let s0s ← tail
      let e0 ← d3IntSampler
      let e0s ← tail
      let s1 ← d3IntSampler
      let s1s ← tail
      let e1 ← d3IntSampler
      let e1s ← tail
      let extra ← d3IntSampler
      finish s0 s0s e0 e0s s1 s1s e1 e1s extra) = _
  calc
    _ = evalDist (do
          let s0s ← tail
          let e0s ← tail
          let s1s ← tail
          let e1s ← tail
          let extra ← d3IntSampler
          let s0 ← d3IntSampler
          let e0 ← d3IntSampler
          let s1 ← d3IntSampler
          let e1 ← d3IntSampler
          finish s0 s0s e0 e0s s1 s1s e1 e1s extra) :=
        evalDist_bind_rotate_four_heads
          d3IntSampler tail d3IntSampler tail d3IntSampler tail
          d3IntSampler tail d3IntSampler finish
    _ = _ := by
        refine evalDist_bind_congr' tail fun s0s => ?_
        refine evalDist_bind_congr' tail fun e0s => ?_
        refine evalDist_bind_congr' tail fun s1s => ?_
        refine evalDist_bind_congr' tail fun e1s => ?_
        refine evalDist_bind_congr' d3IntSampler fun extra => ?_
        refine evalDist_bind_congr' d3IntSampler fun s0 => ?_
        refine evalDist_bind_congr' d3IntSampler fun e0 => ?_
        refine evalDist_bind_congr' d3IntSampler fun s1 => ?_
        refine evalDist_bind_congr' d3IntSampler fun e1 => ?_
        simp only [finish, evalDist_pure]
        congr 1
        simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
        ring

private theorem finiteRealExpectation_entryNoiseIntExpAux_moments
    (n : ℕ) :
    finiteRealExpectation (entryNoiseIntExpAux n)
        (fun z => (z : ℝ) ^ 2) =
      (2 * (n : ℝ)) * ((13689 : ℝ) / 4096) +
        (117 : ℝ) / 64 ∧
    finiteRealExpectation (entryNoiseIntExpAux n)
        (fun z => (z : ℝ) ^ 4) =
      (2 * (n : ℝ)) * ((1610361 : ℝ) / 16384) +
        3 * (2 * (n : ℝ)) * (2 * (n : ℝ) - 1) *
          (((13689 : ℝ) / 4096) ^ 2) +
        6 * (2 * (n : ℝ)) * ((13689 : ℝ) / 4096) *
          ((117 : ℝ) / 64) +
        (1269 : ℝ) / 128 := by
  induction n with
  | zero =>
      constructor
      · unfold entryNoiseIntExpAux
        simp only [ProbComp.sampleIID, Fin.mOfFn]
        convert finiteRealExpectation_d3_affine_sq 0 1 using 1
        all_goals norm_num
      · unfold entryNoiseIntExpAux
        simp only [ProbComp.sampleIID, Fin.mOfFn]
        convert finiteRealExpectation_d3_affine_fourth 0 1 using 1
        all_goals norm_num
  | succ n ih =>
      constructor
      · calc
          finiteRealExpectation (entryNoiseIntExpAux (n + 1))
              (fun z => (z : ℝ) ^ 2) =
              finiteRealExpectation (do
                  let rest ← entryNoiseIntExpAux n
                  let step ← d3DifferenceBlock
                  return rest + step)
                (fun z => (z : ℝ) ^ 2) :=
            finiteRealExpectation_congr (evalDist_entryNoiseIntExpAux_succ n) _
          _ = finiteRealExpectation (entryNoiseIntExpAux n) (fun rest =>
                finiteRealExpectation d3DifferenceBlock
                  (fun step => ((rest + step : ℤ) : ℝ) ^ 2)) := by
              simp_rw [finiteRealExpectation_bind, finiteRealExpectation_pure]
          _ = finiteRealExpectation (entryNoiseIntExpAux n) (fun rest =>
                (rest : ℝ) ^ 2 + 2 * ((13689 : ℝ) / 4096)) := by
              apply congrArg (finiteRealExpectation (entryNoiseIntExpAux n))
              funext rest
              simpa only [Int.cast_add] using
                finiteRealExpectation_block_shift_sq (rest : ℝ)
          _ = 1 * finiteRealExpectation (entryNoiseIntExpAux n)
                  (fun z => (z : ℝ) ^ 2) +
                0 * finiteRealExpectation (entryNoiseIntExpAux n)
                  (fun z => (z : ℝ) ^ 4) +
                2 * ((13689 : ℝ) / 4096) := by
              convert finiteRealExpectation_linear_two (entryNoiseIntExpAux n)
                (fun z => (z : ℝ) ^ 2) (fun z => (z : ℝ) ^ 4)
                1 0 (2 * ((13689 : ℝ) / 4096)) using 1
              all_goals ring_nf
          _ = (2 * ((n + 1 : ℕ) : ℝ)) * ((13689 : ℝ) / 4096) +
                (117 : ℝ) / 64 := by
              rw [ih.1]
              push_cast
              ring
      · calc
          finiteRealExpectation (entryNoiseIntExpAux (n + 1))
              (fun z => (z : ℝ) ^ 4) =
              finiteRealExpectation (do
                  let rest ← entryNoiseIntExpAux n
                  let step ← d3DifferenceBlock
                  return rest + step)
                (fun z => (z : ℝ) ^ 4) :=
            finiteRealExpectation_congr (evalDist_entryNoiseIntExpAux_succ n) _
          _ = finiteRealExpectation (entryNoiseIntExpAux n) (fun rest =>
                finiteRealExpectation d3DifferenceBlock
                  (fun step => ((rest + step : ℤ) : ℝ) ^ 4)) := by
              simp_rw [finiteRealExpectation_bind, finiteRealExpectation_pure]
          _ = finiteRealExpectation (entryNoiseIntExpAux n) (fun rest =>
                (rest : ℝ) ^ 4 +
                  12 * ((13689 : ℝ) / 4096) * (rest : ℝ) ^ 2 +
                  2 * ((1610361 : ℝ) / 16384) +
                  6 * (((13689 : ℝ) / 4096) ^ 2)) := by
              apply congrArg (finiteRealExpectation (entryNoiseIntExpAux n))
              funext rest
              simpa only [Int.cast_add] using
                finiteRealExpectation_block_shift_fourth (rest : ℝ)
          _ = (12 * ((13689 : ℝ) / 4096)) *
                  finiteRealExpectation (entryNoiseIntExpAux n)
                    (fun z => (z : ℝ) ^ 2) +
                1 * finiteRealExpectation (entryNoiseIntExpAux n)
                    (fun z => (z : ℝ) ^ 4) +
                (2 * ((1610361 : ℝ) / 16384) +
                  6 * (((13689 : ℝ) / 4096) ^ 2)) := by
              convert finiteRealExpectation_linear_two (entryNoiseIntExpAux n)
                (fun z => (z : ℝ) ^ 2) (fun z => (z : ℝ) ^ 4)
                (12 * ((13689 : ℝ) / 4096)) 1
                (2 * ((1610361 : ℝ) / 16384) +
                  6 * (((13689 : ℝ) / 4096) ^ 2)) using 1
              all_goals ring_nf
          _ = (2 * ((n + 1 : ℕ) : ℝ)) * ((1610361 : ℝ) / 16384) +
                3 * (2 * ((n + 1 : ℕ) : ℝ)) *
                  (2 * ((n + 1 : ℕ) : ℝ) - 1) *
                    (((13689 : ℝ) / 4096) ^ 2) +
                6 * (2 * ((n + 1 : ℕ) : ℝ)) *
                  ((13689 : ℝ) / 4096) * ((117 : ℝ) / 64) +
                (1269 : ℝ) / 128 := by
              rw [ih.1, ih.2]
              push_cast
              ring

/-- The actual first-exchange entry noise has the exact fourth moment used by the tail bound. -/
theorem expectedValue_firstExchangeEntryNoiseIntExp_fourth :
    OracleComp.EvalDist.expectedValue firstExchangeEntryNoiseIntExp
        (fun z : ℤ => (z.natAbs : ℝ≥0∞) ^ 4) =
      ENNReal.ofReal ((39818394483939 : ℝ) / 524288) := by
  have hAux :
      entryNoiseIntExpAux recommendedParams.n = firstExchangeEntryNoiseIntExp := rfl
  have hMoment := (finiteRealExpectation_entryNoiseIntExpAux_moments
    recommendedParams.n).2
  have hMoment' :
      finiteRealExpectation firstExchangeEntryNoiseIntExp
          (fun z => (z : ℝ) ^ 4) =
        (39818394483939 : ℝ) / 524288 := by
    rw [← hAux]
    rw [hMoment]
    norm_num [recommendedParams]
  have hFunctional (z : ℤ) :
      (z.natAbs : ℝ≥0∞) ^ 4 = ENNReal.ofReal ((z : ℝ) ^ 4) := by
    rw [← ENNReal.ofReal_natCast z.natAbs]
    rw [← ENNReal.ofReal_pow (Nat.cast_nonneg z.natAbs)]
    apply congrArg ENNReal.ofReal
    rw [Nat.cast_natAbs, Int.cast_abs]
    simpa using Even.pow_abs ⟨2, rfl⟩ (z : ℝ)
  simp_rw [hFunctional]
  rw [finiteRealExpectation_ofReal firstExchangeEntryNoiseIntExp
    (fun z => (z : ℝ) ^ 4) (by
      intro z
      simpa using Even.pow_nonneg ⟨2, rfl⟩ (z : ℝ))]
  rw [hMoment']

end lweCKA
