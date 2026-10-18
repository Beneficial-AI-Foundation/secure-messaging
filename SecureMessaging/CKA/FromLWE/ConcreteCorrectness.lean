/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.EntryNoiseMoments
import SecureMessaging.CKA.FromLWE.NoiseCorrectness
import VCVio.EvalDist.Expectation
import VCVio.EvalDist.Monad.Basic
import VCVio.EvalDist.Monad.Map
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# Concrete correctness of the recommended CKA-from-LWE parameters

This file combines the exact entry-noise fourth moment with Markov's inequality and a 64-entry
union bound. The resulting delta is a conservative bound; it is neither a zero-failure claim nor
the paper's sharper numerical estimate. The game bound is below one exactly for natural exchange
bounds `T ≤ 14`; for `T ≥ 15`, its displayed minimum is one.
-/

open OracleComp ENNReal
open scoped BigOperators

namespace lweCKA

/-- The conservative first-exchange failure bound at the recommended parameters. -/
noncomputable def recommendedFailureBound : ℝ≥0∞ :=
  (39818394483939 : ℝ≥0∞) / 562949953421312

/-- The conservative concrete failure bound is nontrivial. -/
theorem recommendedFailureBound_lt_one :
    recommendedFailureBound < 1 := by
  unfold recommendedFailureBound
  rw [ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  norm_num

/-- Circular distance from an integer residue to zero is at most its integer magnitude. -/
theorem modularDistance_intCast_zero_le_natAbs
    (p : Params) (z : ℤ) :
    modularDistance p (z : Scalar p) 0 ≤ z.natAbs := by
  cases z with
  | ofNat n =>
      unfold modularDistance
      simp only [Int.ofNat_eq_natCast, Int.cast_natCast, Int.natAbs_natCast, sub_zero]
      exact le_trans (min_le_left _ _) (by
        rw [ZMod.val_natCast]
        exact Nat.mod_le _ _)
  | negSucc n =>
      unfold modularDistance
      simp only [Int.cast_negSucc, Int.natAbs_negSucc, sub_zero, zero_sub, neg_neg]
      exact le_trans (min_le_right _ _) (by
        rw [ZMod.val_natCast]
        exact Nat.mod_le _ _)

private theorem probEvent_firstExchangeEntryNoiseIntExp_natAbs_ge_radius_le :
    Pr[fun z : ℤ => 512 ≤ z.natAbs |
      firstExchangeEntryNoiseIntExp] ≤
        recommendedFailureBound / 64 := by
  refine (probEvent_le_tsum_probOutput_mul_cost firstExchangeEntryNoiseIntExp
    (fun z : ℤ => 512 ≤ z.natAbs)
    (fun z : ℤ => (z.natAbs : ℝ≥0∞) ^ 4 / (512 : ℝ≥0∞) ^ 4) ?_).trans ?_
  · intro z hz
    have hz' : (512 : ℝ≥0∞) ≤ (z.natAbs : ℝ≥0∞) := by
      exact_mod_cast hz
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num
    have hp := pow_le_pow_left' hz' 4
    norm_num at hp
    exact hp
  · simp_rw [div_eq_mul_inv, ← mul_assoc]
    rw [ENNReal.tsum_mul_right]
    change OracleComp.EvalDist.expectedValue firstExchangeEntryNoiseIntExp
        (fun z : ℤ => (z.natAbs : ℝ≥0∞) ^ 4) *
          ((512 : ℝ≥0∞) ^ 4)⁻¹ ≤ recommendedFailureBound / 64
    rw [expectedValue_firstExchangeEntryNoiseIntExp_fourth]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 524288)]
    unfold recommendedFailureBound
    norm_num
    calc
      (39818394483939 : ℝ≥0∞) / 524288 / 68719476736 =
          39818394483939 / (524288 * 68719476736) := by
        simp only [div_eq_mul_inv]
        rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        ac_rfl
      _ = 39818394483939 / (562949953421312 * 64) := by norm_num
      _ = 39818394483939 / 562949953421312 / 64 := by
        simp only [div_eq_mul_inv]
        rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        ac_rfl
      _ ≤ _ := le_rfl

/-- Every actual first-exchange noise entry exceeds the radius with probability at most delta/64. -/
theorem probEvent_firstExchangeNoise_entry_ge_radius_le
    (i j : Fin recommendedParams.nbar) :
    Pr[fun delta : SharedMatrix recommendedParams =>
      512 ≤ modularDistance recommendedParams (delta i j) 0 |
      firstExchangeNoiseExp recommendedParams d3Sampler] ≤
        recommendedFailureBound / 64 := by
  let q := fun x : Scalar recommendedParams =>
    512 ≤ modularDistance recommendedParams x 0
  calc
    Pr[fun delta : SharedMatrix recommendedParams =>
        512 ≤ modularDistance recommendedParams (delta i j) 0 |
        firstExchangeNoiseExp recommendedParams d3Sampler] =
        Pr[q | (fun delta : SharedMatrix recommendedParams => delta i j) <$>
          firstExchangeNoiseExp recommendedParams d3Sampler] := by
          rw [probEvent_map]
          rfl
    _ = Pr[q | (fun z : ℤ => (z : Scalar recommendedParams)) <$>
          firstExchangeEntryNoiseIntExp] := by
          simp only [probEvent_def]
          rw [evalDist_firstExchangeNoise_entry_eq_cast i j]
    _ = Pr[fun z : ℤ =>
          512 ≤ modularDistance recommendedParams (z : Scalar recommendedParams) 0 |
          firstExchangeEntryNoiseIntExp] := by
          rw [probEvent_map]
          rfl
    _ ≤ Pr[fun z : ℤ => 512 ≤ z.natAbs |
          firstExchangeEntryNoiseIntExp] := by
          exact probEvent_mono'' fun z hz =>
            le_trans hz (modularDistance_intCast_zero_le_natAbs recommendedParams z)
    _ ≤ recommendedFailureBound / 64 :=
      probEvent_firstExchangeEntryNoiseIntExp_natAbs_ge_radius_le

/-- The first exchange fails with probability at most the conservative concrete delta. -/
theorem firstExchangeFailureProb_recommended_le :
    firstExchangeFailureProb recommendedParams d3Sampler ≤
      recommendedFailureBound := by
  calc
    firstExchangeFailureProb recommendedParams d3Sampler ≤
        Pr[fun delta : SharedMatrix recommendedParams =>
          ∃ i j : Fin recommendedParams.nbar,
            512 ≤ modularDistance recommendedParams (delta i j) 0 |
          firstExchangeNoiseExp recommendedParams d3Sampler] := by
          simpa only [recommendedParams_radius] using
            firstExchangeFailureProb_le_noiseTail recommendedParams
              recommendedParams_wellFormed d3Sampler
    _ ≤ Pr[fun delta : SharedMatrix recommendedParams =>
          ∃ ij ∈ (Finset.univ : Finset
            (Fin recommendedParams.nbar × Fin recommendedParams.nbar)),
            512 ≤ modularDistance recommendedParams (delta ij.1 ij.2) 0 |
          firstExchangeNoiseExp recommendedParams d3Sampler] := by
          exact probEvent_mono'' fun delta h => by
            obtain ⟨i, j, hij⟩ := h
            exact ⟨(i, j), Finset.mem_univ _, hij⟩
    _ ≤ ∑ ij ∈ (Finset.univ : Finset
          (Fin recommendedParams.nbar × Fin recommendedParams.nbar)),
          Pr[fun delta : SharedMatrix recommendedParams =>
            512 ≤ modularDistance recommendedParams (delta ij.1 ij.2) 0 |
            firstExchangeNoiseExp recommendedParams d3Sampler] :=
          probEvent_exists_finset_le_sum _ _ _
    _ ≤ ∑ _ij ∈ (Finset.univ : Finset
          (Fin recommendedParams.nbar × Fin recommendedParams.nbar)),
          recommendedFailureBound / 64 := by
          exact Finset.sum_le_sum fun ij _ =>
            probEvent_firstExchangeNoise_entry_ge_radius_le ij.1 ij.2
    _ = recommendedFailureBound := by
          have hcard : (Finset.univ : Finset
              (Fin recommendedParams.nbar × Fin recommendedParams.nbar)).card = 64 := by
            norm_num [recommendedParams, Fintype.card_prod]
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
          exact ENNReal.mul_div_cancel (a := (64 : ℝ≥0∞))
            (b := recommendedFailureBound) (by norm_num) (by norm_num)

/-- With at most `T` completed exchanges, correctness failure is at most `min 1 (T * delta)`.
This bound is below one exactly for natural `T ≤ 14`; it is one for `T ≥ 15`. -/
theorem correctness_failure_recommended_le
    (adv : CKAScheme.CKACorrectnessAdversary
      (Message recommendedParams) (Key recommendedParams))
    (T : ℕ)
    (hT : HasExchangeBound recommendedParams
      recommendedParams_wellFormed d3Sampler adv T) :
    Pr[= false |
      CKAScheme.correctnessExp
        (scheme recommendedParams recommendedParams_wellFormed d3Sampler)
        adv] ≤
      min 1 ((T : ℝ≥0∞) * recommendedFailureBound) := by
  refine le_trans (correctness_failure_le recommendedParams
    recommendedParams_wellFormed d3Sampler adv T hT) ?_
  exact min_le_min le_rfl (mul_le_mul' le_rfl firstExchangeFailureProb_recommended_le)

end lweCKA
