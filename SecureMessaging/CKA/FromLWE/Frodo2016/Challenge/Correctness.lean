/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Challenge.PairBound
import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Challenge.Bounds
import Mathlib.Data.Finset.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Concrete correctness of the historical Frodo challenge parameters

This file aggregates the sixty-four entry events.  The upper estimate is the finite union bound;
the lower estimate is the additive two-term Bonferroni inequality.  The final theorem compares the
certified lower endpoint with the literal real power printed in the paper.
-/

open OracleComp OracleComp.EvalDist
open scoped BigOperators ENNReal

namespace lweCKA

private noncomputable def indicator (p : Prop) : ℝ≥0∞ :=
  @ite ℝ≥0∞ p (Classical.propDecidable p) 1 0

private theorem expectedValue_indicator
    {α : Type} (mx : ProbComp α) (p : α → Prop) :
    expectedValue mx (fun x => indicator (p x)) = Pr[p | mx] := by
  classical
  rw [expectedValue_def, probEvent_eq_tsum_ite]
  apply tsum_congr
  intro x
  by_cases hx : p x <;> simp [indicator, hx]

private theorem nat_le_indicator_add_choose_two (n : ℕ) :
    n ≤ (if n = 0 then 0 else 1) + n.choose 2 := by
  cases n with
  | zero => simp
  | succ n =>
      rw [if_neg (Nat.succ_ne_zero n)]
      rw [show (n + 1).choose 2 = n + n.choose 2 by
        simp only [Nat.choose_succ_succ, Nat.choose_one_right]]
      omega

private theorem sum_indicators_le_exists_add_pairs
    {ι α : Type} [LinearOrder ι] (s : Finset ι) (E : ι → α → Prop) (x : α) :
    (∑ i ∈ s, indicator (E i x)) ≤
      indicator (∃ i ∈ s, E i x) +
        ∑ ij ∈ (s ×ˢ s).filter (fun ij => ij.1 < ij.2),
          indicator (E ij.1 x ∧ E ij.2 x) := by
  classical
  let u := s.filter fun i => E i x
  have hleft :
      (∑ i ∈ s, indicator (E i x)) = (u.card : ℝ≥0∞) := by
    simpa only [u, indicator] using
      (Finset.sum_boole (R := ℝ≥0∞) (fun i => E i x) s)
  have hexists : (∃ i ∈ s, E i x) ↔ u.Nonempty := by
    constructor
    · rintro ⟨i, hi, hEi⟩
      exact ⟨i, by simp [u, hi, hEi]⟩
    · rintro ⟨i, hi⟩
      have hi' : i ∈ s ∧ E i x := by simpa [u] using hi
      exact ⟨i, hi'.1, hi'.2⟩
  have hpairs :
      (∑ ij ∈ (s ×ˢ s).filter (fun ij => ij.1 < ij.2),
          indicator (E ij.1 x ∧ E ij.2 x)) =
        (u.card.choose 2 : ℝ≥0∞) := by
    let pairs := (s ×ˢ s).filter (fun ij => ij.1 < ij.2)
    have hsum :
        (∑ ij ∈ pairs, indicator (E ij.1 x ∧ E ij.2 x)) =
          ((pairs.filter (fun ij => E ij.1 x ∧ E ij.2 x)).card : ℝ≥0∞) := by
      calc
        (∑ ij ∈ pairs, indicator (E ij.1 x ∧ E ij.2 x)) =
            ∑ ij ∈ pairs,
              if E ij.1 x ∧ E ij.2 x then (1 : ℝ≥0∞) else 0 := by
          apply Finset.sum_congr rfl
          intro ij _
          by_cases hij : E ij.1 x ∧ E ij.2 x <;> simp [indicator, hij]
        _ = ((pairs.filter (fun ij => E ij.1 x ∧ E ij.2 x)).card : ℝ≥0∞) :=
          Finset.sum_boole _ _
    have hfilter : pairs.filter (fun ij => E ij.1 x ∧ E ij.2 x) =
        (u ×ˢ u).filter (fun ij => ij.1 < ij.2) := by
      ext ij
      simp [pairs, u, and_assoc, and_left_comm, and_comm]
    rw [show (∑ ij ∈ (s ×ˢ s).filter (fun ij => ij.1 < ij.2),
        indicator (E ij.1 x ∧ E ij.2 x)) =
          (∑ ij ∈ pairs, indicator (E ij.1 x ∧ E ij.2 x)) by rfl,
      hsum, hfilter]
    exact_mod_cast (Finset.card_product_filter_lt (s := u))
  rw [hleft, hpairs]
  by_cases hu : u.card = 0
  · have hempty : ¬u.Nonempty := Finset.not_nonempty_iff_eq_empty.mpr
      (Finset.card_eq_zero.mp hu)
    simp [indicator, hu, hexists.not.mpr hempty]
  · have hnonempty : u.Nonempty := Finset.card_ne_zero.mp hu
    rw [show indicator (∃ i ∈ s, E i x) = 1 by
      simp [indicator, hexists.mpr hnonempty]]
    have hn := nat_le_indicator_add_choose_two u.card
    rw [if_neg hu] at hn
    exact_mod_cast hn

private theorem probEvent_sum_le_union_add_pairs
    {ι α : Type} [LinearOrder ι] (s : Finset ι) (mx : ProbComp α)
    (E : ι → α → Prop) :
    (∑ i ∈ s, Pr[E i | mx]) ≤
      Pr[fun x => ∃ i ∈ s, E i x | mx] +
        ∑ ij ∈ (s ×ˢ s).filter (fun ij => ij.1 < ij.2),
          Pr[fun x => E ij.1 x ∧ E ij.2 x | mx] := by
  classical
  calc
    (∑ i ∈ s, Pr[E i | mx]) =
        expectedValue mx (fun x => ∑ i ∈ s, indicator (E i x)) := by
      rw [expectedValue_finsetSum]
      simp_rw [expectedValue_indicator]
    _ ≤ expectedValue mx
          (fun x =>
            indicator (∃ i ∈ s, E i x) +
              ∑ ij ∈ (s ×ˢ s).filter (fun ij => ij.1 < ij.2),
                indicator (E ij.1 x ∧ E ij.2 x)) :=
      expectedValue_mono mx (sum_indicators_le_exists_add_pairs s E)
    _ = Pr[fun x => ∃ i ∈ s, E i x | mx] +
          ∑ ij ∈ (s ×ˢ s).filter (fun ij => ij.1 < ij.2),
            Pr[fun x => E ij.1 x ∧ E ij.2 x | mx] := by
      rw [expectedValue_add, expectedValue_indicator, expectedValue_finsetSum]
      simp_rw [expectedValue_indicator]

private def challengeCoordEquiv :
    Fin challengeParams.nbar × Fin challengeParams.nbar ≃ Fin 64 := by
  simpa [challengeParams] using (finProdFinEquiv : Fin 8 × Fin 8 ≃ Fin 64)

private def challengeCoord (i : Fin 64) :
    Fin challengeParams.nbar × Fin challengeParams.nbar :=
  challengeCoordEquiv.symm i

private lemma challengeCoord_injective : Function.Injective challengeCoord :=
  challengeCoordEquiv.symm.injective

private theorem challenge_entry_union_reindex :
    Pr[fun t =>
      ∃ c : Fin challengeParams.nbar × Fin challengeParams.nbar,
        challengeEntryMismatch c t | challengeCoinsExp] =
      Pr[fun t => ∃ i : Fin 64, challengeEntryMismatch (challengeCoord i) t |
        challengeCoinsExp] := by
  apply le_antisymm
  · apply probEvent_mono''
    intro t ht
    obtain ⟨c, hc⟩ := ht
    exact ⟨challengeCoordEquiv c, by simpa [challengeCoord] using hc⟩
  · apply probEvent_mono''
    rintro t ⟨i, hi⟩
    exact ⟨challengeCoord i, hi⟩

private theorem challenge_pair_sum_le :
    (∑ ij ∈ ((Finset.univ : Finset (Fin 64)) ×ˢ Finset.univ).filter
        (fun ij => ij.1 < ij.2),
      Pr[fun t =>
        challengeEntryMismatch (challengeCoord ij.1) t ∧
          challengeEntryMismatch (challengeCoord ij.2) t |
        challengeCoinsExp]) ≤
      (2016 : ℝ≥0∞) / 2 ^ 70 := by
  calc
    (∑ ij ∈ ((Finset.univ : Finset (Fin 64)) ×ˢ Finset.univ).filter
        (fun ij => ij.1 < ij.2),
      Pr[fun t =>
        challengeEntryMismatch (challengeCoord ij.1) t ∧
          challengeEntryMismatch (challengeCoord ij.2) t |
        challengeCoinsExp]) =
        ∑ ij ∈ ((Finset.univ : Finset (Fin 64)) ×ˢ Finset.univ),
          if ij.1 < ij.2 then
            Pr[fun t =>
              challengeEntryMismatch (challengeCoord ij.1) t ∧
                challengeEntryMismatch (challengeCoord ij.2) t |
              challengeCoinsExp]
          else 0 := by
      rw [Finset.sum_filter]
    _ ≤ ∑ ij ∈ ((Finset.univ : Finset (Fin 64)) ×ˢ Finset.univ),
          if ij.1 < ij.2 then ((1 : ℝ≥0∞) / 2 ^ 70) else 0 := by
      apply Finset.sum_le_sum
      intro ij _
      by_cases hlt : ij.1 < ij.2
      · simp only [if_pos hlt]
        have hne : challengeCoord ij.1 ≠ challengeCoord ij.2 := by
          intro h
          exact hlt.ne (challengeCoord_injective h)
        exact probEvent_challengeEntryMismatch_pair_le _ _ hne
      · simp only [if_neg hlt]
        exact le_rfl
    _ = ∑ _ij ∈ ((Finset.univ : Finset (Fin 64)) ×ˢ Finset.univ).filter
          (fun ij => ij.1 < ij.2),
          ((1 : ℝ≥0∞) / 2 ^ 70) := by
      rw [Finset.sum_filter]
    _ = (2016 : ℝ≥0∞) / 2 ^ 70 := by
      rw [Finset.sum_const, nsmul_eq_mul,
        Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin 64))),
        Nat.choose_two_right]
      norm_num
      simp only [div_eq_mul_inv]

private theorem challenge_marginal_sum_bounds :
    let m := expectedValue challengeEntryNoiseIntExp challengeFailureRamp
    let e := (1 : ℝ≥0∞) / 2 ^ 345
    (∑ i : Fin 64,
        Pr[challengeEntryMismatch (challengeCoord i) | challengeCoinsExp]) ≤
        64 * m + e ∧
      64 * m ≤
        (∑ i : Fin 64,
          Pr[challengeEntryMismatch (challengeCoord i) | challengeCoinsExp]) + e := by
  dsimp only
  have hpow : (2 : ℝ≥0∞) ^ 351 = 64 * 2 ^ 345 := by
    rw [show 351 = 6 + 345 by norm_num, pow_add]
    norm_num
  have hscale : (64 : ℝ≥0∞) * (1 / 2 ^ 351) = 1 / 2 ^ 345 := by
    rw [div_eq_mul_inv, one_mul, ← div_eq_mul_inv, hpow]
    simpa using ENNReal.mul_div_mul_left (1 : ℝ≥0∞) (2 ^ 345)
      (by norm_num : (64 : ℝ≥0∞) ≠ 0) (by norm_num : (64 : ℝ≥0∞) ≠ ∞)
  constructor
  · calc
      (∑ i : Fin 64,
          Pr[challengeEntryMismatch (challengeCoord i) | challengeCoinsExp]) ≤
          ∑ _i : Fin 64,
            (expectedValue challengeEntryNoiseIntExp challengeFailureRamp +
              (1 : ℝ≥0∞) / 2 ^ 351) := by
        apply Finset.sum_le_sum
        intro i _
        exact (probEvent_challengeEntryMismatch_ramp_bounds (challengeCoord i)).1
      _ = 64 * expectedValue challengeEntryNoiseIntExp challengeFailureRamp +
          (1 : ℝ≥0∞) / 2 ^ 345 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_ofNat]
        change (64 : ℝ≥0∞) *
            (expectedValue challengeEntryNoiseIntExp challengeFailureRamp +
              1 / 2 ^ 351) = _
        rw [mul_add, hscale]
  · calc
      64 * expectedValue challengeEntryNoiseIntExp challengeFailureRamp =
          ∑ _i : Fin 64,
            expectedValue challengeEntryNoiseIntExp challengeFailureRamp := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_ofNat]
      _ ≤
          ∑ _i : Fin 64,
            (Pr[challengeEntryMismatch (challengeCoord _i) | challengeCoinsExp] +
              (1 : ℝ≥0∞) / 2 ^ 351) := by
        apply Finset.sum_le_sum
        intro i _
        exact (probEvent_challengeEntryMismatch_ramp_bounds (challengeCoord i)).2
      _ = (∑ i : Fin 64,
          Pr[challengeEntryMismatch (challengeCoord i) | challengeCoinsExp]) +
          (1 : ℝ≥0∞) / 2 ^ 345 := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
        change (∑ i : Fin 64,
            Pr[challengeEntryMismatch (challengeCoord i) | challengeCoinsExp]) +
              (64 : ℝ≥0∞) * (1 / 2 ^ 351) = _
        rw [hscale]

private theorem challenge_probability_vs_ramp :
    let P := firstExchangeFailureProb challengeParams d1Sampler
    let m := expectedValue challengeEntryNoiseIntExp challengeFailureRamp
    let e := (1 : ℝ≥0∞) / 2 ^ 345
    let b := (2016 : ℝ≥0∞) / 2 ^ 70
    P ≤ 64 * m + e ∧ 64 * m ≤ P + b + e := by
  dsimp only
  have hreindex := challenge_entry_union_reindex
  have hmarg := challenge_marginal_sum_bounds
  constructor
  · rw [firstExchangeFailureProb_challenge_eq_entry_union, hreindex]
    have hunion := probEvent_exists_finset_le_sum Finset.univ challengeCoinsExp
      (fun i t => challengeEntryMismatch (challengeCoord i) t)
    have hunion' :
        Pr[fun t => ∃ i : Fin 64, challengeEntryMismatch (challengeCoord i) t |
          challengeCoinsExp] ≤
          ∑ i : Fin 64,
            Pr[challengeEntryMismatch (challengeCoord i) | challengeCoinsExp] := by
      simpa using hunion
    exact hunion'.trans hmarg.1
  · have hbonf := probEvent_sum_le_union_add_pairs
      (Finset.univ : Finset (Fin 64)) challengeCoinsExp
      (fun i t => challengeEntryMismatch (challengeCoord i) t)
    have hpair := challenge_pair_sum_le
    simp only [Finset.mem_univ, true_and] at hbonf
    rw [← hreindex, ← firstExchangeFailureProb_challenge_eq_entry_union] at hbonf
    have hpair' :
        firstExchangeFailureProb challengeParams d1Sampler +
            (∑ ij ∈ ((Finset.univ : Finset (Fin 64)) ×ˢ Finset.univ).filter
              (fun ij => ij.1 < ij.2),
              Pr[fun t =>
                challengeEntryMismatch (challengeCoord ij.1) t ∧
                  challengeEntryMismatch (challengeCoord ij.2) t |
                challengeCoinsExp]) ≤
          firstExchangeFailureProb challengeParams d1Sampler +
            (2016 : ℝ≥0∞) / 2 ^ 70 :=
      add_le_add le_rfl hpair
    have hsump :
        (∑ i : Fin 64,
          Pr[challengeEntryMismatch (challengeCoord i) | challengeCoinsExp]) ≤
          firstExchangeFailureProb challengeParams d1Sampler +
            (2016 : ℝ≥0∞) / 2 ^ 70 :=
      hbonf.trans hpair'
    calc
      64 * expectedValue challengeEntryNoiseIntExp challengeFailureRamp ≤
          (∑ i : Fin 64,
            Pr[challengeEntryMismatch (challengeCoord i) | challengeCoinsExp]) +
              (1 : ℝ≥0∞) / 2 ^ 345 := hmarg.2
      _ ≤ (firstExchangeFailureProb challengeParams d1Sampler +
            (2016 : ℝ≥0∞) / 2 ^ 70) + 1 / 2 ^ 345 :=
        add_le_add_left hsump _

/-- Unconditional first-exchange failure bounds for the Challenge parameters and exact D1 sampler
with a uniformly sampled public matrix. This does not model an arbitrary seeded matrix generator.
The interval includes both exceptional-secret-vector and dependent-coordinate allowances. -/
theorem firstExchangeFailureProb_challenge_bounds :
    (316048081581 : ℝ≥0∞) / 2 ^ 80 ≤
        firstExchangeFailureProb challengeParams d1Sampler ∧
      firstExchangeFailureProb challengeParams d1Sampler ≤
        (316050145969 : ℝ≥0∞) / 2 ^ 80 := by
  let P := firstExchangeFailureProb challengeParams d1Sampler
  let m := expectedValue challengeEntryNoiseIntExp challengeFailureRamp
  let e := (1 : ℝ≥0∞) / 2 ^ 345
  let b := (2016 : ℝ≥0∞) / 2 ^ 70
  let L := (316048081581 : ℝ≥0∞) / 2 ^ 80
  let U := (316050145969 : ℝ≥0∞) / 2 ^ 80
  let N := (182190504909736707587867345424 : ℝ≥0∞)
  let d := (4538522943514 : ℝ≥0∞)
  have hprob : P ≤ 64 * m + e ∧ 64 * m ≤ P + b + e :=
    challenge_probability_vs_ramp
  have hramp : N / 2 ^ 139 ≤ 64 * m ∧
      64 * m ≤ N / 2 ^ 139 + 64 * d / 2 ^ 128 := challengeEntryRamp_bounds
  have hl_arith : L + b + e ≤ N / 2 ^ 139 := by
    dsimp [L, b, e, N]
    have hpow80 : (2 : ℝ≥0∞) ^ 80 ≤ 2 ^ 345 :=
      pow_le_pow_right₀ (by norm_num) (by norm_num)
    have he80 : (1 : ℝ≥0∞) / 2 ^ 345 ≤ 1 / 2 ^ 80 :=
      ENNReal.div_le_div_left hpow80 1
    calc
      (316048081581 : ℝ≥0∞) / 2 ^ 80 + 2016 / 2 ^ 70 + 1 / 2 ^ 345 ≤
          316048081581 / 2 ^ 80 + 2016 / 2 ^ 70 + 1 / 2 ^ 80 :=
        add_le_add_right he80 _
      _ ≤ 182190504909736707587867345424 / 2 ^ 139 := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        rw [ENNReal.toReal_add (by finiteness) (by finiteness),
          ENNReal.toReal_add (by finiteness) (by finiteness)]
        simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
          ENNReal.toReal_one]
        norm_num
  have hu_arith : N / 2 ^ 139 + 64 * d / 2 ^ 128 + e ≤ U := by
    dsimp [N, d, e, U]
    have hpow128 : (2 : ℝ≥0∞) ^ 128 ≤ 2 ^ 345 :=
      pow_le_pow_right₀ (by norm_num) (by norm_num)
    have he128 : (1 : ℝ≥0∞) / 2 ^ 345 ≤ 1 / 2 ^ 128 :=
      ENNReal.div_le_div_left hpow128 1
    calc
      (182190504909736707587867345424 : ℝ≥0∞) / 2 ^ 139 +
            64 * 4538522943514 / 2 ^ 128 + 1 / 2 ^ 345 ≤
          182190504909736707587867345424 / 2 ^ 139 +
            64 * 4538522943514 / 2 ^ 128 + 1 / 2 ^ 128 :=
        add_le_add_right he128 _
      _ ≤ 316050145969 / 2 ^ 80 := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        rw [ENNReal.toReal_add (by finiteness) (by finiteness),
          ENNReal.toReal_add (by finiteness) (by finiteness)]
        simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_mul,
          ENNReal.toReal_ofNat, ENNReal.toReal_one]
        norm_num
  constructor
  · have h : L + (b + e) ≤ P + (b + e) := by
      calc
        L + (b + e) = L + b + e := by ac_rfl
        _ ≤ N / 2 ^ 139 := hl_arith
        _ ≤ 64 * m := hramp.1
        _ ≤ P + b + e := hprob.2
        _ = P + (b + e) := by ac_rfl
    exact ENNReal.le_of_add_le_add_right (by finiteness) h
  · calc
      P ≤ 64 * m + e := hprob.1
      _ ≤ (N / 2 ^ 139 + 64 * d / 2 ^ 128) + e :=
        add_le_add hramp.2 le_rfl
      _ ≤ U := hu_arith

private theorem challenge_lower_fifth_power :
    (2 : ℝ) ^ (-209 : ℤ) < ((316048081581 : ℝ) / 2 ^ 80) ^ 5 := by
  norm_num [zpow_neg]

/-- The certified lower endpoint exceeds the literal real number `2^(-41.8)`.
Together with `firstExchangeFailureProb_challenge_bounds`, this compares the uniform-public-matrix
first-exchange D1 model to that literal value. It does not refute the paper's rounded table entry.
-/
theorem challenge_lower_strictly_above_paper_literal :
    Real.rpow (2 : ℝ) (-(209 / 5 : ℝ)) <
      (316048081581 : ℝ) / 2 ^ 80 := by
  let x := Real.rpow (2 : ℝ) (-(209 / 5 : ℝ))
  let y := (316048081581 : ℝ) / 2 ^ 80
  have hx : 0 ≤ x := Real.rpow_nonneg (by positivity) _
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hxpow : x ^ 5 = (2 : ℝ) ^ (-209 : ℤ) := by
    dsimp [x]
    rw [← Real.rpow_mul_natCast (x := (2 : ℝ)) (by positivity)]
    convert Real.rpow_intCast (2 : ℝ) (-209) using 1; norm_num
  refine (Real.rpow_lt_rpow_iff hx hy (show (0 : ℝ) < 5 by norm_num)).mp ?_
  calc
    Real.rpow x (5 : ℝ) = x ^ (5 : ℕ) := Real.rpow_natCast x 5
    _ = (2 : ℝ) ^ (-209 : ℤ) := hxpow
    _ < y ^ (5 : ℕ) := by
      simpa only [y] using challenge_lower_fifth_power
    _ = Real.rpow y (5 : ℝ) := (Real.rpow_natCast y 5).symm

/-- At most `T` completed exchanges fail with probability at most the certified Challenge
upper endpoint times `T`, capped at one, for exact D1 sampling and a uniform public matrix. -/
theorem correctness_failure_challenge_le
    (adv : CKAScheme.CKACorrectnessAdversary
      (Message challengeParams) (Key challengeParams))
    (T : ℕ)
    (hT : HasExchangeBound challengeParams challengeParams_wellFormed d1Sampler adv T) :
    Pr[= false | CKAScheme.correctnessExp
      (scheme challengeParams challengeParams_wellFormed d1Sampler) adv] ≤
      min 1 ((T : ℝ≥0∞) * ((316050145969 : ℝ≥0∞) / 2 ^ 80)) := by
  refine le_trans (correctness_failure_le challengeParams
    challengeParams_wellFormed d1Sampler adv T hT) ?_
  exact min_le_min le_rfl
    (mul_le_mul' le_rfl firstExchangeFailureProb_challenge_bounds.2)

end lweCKA
