/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Challenge.PairBound.Projection

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

open PairBoundInternal

namespace PairBoundInternal

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

end PairBoundInternal

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
