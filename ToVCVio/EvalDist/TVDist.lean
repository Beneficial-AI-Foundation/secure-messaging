/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import VCVio.EvalDist.TVDist
import VCVio.EvalDist.Bool

/-!
# Total Variation Distance — Extra Lemmas

Generic total-variation-distance (`tvDist`) facts that hold for any monad with an
evaluation distribution.

* `tvDist_bind_const_right` drops a never-failing, discarded trailing bind from the
  right-hand side of a total-variation distance.
* `tvDist_bind_left_event_le_const` (with its underlying tsum form
  `tsum_probOutput_toReal_mul_tvDist_le_const_mul_probEvent`) is VCVio's `tvDist_bind_left_event_le`
  with a tunable per-branch bound `c` in place of the trivial bound `1`.
* `tvDist_eq_abs_probOutput_true_sub` computes the exact total-variation distance between two
  never-failing `Bool`-valued computations, sharpening `abs_probOutput_toReal_sub_le_tvDist` (which
  only gives one inequality direction, for possibly-failing computations) to an equality.
-/

namespace ToVCVio

universe u v

variable {α : Type u} {m : Type u → Type v} [Monad m]

/-- Total-variation distance is unaffected by a trailing bind whose result is discarded: if `mx`
never fails, `mx >>= fun _ => my` has exactly the same distribution as `my`. -/
lemma tvDist_bind_const_right [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [EvalDistCompatible m]
    {β : Type u} (mx' : m β) (mx : m α) [NeverFail mx] (my : m β) :
    tvDist mx' (mx >>= fun _ => my) = tvDist mx' my := by
  unfold tvDist
  rw [evalDist_ext (mx := mx >>= fun _ => my) (mx' := my) fun y => by simp]

omit [Monad m] in
/-- As VCVio's `tsum_probOutput_toReal_mul_tvDist_le_probEvent`, but with a tunable bound `c` on
the total-variation distance on the bad branch in place of the trivial bound `1`, giving the
tighter conclusion `c * Pr[bad]` whenever the two continuations are known to stay within `c` of
each other even when the bad event holds. -/
lemma tsum_probOutput_toReal_mul_tvDist_le_const_mul_probEvent [MonadLiftT m PMF]
    {β : Type u} (mx : m α) (f g : α → m β) (bad : α → Prop)
    (c : ℝ) (hc : 0 ≤ c)
    (h_eq : ∀ a, ¬ bad a → 𝒟[f a] = 𝒟[g a])
    (h_le : ∀ a, bad a → tvDist (f a) (g a) ≤ c) :
    (∑' a, Pr[= a | mx].toReal * tvDist (f a) (g a)) ≤ c * Pr[bad | mx].toReal := by
  classical
  have h_p_summable : Summable (fun a : α => Pr[= a | mx].toReal) :=
    ENNReal.summable_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top tsum_probOutput_le_one)
  calc (∑' a, Pr[= a | mx].toReal * tvDist (f a) (g a))
      ≤ ∑' a, if bad a then c * Pr[= a | mx].toReal else 0 := by
        refine Summable.tsum_le_tsum (fun a => ?_)
          (h_p_summable.of_nonneg_of_le
            (fun a => mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _))
            (fun a => mul_le_of_le_one_right ENNReal.toReal_nonneg (tvDist_le_one _ _)))
          ((h_p_summable.mul_left c).of_nonneg_of_le
            (fun a => by by_cases ha : bad a <;> simp [ha, mul_nonneg hc ENNReal.toReal_nonneg])
            (fun a => by by_cases ha : bad a <;> simp [ha, mul_nonneg hc ENNReal.toReal_nonneg]))
        by_cases ha : bad a
        · simpa [ha, mul_comm] using
            mul_le_mul_of_nonneg_left (h_le a ha) ENNReal.toReal_nonneg
        · simp [ha, (tvDist_eq_zero_iff (f a) (g a)).2 (h_eq a ha)]
    _ = c * Pr[bad | mx].toReal := by
        rw [show (∑' a, if bad a then c * Pr[= a | mx].toReal else 0) =
            c * ∑' a, if bad a then Pr[= a | mx].toReal else 0 from by
          rw [← tsum_mul_left]
          exact tsum_congr fun a => by by_cases ha : bad a <;> simp [ha]]
        congr 1
        rw [probEvent_eq_tsum_ite, ENNReal.tsum_toReal_eq fun a => by
          by_cases ha : bad a
          · simp [ha,
              ne_top_of_le_ne_top ENNReal.one_ne_top (probOutput_le_one (mx := mx) (x := a))]
          · simp [ha]]
        exact tsum_congr fun a => by by_cases ha : bad a <;> simp [ha]

/-- As VCVio's `tvDist_bind_left_event_le`, but with a tunable bound `c` on the total-variation
distance on the bad branch in place of the trivial bound `1`, giving the tighter conclusion
`c * Pr[bad]` whenever the two continuations are known to stay within `c` of each other even when
the bad event holds. -/
lemma tvDist_bind_left_event_le_const [LawfulMonad m] [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    {β : Type u} (mx : m α) (f g : α → m β) (bad : α → Prop) (c : ℝ) (hc : 0 ≤ c)
    (h_eq : ∀ a, ¬ bad a → 𝒟[f a] = 𝒟[g a])
    (h_le : ∀ a, bad a → tvDist (f a) (g a) ≤ c) :
    tvDist (mx >>= f) (mx >>= g) ≤ c * Pr[bad | mx].toReal :=
  le_trans (tvDist_bind_left_le mx f g)
    (tsum_probOutput_toReal_mul_tvDist_le_const_mul_probEvent mx f g bad c hc h_eq h_le)

/-- Two `Bool`-valued computations that never fail have total-variation distance exactly the gap
between their `true`-output probabilities. Unlike the general `Bool` bound
`abs_probOutput_toReal_sub_le_tvDist`, which only lower-bounds `tvDist` (since a computation may
also differ from another by shifting mass to/from failure), this is an equality once failure is
ruled out on both sides: the whole `Option Bool` mass then splits exactly between `some true` and
`some false`, so total-variation distance collapses to the single-coordinate gap. -/
lemma tvDist_eq_abs_probOutput_true_sub {m : Type → Type v} [Monad m]
    [MonadLiftT m SPMF]
    (p q : m Bool) [NeverFail p] [NeverFail q] :
    tvDist p q = |(Pr[= true | p]).toReal - (Pr[= true | q]).toReal| := by
  have hp_none : (𝒟[p]).toPMF none = 0 := NeverFail.probFailure_eq_zero
  have hq_none : (𝒟[q]).toPMF none = 0 := NeverFail.probFailure_eq_zero
  have hp_true : (𝒟[p]).toPMF (some true) = Pr[= true | p] := rfl
  have hq_true : (𝒟[q]).toPMF (some true) = Pr[= true | q] := rfl
  have hp_false : (𝒟[p]).toPMF (some false) = 1 - Pr[= true | p] := by
    rw [show (𝒟[p]).toPMF (some false) = Pr[= false | p] from rfl, probOutput_false_eq_sub,
      NeverFail.probFailure_eq_zero, tsub_zero]
  have hq_false : (𝒟[q]).toPMF (some false) = 1 - Pr[= true | q] := by
    rw [show (𝒟[q]).toPMF (some false) = Pr[= false | q] from rfl, probOutput_false_eq_sub,
      NeverFail.probFailure_eq_zero, tsub_zero]
  unfold tvDist SPMF.tvDist PMF.tvDist PMF.etvDist
  rw [tsum_fintype, Fintype.sum_option, Fintype.sum_bool, hp_none, hq_none,
    ENNReal.absDiff_self, zero_add, hp_true, hq_true, hp_false, hq_false,
    ENNReal.absDiff_tsub_tsub probOutput_le_one probOutput_le_one ENNReal.one_ne_top,
    show ENNReal.absDiff (Pr[= true | p]) (Pr[= true | q]) +
        ENNReal.absDiff (Pr[= true | p]) (Pr[= true | q]) =
        2 * ENNReal.absDiff (Pr[= true | p]) (Pr[= true | q]) from by ring,
    mul_div_assoc, ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top]
  exact ENNReal.absDiff_toReal probOutput_ne_top probOutput_ne_top

end ToVCVio
