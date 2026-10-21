/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import VCVio.EvalDist.MeasureTVDist.Basic
import VCVio.EvalDist.Monad.Map

/-!
# Total Variation Distance — Extra Lemmas

Generic total-variation-distance (`tvDist`) facts that hold for any monad with an
evaluation distribution.

* `tvDist_bind_const_right` removes a never-failing leading sample whose value is discarded from
  the right-hand computation.
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
/-- A weighted identical-until-bad bound, in the style of the fundamental lemma of game playing:
if `𝒟[f a] = 𝒟[g a]` for all `a` such that `¬ bad a`, and `tvDist (f a) (g a) ≤ c` even when `bad a`
holds, then averaging over any `mx : m α`,
`∑ₐ Pr{let x ← mx}[x = a] · tvDist (f a) (g a) ≤ c · Pr[bad | mx]`.
Sharpens VCVio's `tsum_probOutput_toReal_mul_tvDist_le_probEvent`, which only gets the trivial
worst-case slack `c = 1`. -/
lemma tsum_probOutput_toReal_mul_tvDist_le_const_mul_probEvent [MonadLiftT m PMF]
    {β : Type u} (mx : m α) (f g : α → m β) (bad : α → Prop)
    (c : ℝ) (hc : 0 ≤ c)
    (h_eq : ∀ a, ¬ bad a → 𝒟[f a] = 𝒟[g a])
    (h_le : ∀ a, bad a → tvDist (f a) (g a) ≤ c) :
    (∑' a, Pr{let x ← mx}[x = a].toReal * tvDist (f a) (g a)) ≤ c * Pr{let x ← mx}[bad x].toReal := by
  classical
  have h_p_summable : Summable (fun a : α => Pr{let x ← mx}[x = a].toReal) :=
    ENNReal.summable_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (OracleComp.tsum_prEvent_le_one _))
  calc (∑' a, Pr{let x ← mx}[x = a].toReal * tvDist (f a) (g a))
      ≤ ∑' a, if bad a then c * Pr{let x ← mx}[x = a].toReal else 0 := by
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
    _ = c * Pr{let x ← mx}[bad x].toReal := by
        rw [show (∑' a, if bad a then c * Pr{let x ← mx}[x = a].toReal else 0) =
            c * ∑' a, if bad a then Pr{let x ← mx}[x = a].toReal else 0 from by
          rw [← tsum_mul_left]
          exact tsum_congr fun a => by by_cases ha : bad a <;> simp [ha]]
        congr 1
        rw [OracleComp.prEvent_eq_tsum_ite, ENNReal.tsum_toReal_eq fun a => by
          by_cases ha : bad a
          · simp [ha,
              ne_top_of_le_ne_top ENNReal.one_ne_top ((prEvent_le_one _) (mx := mx) (x := a))]
          · simp [ha]]
        exact tsum_congr fun a => by by_cases ha : bad a <;> simp [ha]

/-- Bind-level identical-until-bad bound:
if `𝒟[f a] = 𝒟[g a]` for all `a` such that `¬ bad a`, and `tvDist (f a) (g a) ≤ c` even when `bad a`
holds, then averaging over any `mx : m α`,
`tvDist (mx >>= f) (mx >>= g) ≤ c · Pr[bad | mx]`.
Sharpens VCVio's `tvDist_bind_left_event_le`, which only gets the trivial worst-case slack
`c = 1`. -/
lemma tvDist_bind_left_event_le_const [LawfulMonad m] [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    {β : Type u} (mx : m α) (f g : α → m β) (bad : α → Prop) (c : ℝ) (hc : 0 ≤ c)
    (h_eq : ∀ a, ¬ bad a → 𝒟[f a] = 𝒟[g a])
    (h_le : ∀ a, bad a → tvDist (f a) (g a) ≤ c) :
    tvDist (mx >>= f) (mx >>= g) ≤ c * Pr{let x ← mx}[bad x].toReal :=
  le_trans (tvDist_bind_left_le mx f g)
    (tsum_probOutput_toReal_mul_tvDist_le_const_mul_probEvent mx f g bad c hc h_eq h_le)

/-- For _never-failing_ `Bool`-valued experiments, total-variation distance equals the optimal
distinguishing advantage exactly: `tvDist p q = |Pr[p = true] − Pr[q = true]|` — the best possible
distinguisher against `p`/`q` is just "guess the bit you observed," and no distinguisher can do
better.
Sharpens VCVio's `abs_probOutput_toReal_sub_le_tvDist` which only lower-bounds `tvDist`. -/
lemma tvDist_eq_abs_probOutput_true_sub {m : Type → Type v} [Monad m]
    [MonadLiftT m SPMF]
    (p q : m Bool) [NeverFail p] [NeverFail q] :
    tvDist p q = |(Pr{let x ← p}[x = true]).toReal - (Pr{let x ← q}[x = true]).toReal| := by
  have hp_none : (𝒟[p]).toPMF none = 0 := NeverFail.OracleComp.prFail_eq_zero
  have hq_none : (𝒟[q]).toPMF none = 0 := NeverFail.OracleComp.prFail_eq_zero
  have hp_true : (𝒟[p]).toPMF (some true) = Pr{let x ← p}[x = true] := rfl
  have hq_true : (𝒟[q]).toPMF (some true) = Pr{let x ← q}[x = true] := rfl
  have hp_false : (𝒟[p]).toPMF (some false) = 1 - Pr{let x ← p}[x = true] := by
    rw [show (𝒟[p]).toPMF (some false) = Pr{let x ← p}[x = false] from rfl, probOutput_false_eq_sub,
      NeverFail.OracleComp.prFail_eq_zero, tsub_zero]
  have hq_false : (𝒟[q]).toPMF (some false) = 1 - Pr{let x ← q}[x = true] := by
    rw [show (𝒟[q]).toPMF (some false) = Pr{let x ← q}[x = false] from rfl, probOutput_false_eq_sub,
      NeverFail.OracleComp.prFail_eq_zero, tsub_zero]
  unfold tvDist SPMF.tvDist PMF.tvDist PMF.etvDist
  rw [tsum_fintype, Fintype.sum_option, Fintype.sum_bool, hp_none, hq_none,
    ENNReal.absDiff_self, zero_add, hp_true, hq_true, hp_false, hq_false,
    ENNReal.absDiff_tsub_tsub (prEvent_le_one _) (prEvent_le_one _) ENNReal.one_ne_top,
    show ENNReal.absDiff (Pr{let x ← p}[x = true]) (Pr{let x ← q}[x = true]) +
        ENNReal.absDiff (Pr{let x ← p}[x = true]) (Pr{let x ← q}[x = true]) =
        2 * ENNReal.absDiff (Pr{let x ← p}[x = true]) (Pr{let x ← q}[x = true]) from by ring,
    mul_div_assoc, ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top]
  exact ENNReal.absDiff_toReal (prEvent_ne_top _) (prEvent_ne_top _)

end ToVCVio
