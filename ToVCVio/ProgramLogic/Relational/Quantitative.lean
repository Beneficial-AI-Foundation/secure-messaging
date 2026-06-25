/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.ProgramLogic.Relational.Quantitative

/-!
# Real-valued TV-distance convexity over a `bind`

VCVio's `tvDist` is real-valued, and the framework pairs each real-valued `tvDist_*` bound with an
`ofReal_*` companion in `ℝ≥0∞` (e.g. `tvDist_bind_left_event_le` and its
`ofReal_tvDist_bind_left_event_le` companion). This file adds the real-valued convex-combination
("const") bound, completing the pair whose `ℝ≥0∞` side is `ofReal_tvDist_bind_left_le_const`:

* `tvDist_bind_left_le_const` — per-`a` bound restricted to `a ∈ support mx`;
* `tvDist_bind_left_le_const'` — the unrestricted `∀ a` companion.

Both are proved directly from `tvDist_bind_left_le` (the weighted-sum bound) and the fact that the
output distribution has total mass `1`, with no detour through `ENNReal.ofReal`. Unlike a real bound
threaded through `ofReal`, no `0 ≤ c` hypothesis is needed: when `mx` has unit mass its support is
nonempty, so `0 ≤ tvDist (f a) (g a) ≤ c` already forces `0 ≤ c`. The signatures mirror
`ofReal_tvDist_bind_left_le_const`/`'` exactly (same instances, same `support`-restricted vs.
unrestricted hypothesis split), with `c : ℝ` in place of `ε : ℝ≥0∞`.
-/

open ENNReal OracleSpec OracleComp
open scoped OracleSpec.PrimitiveQuery

namespace OracleComp.ProgramLogic.Relational

universe u v

/-- If `tvDist (f a) (g a) ≤ c` for every `a ∈ support mx`, then `tvDist (mx >>= f) (mx >>= g) ≤ c`.
Real-valued companion of `ofReal_tvDist_bind_left_le_const`, proved directly from the weighted-sum
bound `tvDist_bind_left_le` and `∑' a, Pr[= a | mx] = 1`. -/
theorem tvDist_bind_left_le_const
    {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    [MonadLiftT m SetM] [EvalDistCompatible m]
    {α β : Type u} (mx : m α) (f g : α → m β) (c : ℝ)
    (hfg : ∀ a, a ∈ support mx → tvDist (f a) (g a) ≤ c) :
    tvDist (mx >>= f) (mx >>= g) ≤ c := by
  classical
  have hprob_ne_top : ∀ a : α, Pr[= a | mx] ≠ ⊤ := fun a =>
    ne_top_of_le_ne_top one_ne_top (probOutput_le_one (mx := mx) (x := a))
  have hp_sum_ne_top : (∑' a : α, Pr[= a | mx]) ≠ ⊤ := by
    rw [tsum_probOutput_of_liftM_PMF]; exact one_ne_top
  have hp_summable : Summable (fun a : α => Pr[= a | mx].toReal) :=
    ENNReal.summable_toReal hp_sum_ne_top
  have hp_sum_toReal : (∑' a : α, Pr[= a | mx].toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq hprob_ne_top, tsum_probOutput_of_liftM_PMF, ENNReal.toReal_one]
  have hlhs_nonneg : ∀ a : α, 0 ≤ Pr[= a | mx].toReal * tvDist (f a) (g a) :=
    fun _ => mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _)
  have hlhs_le_p : ∀ a : α,
      Pr[= a | mx].toReal * tvDist (f a) (g a) ≤ Pr[= a | mx].toReal :=
    fun _ => mul_le_of_le_one_right ENNReal.toReal_nonneg (tvDist_le_one _ _)
  have hlhs_summable :
      Summable (fun a : α => Pr[= a | mx].toReal * tvDist (f a) (g a)) :=
    Summable.of_nonneg_of_le hlhs_nonneg hlhs_le_p hp_summable
  have hrhs_summable : Summable (fun a : α => Pr[= a | mx].toReal * c) :=
    Summable.mul_right _ hp_summable
  refine (tvDist_bind_left_le mx f g).trans ?_
  calc
    (∑' a : α, Pr[= a | mx].toReal * tvDist (f a) (g a))
        ≤ ∑' a : α, Pr[= a | mx].toReal * c :=
          Summable.tsum_le_tsum
            (fun a => by
              by_cases ha : a ∈ support mx
              · exact mul_le_mul_of_nonneg_left (hfg a ha) ENNReal.toReal_nonneg
              · rw [probOutput_eq_zero_of_not_mem_support ha]; simp)
            hlhs_summable hrhs_summable
    _ = (∑' a : α, Pr[= a | mx].toReal) * c := Summable.tsum_mul_right _ hp_summable
    _ = c := by rw [hp_sum_toReal, one_mul]

/-- Unrestricted companion of `tvDist_bind_left_le_const`: a uniform per-`a` bound `tvDist (f a)
(g a) ≤ c` lifts through the shared `mx` bind. Mirrors `ofReal_tvDist_bind_left_le_const'`. -/
theorem tvDist_bind_left_le_const'
    {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    [MonadLiftT m SetM] [EvalDistCompatible m]
    {α β : Type u} (mx : m α) (f g : α → m β) (c : ℝ)
    (hfg : ∀ a, tvDist (f a) (g a) ≤ c) :
    tvDist (mx >>= f) (mx >>= g) ≤ c :=
  tvDist_bind_left_le_const mx f g c fun a _ => hfg a

end OracleComp.ProgramLogic.Relational
