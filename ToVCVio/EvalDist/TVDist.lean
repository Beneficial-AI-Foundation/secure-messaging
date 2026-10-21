/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import VCVio.EvalDist.MeasureTVDist.Bind
import VCVio.EvalDist.MeasureTVDist.Event
import VCVio.EvalDist.Monad.Map
import VCVio.EvalDist.EvalDistEq
import ToVCVio.EvalDist.Monad.Basic

/-!
# Total Variation Distance — Extra Lemmas

Generic total-variation-distance (`measureTVDist`) facts that hold for any monad with an
evaluation distribution.

* `measureTVDist_bind_const_right` removes a lossless leading sample whose value is discarded
  from the right-hand computation.
* `measureTVDist_bind_left_event_le_const` (with its tsum form
  `tsum_prEvent_toReal_mul_measureTVDist_le_const_mul_prEvent`) is VCVio's
  `OracleComp.measureTVDist_bind_left_le_prEvent_of_evalDistEq` with a tunable per-branch bound
  `c` in place of the trivial bound `1`, in any monad.
* `measureTVDist_eq_abs_prEvent_true_sub` computes the exact total-variation distance between two
  lossless `Bool`-valued computations, sharpening `abs_prEvent_toReal_sub_le_measureTVDist`
  (which only gives one inequality direction) to an equality.
-/

open MeasureTheory
open scoped ENNReal

namespace ToVCVio

universe v

variable {α : Type} {m : Type → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- Total-variation distance is unaffected by a trailing bind whose result is discarded: if `mx`
is lossless, `mx >>= fun _ => my` has exactly the same distribution as `my`. -/
lemma measureTVDist_bind_const_right {β : Type} [MeasurableSpace β]
    (mx' : m β) (mx : m α) (my : m β) (hmx : Pr{let _ ← mx}[True] = 1 := by simp) :
    measureTVDist mx' (mx >>= fun _ => my) = measureTVDist mx' my := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_true_eq_evalDist_apply_univ] at hmx
  simp only [measureTVDist, evalDist_bind_const, hmx, one_smul]

/-- A weighted identical-until-bad bound, in the style of the fundamental lemma of game playing:
if `f a =ᵈ g a` for all `a` such that `¬ bad a`, and `δ(f a, g a) ≤ c` even when `bad a`
holds, then averaging over any `mx : m α`,
`∑ₐ Pr[x = a | mx] · δ(f a, g a) ≤ c · Pr[bad | mx]`, where `δ` is `measureTVDist`.
Sharpens the trivial worst-case slack `c = 1`. -/
lemma tsum_prEvent_toReal_mul_measureTVDist_le_const_mul_prEvent {β : Type} [MeasurableSpace β]
    (mx : m α) (f g : α → m β) (bad : α → Prop) (c : ℝ) (hc : 0 ≤ c)
    (h_eq : ∀ a, ¬ bad a → f a =ᵈ g a)
    (h_le : ∀ a, bad a → measureTVDist (f a) (g a) ≤ c) :
    (∑' a, Pr{let x ← mx}[x = a].toReal * measureTVDist (f a) (g a)) ≤
      c * Pr{let x ← mx}[bad x].toReal := by
  classical
  have hterm : ∀ a, Pr{let x ← mx}[x = a] * measureETVDist (f a) (g a) ≤
      ENNReal.ofReal c * (if bad a then Pr{let x ← mx}[x = a] else 0) := by
    intro a
    by_cases ha : bad a
    · rw [ite_eq_left ha, mul_comm]
      exact mul_le_mul'
        ((ENNReal.le_ofReal_iff_toReal_le (measureETVDist_ne_top _ _) hc).2 (h_le a ha)) le_rfl
    · rw [ite_eq_right ha, mul_zero, (measureETVDist_eq_zero_iff _ _).2 (h_eq a ha).evalDist_eq,
        mul_zero]
  have hsum : ∑' a, Pr{let x ← mx}[x = a] * measureETVDist (f a) (g a) ≤
      ENNReal.ofReal c * Pr{let x ← mx}[bad x] := by
    refine (ENNReal.tsum_le_tsum hterm).trans ?_
    rw [ENNReal.tsum_mul_left]
    exact mul_le_mul' le_rfl (tsum_ite_prEvent_eq_le_prEvent mx bad)
  calc (∑' a, Pr{let x ← mx}[x = a].toReal * measureTVDist (f a) (g a))
      = (∑' a, Pr{let x ← mx}[x = a] * measureETVDist (f a) (g a)).toReal := by
        rw [ENNReal.tsum_toReal_eq fun a =>
          ENNReal.mul_ne_top (prEvent_ne_top _) (measureETVDist_ne_top _ _)]
        simp only [ENNReal.toReal_mul, measureTVDist_eq_toReal_measureETVDist]
    _ ≤ (ENNReal.ofReal c * Pr{let x ← mx}[bad x]).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (prEvent_ne_top _)) hsum
    _ = c * Pr{let x ← mx}[bad x].toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]

/-- Bind-level identical-until-bad bound:
if `f a =ᵈ g a` for all `a` such that `¬ bad a`, and `δ(f a, g a) ≤ c` even when `bad a`
holds, then averaging over any `mx : m α`,
`δ(mx >>= f, mx >>= g) ≤ c · Pr[bad | mx]`, where `δ` is `measureTVDist`.
Sharpens VCVio's `OracleComp.measureTVDist_bind_left_le_prEvent_of_evalDistEq`, which only gets
the trivial worst-case slack `c = 1`. -/
lemma measureTVDist_bind_left_event_le_const {β : Type} [MeasurableSpace β]
    (mx : m α) (f g : α → m β) (bad : α → Prop) (c : ℝ) (hc : 0 ≤ c)
    (h_eq : ∀ a, ¬ bad a → f a =ᵈ g a)
    (h_le : ∀ a, bad a → measureTVDist (f a) (g a) ≤ c) :
    measureTVDist (mx >>= f) (mx >>= g) ≤ c * Pr{let x ← mx}[bad x].toReal := by
  let : MeasurableSpace α := ⊤
  have hbound : ∀ᵐ a ∂𝒟[mx], measureETVDist (f a) (g a) ≤
      {a | bad a}.indicator (fun _ => ENNReal.ofReal c) a := by
    refine Filter.Eventually.of_forall fun a => ?_
    by_cases ha : bad a
    · rw [Set.indicator_of_mem (by exact ha)]
      exact (ENNReal.le_ofReal_iff_toReal_le (measureETVDist_ne_top _ _) hc).2 (h_le a ha)
    · rw [Set.indicator_of_notMem (by exact ha),
        (measureETVDist_eq_zero_iff _ _).2 (h_eq a ha).evalDist_eq]
  have hint : ∫⁻ a, {a | bad a}.indicator (fun _ => ENNReal.ofReal c) a ∂𝒟[mx] =
      ENNReal.ofReal c * Pr{let x ← mx}[bad x] := by
    rw [lintegral_indicator_const MeasurableSet.of_discrete, prEvent_eq_evalDist_of_discrete]
  refine (measureTVDist_bind_bind_le_lintegral mx f g .of_discrete .of_discrete _ hbound
    (by rw [hint]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (prEvent_ne_top _))).trans ?_
  rw [hint, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]

/-- For _lossless_ `Bool`-valued experiments, total-variation distance equals the optimal
distinguishing advantage exactly: `δ(p, q) = |Pr[p = true] − Pr[q = true]|` — the best possible
distinguisher against `p`/`q` is just "guess the bit you observed," and no distinguisher can do
better.
Sharpens VCVio's `abs_prEvent_toReal_sub_le_measureTVDist` which only lower-bounds
`measureTVDist`. -/
lemma measureTVDist_eq_abs_prEvent_true_sub (p q : m Bool)
    (hp : Pr{let _ ← p}[True] = 1 := by simp) (hq : Pr{let _ ← q}[True] = 1 := by simp) :
    measureTVDist p q =
      |(Pr{let x ← p}[x = true]).toReal - (Pr{let x ← q}[x = true]).toReal| := by
  rw [prEvent_true_eq_evalDist_apply_univ] at hp hq
  have hle (μ : Measure Bool) (hμ : μ Set.univ = 1) (s : Set Bool) : μ s ≤ 1 :=
    (measure_mono (Set.subset_univ s)).trans hμ.le
  have hcompl (μ : Measure Bool) (hμ : μ Set.univ = 1) : μ {false} = 1 - μ {true} := by
    have hs : ({false} : Set Bool) = {true}ᶜ := by ext b; cases b <;> simp
    rw [hs, measure_compl (measurableSet_singleton _)
      (ne_top_of_le_ne_top ENNReal.one_ne_top (hle μ hμ _)), hμ]
  rw [prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton,
    ← ENNReal.absDiff_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (hle _ hp _))
      (ne_top_of_le_ne_top ENNReal.one_ne_top (hle _ hq _))]
  unfold measureTVDist Measure.tvDist
  congr 1
  refine le_antisymm ?_ (Measure.absDiff_apply_le_etvDist _ _ (measurableSet_singleton true))
  refine iSup_le fun ⟨s, _⟩ => ?_
  have key : s = ∅ ∨ s = {true} ∨ s = {false} ∨ s = Set.univ := by
    by_cases ht : true ∈ s <;> by_cases hf : false ∈ s
    · exact Or.inr <| Or.inr <| Or.inr <| by ext b; cases b <;> simp [ht, hf]
    · exact Or.inr <| Or.inl <| by ext b; cases b <;> simp [ht, hf]
    · exact Or.inr <| Or.inr <| Or.inl <| by ext b; cases b <;> simp [ht, hf]
    · exact Or.inl <| by ext b; cases b <;> simp [ht, hf]
  rcases key with rfl | rfl | rfl | rfl
  · simp only [measure_empty, ENNReal.absDiff_self, zero_le]
  · exact le_rfl
  · rw [hcompl _ hp, hcompl _ hq,
      ENNReal.absDiff_tsub_tsub (hle _ hp _) (hle _ hq _) ENNReal.one_ne_top]
  · simp only [hp, hq, ENNReal.absDiff_self, zero_le]

end ToVCVio
