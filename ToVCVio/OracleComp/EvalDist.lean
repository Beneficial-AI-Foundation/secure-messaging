/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import VCVio.OracleComp.EvalDist.Sum
public import VCVio.OracleComp.ProbComp.Basic
public import VCVio.OracleComp.Constructions.SampleableType
import VCVio.EvalDist.Monad.Disagreement.Measure
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Event probabilities after a common draw

Let `mx : ProbComp α` be a draw, and let computations that depend on its output satisfy a relation
between event probabilities for every possible output `x` of `mx`. The relation persists after
the draw `x ← mx` for:

- an equality of event probabilities (`OracleComp.prEvent_bind_congr_of_support'`);
- a sum of two event probabilities (`ToVCVio.prEvent_bind_congr_eq_add`);
- two-sided additive bounds by `ε ≠ ∞`, which give a bound on the absolute difference of the real
  probabilities (`OracleComp.abs_toReal_prEvent_bind_sub_le`);
- an equality of two differences of real probabilities
  (`OracleComp.toReal_prEvent_bind_sub_eq_of_forall`).

For a uniform draw from a finite type, the real probability of an event is the average of its
probabilities over the drawn values (`OracleComp.prEvent_uniform_bind_toReal`).
`OracleComp.prEvent_eq_false_eq_one_sub` gives `Pr[false] = 1 - Pr[true]` for oracle
computations.
-/

@[expose] public section

open OracleSpec ENNReal

namespace ToVCVio

/-- If, on every possible output of a common `ProbComp` draw, one event probability is
the sum of two others, the same holds after the draw. -/
lemma prEvent_bind_congr_eq_add {α β γ₁ γ₂ : Type} (mx : ProbComp α)
    {f : α → ProbComp β} {g₁ : α → ProbComp γ₁} {g₂ : α → ProbComp γ₂}
    {p : β → Prop} {q₁ : γ₁ → Prop} {q₂ : γ₂ → Prop}
    (h : ∀ x ∈ support mx,
      Pr{let y ← f x}[p y] = Pr{let z ← g₁ x}[q₁ z] + Pr{let z ← g₂ x}[q₂ z]) :
    Pr{let y ← mx >>= f}[p y] =
      Pr{let z ← mx >>= g₁}[q₁ z] + Pr{let z ← mx >>= g₂}[q₂ z] := by
  simp only [OracleComp.prEvent_bind_eq_tsum, ← ENNReal.tsum_add]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ support mx
  · rw [h x hx, left_distrib]
  · simp only [prEvent_eq_zero_of_not_mem_support mx hx, zero_mul, add_zero]

end ToVCVio

namespace OracleComp

/-- An oracle computation returns `false` with the probability it does not return `true`. -/
lemma prEvent_eq_false_eq_one_sub {ι : Type} {spec : OracleSpec ι}
    [OracleSpec.AnswerMeasure spec] (mx : OracleComp spec Bool) :
    Pr{let x ← mx}[x = false] = 1 - Pr{let x ← mx}[x = true] := by
  rw [← prEvent_not_eq_one_sub mx (· = true)]
  simp only [Bool.not_eq_true]

/-- Maps agreeing on the support give the same distribution. -/
theorem evalDist_map_congr_support {α β : Type} (X : ProbComp α) (f g : α → β)
    (h : ∀ x ∈ support X, f x = g x) : f <$> X =ᵈ g <$> X := by
  simp only [map_eq_bind_pure_comp]
  exact EvalDistEq.bind_congr_of_support X fun x hx => by
    simp only [Function.comp_apply, h x hx, EvalDistEq.refl]

/-- An independent sample commutes past two dependent ones. -/
theorem prEvent_swap3 {α β γ : Type} (mx : ProbComp α) (my : α → ProbComp β)
    (mz : ProbComp γ) (f : α → β → γ → ProbComp Prop) :
    prEvent (mx >>= fun a => my a >>= fun b => mz >>= fun c => f a b c) =
      prEvent (mz >>= fun c => mx >>= fun a => my a >>= fun b => f a b c) :=
  (prEvent_bind_congr_of_support _ _ _ fun a _ =>
      OracleComp.prEvent_bind_bind_swap (my a) mz (fun b c => f a b c)).trans
    (OracleComp.prEvent_bind_bind_swap mx mz (fun a c => my a >>= fun b => f a b c))

/-- If `Pr{let z ← my x}[p z] = Pr{let z ← oc x}[p z]` for every `x ∈ support mx`, then
`Pr{let x ← mx >>= my}[p x] = Pr{let x ← mx >>= oc}[p x]`. Upstream
`prEvent_bind_congr_of_support` states this for the event after `map_bind`. -/
theorem prEvent_bind_congr_of_support' {α β : Type} (mx : ProbComp α) {my oc : α → ProbComp β}
    (p : β → Prop) (h : ∀ x ∈ support mx, Pr{let z ← my x}[p z] = Pr{let z ← oc x}[p z]) :
    Pr{let x ← mx >>= my}[p x] = Pr{let x ← mx >>= oc}[p x] := by
  rw [map_bind, map_bind]
  exact prEvent_bind_congr_of_support mx _ _ h

/-- A two-sided bound that holds for every possible output of a common draw holds after the draw:
if `Pr[q | my x]` and `Pr[q | oc x]` are within `ε ≠ ∞` of each other for every `x ∈ support mx`,
then the real probabilities of `q` after `mx >>= my` and `mx >>= oc` are within `ε.toReal`. -/
theorem abs_toReal_prEvent_bind_sub_le {α β : Type} (mx : ProbComp α) (my oc : α → ProbComp β)
    (q : β → Prop) (ε : ℝ≥0∞) (hε : ε ≠ ∞)
    (h₁ : ∀ x ∈ support mx, Pr{let z ← my x}[q z] ≤ Pr{let z ← oc x}[q z] + ε)
    (h₂ : ∀ x ∈ support mx, Pr{let z ← oc x}[q z] ≤ Pr{let z ← my x}[q z] + ε) :
    |(Pr{let x ← mx >>= my}[q x]).toReal - (Pr{let x ← mx >>= oc}[q x]).toReal| ≤ ε.toReal := by
  have hb₁ : Pr{let x ← mx >>= my}[q x] ≤ Pr{let x ← mx >>= oc}[q x] + ε := by
    have := prEvent_bind_le_add_of_disagree (D := fun _ => False) (ε₁ := 0) (by simp)
      (fun x hx _ => h₁ x hx)
    simpa only [add_zero] using this
  have hb₂ : Pr{let x ← mx >>= oc}[q x] ≤ Pr{let x ← mx >>= my}[q x] + ε := by
    have := prEvent_bind_le_add_of_disagree (D := fun _ => False) (ε₁ := 0) (by simp)
      (fun x hx _ => h₂ x hx)
    simpa only [add_zero] using this
  have hl := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _, hε⟩) hb₁
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _, hε⟩) hb₂
  rw [ENNReal.toReal_add (prEvent_ne_top _) hε] at hl hr
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- An equality of differences of real event probabilities that holds for every possible output of
a common draw holds after the draw: if `Pr[q | my x] - Pr[q | oc x] = Pr[q | my' x] - Pr[q | oc' x]`
for every `x ∈ support mx`, the same holds for `mx >>= my`, `mx >>= oc`, `mx >>= my'` and
`mx >>= oc'`. -/
theorem toReal_prEvent_bind_sub_eq_of_forall {α β : Type} (mx : ProbComp α)
    (my oc my' oc' : α → ProbComp β) (q : β → Prop)
    (h : ∀ x ∈ support mx, (Pr{let z ← my x}[q z]).toReal - (Pr{let z ← oc x}[q z]).toReal =
      (Pr{let z ← my' x}[q z]).toReal - (Pr{let z ← oc' x}[q z]).toReal) :
    (Pr{let x ← mx >>= my}[q x]).toReal - (Pr{let x ← mx >>= oc}[q x]).toReal =
      (Pr{let x ← mx >>= my'}[q x]).toReal - (Pr{let x ← mx >>= oc'}[q x]).toReal := by
  have hcross : Pr{let x ← mx >>= my}[q x] + Pr{let x ← mx >>= oc'}[q x] =
      Pr{let x ← mx >>= my'}[q x] + Pr{let x ← mx >>= oc}[q x] := by
    simp only [OracleComp.prEvent_bind_eq_tsum]
    rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
    refine tsum_congr fun x => ?_
    by_cases hx : x ∈ support mx
    · rw [← mul_add, ← mul_add]
      congr 1
      have hx' := h x hx
      rw [← ENNReal.toReal_eq_toReal_iff'
        (ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _, prEvent_ne_top _⟩)
        (ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _, prEvent_ne_top _⟩),
        ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _),
        ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _)]
      linarith
    · simp [(prEvent_eq_zero_of_not_mem_support _) hx]
  have h' := congrArg ENNReal.toReal hcross
  rw [ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _),
    ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _)] at h'
  linarith

/-- For a uniform draw from a finite type `α`, the real probability of an event after
`a ←$ α; f a` is the average `|α|⁻¹ · ∑ₐ Pr[p | f a]`. -/
theorem prEvent_uniform_bind_toReal {α β : Type} [SampleableType α] [Fintype α]
    (f : α → ProbComp β) (p : β → Prop) :
    (Pr{let y ← (do let a ← ($ᵗ α : ProbComp α); f a)}[p y]).toReal =
      (Fintype.card α : ℝ)⁻¹ * ∑ a, (Pr{let y ← f a}[p y]).toReal := by
  simp only [prEvent_bind_eq_sum_fintype, SampleableType.prEvent_uniformSample_eq_singleton,
    ← Finset.mul_sum]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_sum (fun _ _ => prEvent_ne_top _)]

end OracleComp
