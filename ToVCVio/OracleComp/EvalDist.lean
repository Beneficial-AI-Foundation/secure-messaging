/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.ProbCompLift
import ToVCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Sum

/-!
# Point-probability transport for `ProbComp` runtimes and `StateT` projections
-/

open OracleSpec ENNReal

namespace ToVCVio

/-- The canonical `ProbComp` runtime gives each singleton `{x}` the mass
`Pr{let y ← mx}[y = x]`. -/
lemma evalDist_probCompRuntime_singleton_eq {α : Type} [MeasurableSpace α]
    [MeasurableSingletonClass α] (mx : ProbComp α) (x : α) :
    ProbCompRuntime.probComp.evalDist mx {x} = Pr{let y ← mx}[y = x] := by
  rw [ProbCompRuntime.probComp_evalDist, prEvent_eq_evalDist_singleton]

/-- Lift a `.run` point-distribution equality to the `Bool` `.run'` projection. -/
lemma prEvent_run'_true_eq_of_run_prEvent_eq {σ : Type}
    {m₁ m₂ : StateT σ ProbComp Bool} (s : σ)
    (h : ∀ z, Pr{let x ← m₁.run s}[x = z] = Pr{let x ← m₂.run s}[x = z]) :
    Pr{let x ← m₁.run' s}[x = true] = Pr{let x ← m₂.run' s}[x = true] := by
  simp only [StateT.run'_eq]
  exact ((OracleComp.evalDistEq_of_forall_prEvent_eq_output h).map Prod.fst).prEvent_eq _

/-- Continuation events with equal probability on every possible output of a common
`ProbComp` draw give equal event probabilities after the draw. -/
lemma prEvent_bind_congr_of_mem_support {α β γ : Type} (mx : ProbComp α)
    {f : α → ProbComp β} {g : α → ProbComp γ} {p : β → Prop} {q : γ → Prop}
    (h : ∀ x ∈ support mx, Pr{let y ← f x}[p y] = Pr{let z ← g x}[q z]) :
    Pr{let y ← mx >>= f}[p y] = Pr{let z ← mx >>= g}[q z] := by
  rw [map_bind, map_bind]
  exact OracleComp.prEvent_bind_congr_of_support mx _ _ h

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
