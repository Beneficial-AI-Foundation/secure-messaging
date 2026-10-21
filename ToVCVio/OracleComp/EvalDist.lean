/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.ProbCompLift
import ToVCVio.EvalDist.Monad.Basic

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

end ToVCVio
