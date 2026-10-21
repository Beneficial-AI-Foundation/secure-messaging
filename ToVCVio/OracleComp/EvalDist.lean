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

/-- The canonical `ProbComp` runtime embeds through `evalDist` without changing
point probabilities. -/
lemma probOutput_probCompRuntime_evalDist_eq {α : Type} (mx : ProbComp α) (x : α) :
    Pr{let y ← ProbCompRuntime.probComp.evalDist mx}[y = x] = Pr{let y ← mx}[y = x] := by
  rfl

/-- Lift a `.run` point-distribution equality to the `Bool` `.run'` projection. -/
lemma probOutput_run'_true_eq_of_run_probOutput_eq {σ : Type}
    {m₁ m₂ : StateT σ ProbComp Bool} (s : σ)
    (h : ∀ z, Pr{let x ← m₁.run s}[x = z] = Pr{let x ← m₂.run s}[x = z]) :
    Pr{let x ← m₁.run' s}[x = true] = Pr{let x ← m₂.run' s}[x = true] := by
  change Pr{let x ← Prod.fst <$> m₁.run s}[x = true] = Pr{let x ← Prod.fst <$> m₂.run s}[x = true]
  simp only [map_eq_bind_pure_comp]
  rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
  exact tsum_congr fun z => by rw [h z]

end ToVCVio
