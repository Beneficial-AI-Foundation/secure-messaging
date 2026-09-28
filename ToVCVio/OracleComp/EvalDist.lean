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
    Pr[= x | ProbCompRuntime.probComp.evalDist mx] = Pr[= x | mx] := by
  rfl

/-- Lift a `.run` point-distribution equality to the `Bool` `.run'` projection. -/
lemma probOutput_run'_true_eq_of_run_probOutput_eq {σ : Type}
    {m₁ m₂ : StateT σ ProbComp Bool} (s : σ)
    (h : ∀ z, Pr[= z | m₁.run s] = Pr[= z | m₂.run s]) :
    Pr[= true | m₁.run' s] = Pr[= true | m₂.run' s] := by
  change Pr[= true | Prod.fst <$> m₁.run s] = Pr[= true | Prod.fst <$> m₂.run s]
  simp only [map_eq_bind_pure_comp]
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  exact tsum_congr fun z => by rw [h z]

end ToVCVio
