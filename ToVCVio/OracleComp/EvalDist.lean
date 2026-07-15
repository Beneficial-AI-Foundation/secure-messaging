/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.ProbCompLift
import VCVio.EvalDist.Defs.Instances
import ToVCVio.EvalDist.Monad.Basic

/-!
# `ProbComp` point-probability bridges

Two small `ProbComp`-level transport lemmas, reusable for any `ProbComp`/`StateT`
game: the canonical runtime's `evalDist` embedding is transparent to point
probabilities, and a `.run`-level distribution equality projects to the `Bool`
`.run'` probability.
-/

open OracleSpec Option ENNReal BigOperators

/-- The canonical `ProbComp` runtime embeds through `evalDist` without changing
point probabilities: `ProbCompRuntime.probComp.evalDist` is `𝒟[·]`. -/
lemma probOutput_probCompRuntime_evalDist_eq {α : Type} (mx : ProbComp α) (x : α) :
    Pr[= x | ProbCompRuntime.probComp.evalDist mx] = Pr[= x | mx] := by
  rfl

/-- Lift a `.run` point-distribution equality to the `Bool` `.run'` projection:
if two `StateT σ ProbComp Bool` computations have the same output distribution
when run from `s`, their `true`-output probabilities after `.run'` agree. -/
lemma probOutput_run'_true_eq_of_run_probOutput_eq {σ : Type}
    {m₁ m₂ : StateT σ ProbComp Bool} (s : σ)
    (h : ∀ z, Pr[= z | m₁.run s] = Pr[= z | m₂.run s]) :
    Pr[= true | m₁.run' s] = Pr[= true | m₂.run' s] := by
  change Pr[= true | Prod.fst <$> m₁.run s] = Pr[= true | Prod.fst <$> m₂.run s]
  simp only [map_eq_bind_pure_comp]
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  exact tsum_congr fun z => by rw [h z]
