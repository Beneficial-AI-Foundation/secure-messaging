/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.ProbCompLift
import VCVio.ProgramLogic.Relational.SimulateQ
import ToVCVio.EvalDist.Monad.Basic

/-!
# OracleComp EvalDist Compatibility Lemmas

Compatibility wrappers for coupling-based `simulateQ` proofs and two small
`ProbComp`/`StateT` probability projections.

VCVio's relational program logic now performs the whole-adversary coupling.
The lemmas below preserve the older explicit-coupling API by translating a
per-query coupling witness into a `RelTriple`, applying
`relTriple_simulateQ_run` or `relTriple_simulateQ_run'`, and translating the
result back only when the public statement requests an explicit coupling.
-/

open OracleSpec Option ENNReal BigOperators
open OracleComp.ProgramLogic.Relational
open scoped OracleSpec.PrimitiveQuery

universe u

namespace OracleComp

variable {ι : Type} {specBase : OracleSpec ι}
variable [IsUniformSpec specBase]

/-- Turn an explicit coupling whose support satisfies `R` into a relational triple. -/
private lemma relTriple_of_coupling
    {A B : Type} {oa : OracleComp specBase A} {ob : OracleComp specBase B}
    {R : A → B → Prop}
    (h : ∃ c : _root_.SPMF.Coupling (evalDist oa) (evalDist ob),
      ∀ a b, c.1.1 (some (a, b)) ≠ 0 → R a b) :
    RelTriple oa ob R := by
  obtain ⟨c, hc⟩ := h
  rw [relTriple_iff_relWP, relWP_iff_couplingPost]
  refine ⟨c, fun z hz => ?_⟩
  exact hc z.1 z.2 ((_root_.SPMF.mem_support_iff c.1 z).1 hz)

/-- **Coupled bisimulation for `simulateQ` with `StateT`.**

If every related state pair has a per-query coupling whose support has equal
answers and `R`-related successor states, the full simulated runs have the
same kind of coupling. -/
lemma evalDist_simulateQ_run_coupled
    {ι' : Type} {specGame : OracleSpec ι'}
    {σ α : Type}
    (impl₁ impl₂ : QueryImpl specGame (StateT σ (OracleComp specBase)))
    (R : σ → σ → Prop)
    (hstep : ∀ (t : specGame.Domain) (s₁ s₂ : σ), R s₁ s₂ →
      ∃ c : _root_.SPMF.Coupling
          (evalDist ((impl₁ t).run s₁))
          (evalDist ((impl₂ t).run s₂)),
        ∀ a₁ a₂, c.1.1 (some (a₁, a₂)) ≠ 0 →
          a₁.1 = a₂.1 ∧ R a₁.2 a₂.2)
    (adv : OracleComp specGame α) (s₁ s₂ : σ) (hr : R s₁ s₂) :
    ∃ c : _root_.SPMF.Coupling
        (evalDist ((simulateQ impl₁ adv).run s₁))
        (evalDist ((simulateQ impl₂ adv).run s₂)),
      ∀ a₁ a₂, c.1.1 (some (a₁, a₂)) ≠ 0 →
        a₁.1 = a₂.1 ∧ R a₁.2 a₂.2 := by
  have hrel : RelTriple
      ((simulateQ impl₁ adv).run s₁)
      ((simulateQ impl₂ adv).run s₂)
      (fun a₁ a₂ => a₁.1 = a₂.1 ∧ R a₁.2 a₂.2) :=
    relTriple_simulateQ_run impl₁ impl₂ R adv
      (fun t q₁ q₂ hR => relTriple_of_coupling (hstep t q₁ q₂ hR))
      s₁ s₂ hr
  rw [relTriple_iff_relWP, relWP_iff_couplingPost] at hrel
  obtain ⟨c, hc⟩ := hrel
  refine ⟨c, fun a₁ a₂ hmass => ?_⟩
  exact hc (a₁, a₂) ((_root_.SPMF.mem_support_iff c.1 (a₁, a₂)).2 hmass)

/-- **Output-equivalence corollary of coupled bisimulation.**

The final private states may differ, but the adversary's returned values have
the same evaluation distribution. -/
lemma evalDist_simulateQ_run'_eq_of_bisim
    {ι' : Type} {specGame : OracleSpec ι'}
    {σ α : Type}
    (impl₁ impl₂ : QueryImpl specGame (StateT σ (OracleComp specBase)))
    (R : σ → σ → Prop)
    (hstep : ∀ (t : specGame.Domain) (s₁ s₂ : σ), R s₁ s₂ →
      ∃ c : _root_.SPMF.Coupling
          (evalDist ((impl₁ t).run s₁))
          (evalDist ((impl₂ t).run s₂)),
        ∀ a₁ a₂, c.1.1 (some (a₁, a₂)) ≠ 0 →
          a₁.1 = a₂.1 ∧ R a₁.2 a₂.2)
    (adv : OracleComp specGame α) (s₁ s₂ : σ) (hr : R s₁ s₂) :
    evalDist ((simulateQ impl₁ adv).run' s₁) =
      evalDist ((simulateQ impl₂ adv).run' s₂) := by
  exact evalDist_eq_of_relTriple_eqRel
    (relTriple_simulateQ_run' impl₁ impl₂ R adv
      (fun t q₁ q₂ hR => relTriple_of_coupling (hstep t q₁ q₂ hR))
      s₁ s₂ hr)

end OracleComp

namespace ToVCVio

/-! ## Point-probability transport for `ProbComp` runtimes and `StateT` projections -/

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
