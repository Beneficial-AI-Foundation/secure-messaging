import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# EvalDist Projections for Relational simulateQ

Convenience lemmas that expose relational `simulateQ` theorems as ordinary
equalities between `evalDist` distributions.

The VCVio relational lemmas conclude with statements of the form
`RelTriple oa ob EqRel`. This file packages the projection step from such a
relational proof to a plain equality
`evalDist oa = evalDist ob`.

## Notation

`RelTriple oa ob R` is the relational Hoare-style triple with precondition
`True`: the two computations `oa` and `ob` are related so that their outputs
satisfy the postcondition `R`.

For a computation `oa`, `𝒟[oa]` denotes `evalDist oa`.

For stateful computations, `.run` returns both the output and final state,
while `.run'` returns only the output.

## Main Lemmas

* `evalDist_simulateQ_run'_eq_of_impl_evalDist_eq`: if two oracle
  implementations have the same `(answer, state)` distribution for every query and
  state, then the adversary's output distributions after `.run'` are equal.
* `evalDist_simulateQ_run_eq_of_impl_eq_preservesInv`: if two oracle implementations
  in `StateT σ ProbComp` are definitionally equal on invariant states, then it
  is enough to show that the right-hand implementation preserves the invariant;
  the full `.run` distributions are equal.
-/
open ENNReal OracleSpec OracleComp
open scoped OracleSpec.PrimitiveQuery

universe u

namespace OracleComp.ProgramLogic.Relational

variable {ι : Type u} {spec : OracleSpec ι}
variable {α : Type}

/-- **Output equality from per-query distribution equality.**

If the two oracle implementations have the same distribution for every query
step, then simulating the same adversary with either implementation gives the
same output distribution after `.run'`.

This is the `evalDist` projection of
`relTriple_simulateQ_run'_of_impl_evalDist_eq`; `.run'` discards the final
private state and keeps only the adversary's returned value. -/
theorem evalDist_simulateQ_run'_eq_of_impl_evalDist_eq
    {ι₁ : Type u} {ι₂ : Type u}
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
    {σ : Type}
    -- Two implementations of the game oracle interface. Their handlers may
    -- call different base oracle interfaces, `spec₁` and `spec₂`.
    (impl₁ : QueryImpl spec (StateT σ (OracleComp spec₁)))
    (impl₂ : QueryImpl spec (StateT σ (OracleComp spec₂)))
    -- The adversary/program that queries `spec`.
    (oa : OracleComp spec α)
    -- Per-query equality of the two output distributions.
    (himpl : ∀ (t : spec.Domain) (s : σ),
      𝒟[(impl₁ t).run s] = 𝒟[(impl₂ t).run s])
    -- Start from equal states.
    (s₁ s₂ : σ) (hs : s₁ = s₂) :
    -- After `.run'`, only the adversary's output remains.
    evalDist ((simulateQ impl₁ oa).run' s₁) =
      evalDist ((simulateQ impl₂ oa).run' s₂) := by
  exact evalDist_eq_of_relTriple_eqRel
    (relTriple_simulateQ_run'_of_impl_evalDist_eq impl₁ impl₂ oa himpl s₁ s₂ hs)

/-- **Full-run equality from invariant-preserving handler equality.**

If two implementations in `StateT σ ProbComp` agree on states satisfying
`Inv`, and `impl₂` preserves `Inv`, then simulating the same adversary with
either implementation gives the same full `.run` distribution.

This is the `evalDist` projection of
`relTriple_simulateQ_run_eqRel_of_impl_eq_preservesInv`. Preservation is only
stated for `impl₂` because the implementations are equal on invariant states,
so preservation transfers to `impl₁`. -/
theorem evalDist_simulateQ_run_eq_of_impl_eq_preservesInv
    {ι : Type} {spec : OracleSpec ι}
    {σ : Type _}
    -- Two implementations of the same oracle interface in `StateT σ ProbComp`.
    (impl₁ impl₂ : QueryImpl spec (StateT σ ProbComp))
    -- Invariant describing the states where the implementations agree.
    (Inv : σ → Prop)
    -- The adversary/program that queries `spec`.
    (oa : OracleComp spec α)
    -- On invariant states, corresponding handlers are exactly equal.
    (himpl_eq : ∀ (t : spec.Domain) (s : σ), Inv s → (impl₁ t).run s = (impl₂ t).run s)
    -- It is enough to prove preservation for `impl₂`; on invariant states,
    -- `impl₁` has the same query behavior by `himpl_eq`.
    (hpres₂ : ∀ (t : spec.Domain) (s : σ), Inv s →
      ∀ z ∈ support ((impl₂ t).run s), Inv z.2)
    -- Start from an invariant state.
    (s : σ) (hs : Inv s) :
    -- The whole simulated `(output, finalState)` distributions agree.
    evalDist ((simulateQ impl₁ oa).run s) = evalDist ((simulateQ impl₂ oa).run s) := by
  exact evalDist_eq_of_relTriple_eqRel
    (relTriple_simulateQ_run_eqRel_of_impl_eq_preservesInv
      impl₁ impl₂ Inv oa himpl_eq hpres₂ s hs)

end OracleComp.ProgramLogic.Relational
