import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.ProbCompLift
import VCVio.EvalDist.Defs.Instances
import ToMathlib.ProbabilityTheory.Coupling
import ToVCVio.EvalDist.Monad.Basic

/-!
# OracleComp EvalDist Lemmas

Coupled-bisimulation lemmas for `simulateQ` adversaries with stateful game
oracles whose implementations may call a second, base oracle interface. The
results are stated over output `SPMF` distributions and their couplings.

The general shape is an in-between simulator/reduction:

```text
specGame = {𝒪₁, 𝒪₂}        -- oracles visible to the adversary
specBase = {𝒪'₁, 𝒪'₂}      -- oracles available to the simulator

  ┌───────────────┐
  │ 𝒜^{𝒪₁, 𝒪₂}    │
  └───────┬───────┘
    │ query 𝒪ᵢ
    ▼
  ┌───────────────┐
  │ impl 𝒪ᵢ       │ : StateT σ (OracleComp specBase) _
  └───────┬───────┘
    │ may query 𝒪'ⱼ
    ▼
  ┌───────────────┐
  │ 𝒪'₁, 𝒪'₂      │
  └───────────────┘
```

For instance, the implementation of `𝒪₁` may call the base oracle `𝒪'₁`:

```text
impl 𝒪₁(x, s):
  y  ← 𝒪'₁(x)
  s' := update(s, x, y)
  return (reply(x, y), s')
```

After `simulateQ impl 𝒜` removes the `specGame` layer, the resulting
computation may still contain calls to `specBase`.

*NOTE:* The proofs for CKA from DDH don't use these lemmas.
We keep them for potential use in the future.

## Notation

### Couplings

A **coupling** of two probability distributions `μ` on `X` and
`ν` on `Y` is a joint distribution `γ` on `X × Y` whose marginals are `μ`
and `ν`. Two distributions are *coupled with respect to a relation*
`rel ⊆ X × Y` when there exists a coupling `γ` whose support is contained in `rel`.

### SPMF Bind

For `p : SPMF α` and `f : α → SPMF β`, `p >>= f : SPMF β` is the probability distribution
obtained by first sampling `a` from `p`, and then a value from `f a`.

### Per-Query Distributions

Consider two oracle implementations
`impl₁ impl₂ : QueryImpl specGame (StateT σ (OracleComp specBase))`.
For a game query `t` and a game state `s`, write

`μᵢ(t, s) = evalDist ((implᵢ t).run s)`

for the distribution of `(answer, nextState)` corresponding to `(t, s)`.

## Main Lemmas

For an oracle query `t` and two starting states `s₁, s₂`, assume there exists
a per-query coupling

`γ(t, s₁, s₂) : SPMF.Coupling (μ₁(t, s₁)) (μ₂(t, s₂))`.

such that every supported pair `((u₁, s₁'), (u₂, s₂'))` in `γ(t, s₁, s₂)` has
equal answers, `u₁ = u₂`, and `R`-related next states, `R s₁' s₂'`.

Then, we can lift this per-query coupling through a whole adversary interaction and output.
-/

open OracleSpec Option ENNReal BigOperators
open scoped OracleSpec.PrimitiveQuery

universe u

namespace SPMF

/-- **Bind equality from a coupling.**

Let `p` and `q` be distributions coupled by `c`. If every supported pair
`(a₁, a₂)` in `c` satisfies `f a₁ = g a₂`, then `p >>= f` and `q >>= g`
are equal distributions. -/
lemma IsCoupling.bind_eq {α₁ α₂ β : Type u}
    {p : SPMF α₁} {q : SPMF α₂} {c : SPMF (α₁ × α₂)}
    (hc : IsCoupling c p q)
    {f : α₁ → SPMF β} {g : α₂ → SPMF β}
    (h : ∀ a₁ a₂, c.1 (some (a₁, a₂)) ≠ 0 → f a₁ = g a₂) :
    p >>= f = q >>= g := by
  rw [show p = Prod.fst <$> c from hc.map_fst.symm,
      show q = Prod.snd <$> c from hc.map_snd.symm]
  rw [SPMF.fmap_eq_map, SPMF.fmap_eq_map]
  rw [bind_eq_pmf_bind, bind_eq_pmf_bind]
  simp only [PMF.bind_map]
  apply PMF.bind_congr
  intro o ho
  cases o with
  | none => rfl
  | some ab =>
    obtain ⟨a₁, a₂⟩ := ab
    simp only [Function.comp, Option.map]
    exact h a₁ a₂ ho

end SPMF

namespace OracleComp

variable {ι : Type} {specBase : OracleSpec ι}
variable [specBase.Fintype] [specBase.Inhabited]

/-- **Coupled bisimulation for `simulateQ` with `StateT`.**

If every related state pair `R s₁ s₂` admits a per-query coupling
`γ(t, s₁, s₂)` whose support satisfies
`((u₁, s₁'), (u₂, s₂')) ↦ u₁ = u₂ ∧ R s₁' s₂'`, then the full
`simulateQ` runs can be coupled with the same final condition.

Use this when the two per-query distributions need not be equal, but can be
coupled so that each query returns the same answer and preserves the state
relation. -/
lemma evalDist_simulateQ_run_coupled
    {ι' : Type} {specGame : OracleSpec ι'}
    {σ α : Type}
    -- Two implementations of the game oracles visible to the adversary.
    -- They may call the base oracle interface.
    (impl₁ impl₂ : QueryImpl specGame (StateT σ (OracleComp specBase)))
    -- Relation between two implementation states.
    (R : σ → σ → Prop)
    -- Per-query coupling assumption: from related states, the two oracles can
    -- be coupled so that they return the same answer and preserve `R` on next states.
    (hstep : ∀ (t : specGame.Domain) (s₁ s₂ : σ), R s₁ s₂ →
      ∃ c : _root_.SPMF.Coupling
          (evalDist ((impl₁ t).run s₁))
          (evalDist ((impl₂ t).run s₂)),
        ∀ a₁ a₂, c.1.1 (some (a₁, a₂)) ≠ 0 →
          a₁.1 = a₂.1 ∧ R a₁.2 a₂.2)
    -- If we run the adversary from related initial states.
    (adv : OracleComp specGame α) (s₁ s₂ : σ) (hr : R s₁ s₂) :
    -- Then the whole simulated executions admit an analogous coupling.
    ∃ c : _root_.SPMF.Coupling
        (evalDist ((simulateQ impl₁ adv).run s₁))
        (evalDist ((simulateQ impl₂ adv).run s₂)),
      ∀ a₁ a₂, c.1.1 (some (a₁, a₂)) ≠ 0 →
        a₁.1 = a₂.1 ∧ R a₁.2 a₂.2 := by
  revert s₁ s₂
  induction adv using OracleComp.inductionOn with
  | pure x =>
    intro s₁ s₂ hr
    exact ⟨⟨pure ((x, s₁), (x, s₂)), by constructor <;> simp⟩,
      fun a₁ a₂ h => by
        rcases a₁ with ⟨y₁, t₁⟩
        rcases a₂ with ⟨y₂, t₂⟩
        have hmem :
            ((y₁, t₁), (y₂, t₂)) ∈
              support (pure (((x, s₁), (x, s₂))) : SPMF ((α × σ) × (α × σ))) :=
          (_root_.SPMF.mem_support_iff _ _).2 h
        have hEq : ((y₁, t₁), (y₂, t₂)) = (((x, s₁), (x, s₂))) := by
          simpa [support_pure, Set.mem_singleton_iff] using hmem
        cases hEq
        exact ⟨rfl, hr⟩⟩
  | query_bind t oa ih =>
    intro s₁ s₂ hr
    rw [simulateQ_query_bind, StateT.run_bind]
    change ∃ c : _root_.SPMF.Coupling
        (evalDist (((impl₁ t).run s₁) >>= fun p => (simulateQ impl₁ (oa p.1)).run p.2))
        (evalDist (((impl₂ t).run s₂) >>= fun p => (simulateQ impl₂ (oa p.1)).run p.2)),
      ∀ a₁ a₂, c.1.1 (some (a₁, a₂)) ≠ 0 →
        a₁.1 = a₂.1 ∧ R a₁.2 a₂.2
    rw [evalDist_bind, evalDist_bind]
    obtain ⟨c, hc⟩ := hstep t s₁ s₂ hr
    classical
    let d : (specGame.Range t × σ) → (specGame.Range t × σ) → SPMF ((α × σ) × (α × σ)) :=
      fun p₁ p₂ =>
        if hrel : R p₁.2 p₂.2 then (Classical.choose (ih p₁.1 p₁.2 p₂.2 hrel)).1
        else failure
    have hd :
        ∀ p₁ p₂, c.1.1 (some (p₁, p₂)) ≠ 0 →
          _root_.SPMF.IsCoupling (d p₁ p₂)
            (evalDist ((simulateQ impl₁ (oa p₁.1)).run p₁.2))
            (evalDist ((simulateQ impl₂ (oa p₂.1)).run p₂.2)) := by
      intro p₁ p₂ hsupp
      rcases p₁ with ⟨u₁, s₁'⟩
      rcases p₂ with ⟨u₂, s₂'⟩
      obtain ⟨hout, hrel⟩ := hc (u₁, s₁') (u₂, s₂') hsupp
      subst hout
      have hdEq : d (u₁, s₁') (u₁, s₂') = (Classical.choose (ih u₁ s₁' s₂' hrel)).1 := by
        dsimp [d]
        rw [dif_pos hrel]
      rw [hdEq]
      exact (Classical.choose (ih u₁ s₁' s₂' hrel)).2
    refine ⟨⟨c.1 >>= fun p => d p.1 p.2, _root_.SPMF.IsCoupling.bind c d hd⟩, ?_⟩
    intro a₁ a₂ hsupp
    have hmem : ((a₁, a₂) :
        (α × σ) × (α × σ)) ∈ support (c.1 >>= fun p => d p.1 p.2) := by
      exact (_root_.SPMF.mem_support_iff _ _).2 hsupp
    rw [mem_support_bind_iff] at hmem
    rcases hmem with ⟨p, hp, hp'⟩
    have hpMass : c.1.1 (some p) ≠ 0 := by
      exact (_root_.SPMF.mem_support_iff _ _).1 hp
    rcases p with ⟨⟨u₁, s₁'⟩, ⟨u₂, s₂'⟩⟩
    obtain ⟨hout, hrel⟩ := hc (u₁, s₁') (u₂, s₂') hpMass
    subst hout
    have hdEq : d (u₁, s₁') (u₁, s₂') = (Classical.choose (ih u₁ s₁' s₂' hrel)).1 := by
      dsimp [d]
      rw [dif_pos hrel]
    have hp'Mass : ((Classical.choose (ih u₁ s₁' s₂' hrel)).1).1 (some (a₁, a₂)) ≠ 0 := by
      rw [← hdEq]
      exact (_root_.SPMF.mem_support_iff _ _).1 hp'
    exact (Classical.choose_spec (ih u₁ s₁' s₂' hrel)) a₁ a₂ hp'Mass

/-- **Output-equivalence corollary of coupled bisimulation.**

The previous lemma couples the full `.run` distributions in `SPMF (α × σ)`.
This corollary keeps only the first component: every paired outcome
`((u₁, s₁'), (u₂, s₂'))` has `u₁ = u₂`, so mapping `(u, s') ↦ u` on both
sides gives equality of the adversary's observable outputs. -/
lemma evalDist_simulateQ_run'_eq_of_bisim
    {ι' : Type} {specGame : OracleSpec ι'}
    {σ α : Type}
    -- Two stateful implementations of the game oracles.
    (impl₁ impl₂ : QueryImpl specGame (StateT σ (OracleComp specBase)))
    -- Relation maintained between their private states.
    (R : σ → σ → Prop)
    -- Per-query coupling assumption, as in `evalDist_simulateQ_run_coupled`.
    (hstep : ∀ (t : specGame.Domain) (s₁ s₂ : σ), R s₁ s₂ →
      ∃ c : _root_.SPMF.Coupling
          (evalDist ((impl₁ t).run s₁))
          (evalDist ((impl₂ t).run s₂)),
        ∀ a₁ a₂, c.1.1 (some (a₁, a₂)) ≠ 0 →
          a₁.1 = a₂.1 ∧ R a₁.2 a₂.2)
    -- Start the same adversary from related states.
    (adv : OracleComp specGame α) (s₁ s₂ : σ) (hr : R s₁ s₂) :
    -- The adversary's returned value has the same distribution on both sides.
    evalDist ((simulateQ impl₁ adv).run' s₁) =
      evalDist ((simulateQ impl₂ adv).run' s₂) := by
  obtain ⟨c, hc⟩ := evalDist_simulateQ_run_coupled impl₁ impl₂ R hstep adv s₁ s₂ hr
  have hmap :
      (evalDist ((simulateQ impl₁ adv).run s₁) >>= fun a₁ => pure a₁.1) =
      (evalDist ((simulateQ impl₂ adv).run s₂) >>= fun a₂ => pure a₂.1) := by
    exact _root_.SPMF.IsCoupling.bind_eq c.2 (fun a₁ a₂ hsupp => by
      obtain ⟨hout, _⟩ := hc _ _ hsupp
      simp [hout])
  simpa [map_eq_bind_pure_comp] using hmap

end OracleComp

/-! ## Point-probability transport for `ProbComp` runtimes and `StateT` projections

Two small `ProbComp`-level bridges, both reusable for any `ProbComp`/`StateT`
game: the canonical runtime's `evalDist` embedding is transparent to point
probabilities, and a `.run`-level distribution equality projects to the `Bool`
`.run'` probability. -/

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
