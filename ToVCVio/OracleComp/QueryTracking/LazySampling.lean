import VCVio.ProgramLogic.Relational.SimulateQ
import VCVio.OracleComp.Constructions.SampleableType

/-!
# State-relational coupling and external-sample commutation under `simulateQ`

Two distributional equivalence theorems for `simulateQ`-based oracle simulation
targeting `StateT σ ProbComp`, stated at the level of an arbitrary adversary
program over `OracleSpec`.

## Preliminaries

* **Coupling.** A coupling of two probability distributions `μ` on `X` and
  `ν` on `Y` is a joint distribution `γ` on `X × Y` whose marginals are `μ`
  and `ν`. Two distributions are *coupled with respect to a relation*
  `rel ⊆ X × Y` when there exists a coupling `γ` whose support is
  contained in `rel`.

* **`RelTriple x y rel`** A relational Hoare triple in VCVio.
  For oracle computations `x, y` and a binary relation `rel`, it states
  the existence of a coupling of the evaluation distributions `𝒟[x]`
  and `𝒟[y]` whose support is contained in `rel`.

* **`𝒟[·]`** `evalDist`, the underlying probability distribution of an
  oracle computation `x`.

* **Pair relations.** A binary relation on pairs of type `α × σ` is written
  `fun p₁ p₂ => Q p₁ p₂`, where `Q` is a `Prop`-valued expression in
  `p₁, p₂`, and `p_i.1 : α`, `p_i.2 : σ` are the first and second components
  of `p_i`. The relation `fun p₁ p₂ => p₁.1 = p₂.1 ∧ R p₁.2 p₂.2` thus reads
  "first components equal and second components `R`-related".

* **Running a `QueryImpl`.** An oracle implementation
  `impl : QueryImpl spec (StateT σ ProbComp)`
  takes an oracle query `t` and returns a stateful probabilistic computation
  `impl t`. Running that computation on a starting state `s` (via `.run s`) produces
  a per-query probabilistic pair `(a', s') : α × σ` (response and updated state,
  with `α = spec.Range t`).

* **The per-query `RelTriple` used below.**
  `RelTriple ((impl₁ t).run s₁) ((impl₂ t).run s₂)`
    `(fun p₁ p₂ => p₁.1 = p₂.1 ∧ R p₁.2 p₂.2)`
  says: there exists a coupling of the two `ProbComp (α × σ)` runs whose
  support consists only of joint outcomes `((a₁, s₁'), (a₂, s₂'))` with
  `a₁ = a₂` and `R s₁' s₂'` — i.e., responses agree and post-states stay
  `R`-related.

## Main results

* `probOutput_simulateQ_run'_eq_of_state_rel` — **state-relational coupling**.

  For two oracle implementations `impl₁, impl₂ : QueryImpl spec (StateT σ ProbComp)`
  over a state space `σ`, and a relation `R : σ → σ → Prop` on `σ`:

  - if for every oracle query `t : spec.Domain` and `R`-related states `s₁`,
  `s₂`, the per-query oracle computations
  `(impl_i t).run s_i : ProbComp (spec.Range t × σ)`
  satisfy the relational Hoare triple
  `RelTriple ((impl₁ t).run s₁) ((impl₂ t).run s₂) (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R p₁.2 p₂.2)`,

  - then for any `R`-related `s₁`, `s₂` and any adversary program `oa : OracleComp spec α`,
  the output distributions of `simulateQ impl₁ oa` and `simulateQ impl₂ oa` are equal:
  `evalDist ((simulateQ impl₁ oa).run' s₁) = evalDist ((simulateQ impl₂ oa).run' s₂)`,
  i.e. the adversary produces the same output probabilities under either
  implementation.

* `probOutput_simulateQ_greedyLazy_run'_eq` — **external-sample commutation**.

  A top-level sample `a ← $ᵗ τ` consumed only inside oracle bodies can be
  delayed into the first query via the canonical `greedyLazy`
  construction. Formally, for any family
  `implFam : τ → QueryImpl spec (StateT σ ProbComp)`,
  `evalDist (do let a ← $ᵗ τ; (simulateQ (implFam a) oa).run' s)`
    `= evalDist ((simulateQ (greedyLazy implFam) oa).run' (s, none))`.

* `probOutput_simulateQ_consumeLazy_run'_eq` — **external-sample consume-site commutation**.

  Given a "hit" predicate `hit : spec.Domain → Bool` marking the queries
  that consume the external sample `a : τ`, a top-level sample `a ← $ᵗ τ`
  can be deferred to the first hit query
  via the `consumeLazy` construction, *provided* `implFam` is
  constant in `τ` at non-hit queries (the `h_indep` hypothesis). Under that
  hypothesis,
  `evalDist (do let a ← $ᵗ τ; (simulateQ (implFam a) oa).run' s)`
    `= evalDist ((simulateQ (consumeLazy implFam hit) oa).run' (s, none))`.

-/

open OracleComp OracleSpec ENNReal

namespace OracleComp.ProgramLogic.Relational

variable {ι : Type} {spec : OracleSpec ι}
variable [spec.Fintype] [spec.Inhabited]
variable {σ α : Type}

/-! ## State-relational coupling -/

omit [spec.Fintype] [spec.Inhabited] in
/-- **State-relational coupling under `simulateQ`.**

Lifts per-query `RelTriple`s on "output equality and `R`-preservation on
post-states" to equal output distributions under `simulateQ` from any
`R`-related initial states. See the module docstring for the unfolded
statement.

This is `evalDist`-level convenience over `relTriple_simulateQ_run'`. -/
lemma probOutput_simulateQ_run'_eq_of_state_rel
    (impl₁ impl₂ : QueryImpl spec (StateT σ ProbComp))
    (R : σ → σ → Prop)
    (h_step : ∀ (t : spec.Domain) (s₁ s₂ : σ), R s₁ s₂ →
      RelTriple ((impl₁ t).run s₁) ((impl₂ t).run s₂)
        (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R p₁.2 p₂.2))
    (oa : OracleComp spec α) (s₁ s₂ : σ) (h : R s₁ s₂) :
    evalDist ((simulateQ impl₁ oa).run' s₁) =
      evalDist ((simulateQ impl₂ oa).run' s₂) :=
  evalDist_eq_of_relTriple_eqRel
    (relTriple_simulateQ_run' impl₁ impl₂ R oa h_step s₁ s₂ h)

/-! ## External-sample commutation via greedy lazy sampling -/

variable {τ : Type} [SampleableType τ]

/-- **Greedy-lazy lift** of a `τ`-parameterized impl-family.

Given a family `implFam : τ → QueryImpl spec (StateT σ ProbComp)` of oracle
implementations over a state space `σ`, produce a single implementation
over the augmented state space `σ × Option τ`, where the `Option τ` component
is a one-slot cache holding a single uniform sample of `τ`, shared across all
queries.

On the first invocation the cache is `none`: sample `a ← $ᵗ τ` uniformly,
run `implFam a`, and write `some a` to the cache. On every subsequent
invocation the cache is `some a` and that same `a` is reused as the
parameter to `implFam`, for any `t : spec.Domain`. -/
noncomputable def greedyLazy
    (implFam : τ → QueryImpl spec (StateT σ ProbComp)) :
    QueryImpl spec (StateT (σ × Option τ) ProbComp) :=
  -- per-query handler: answer query `t` from augmented state `(state, cache)`,
  -- returning the response and the updated augmented state
  fun t (state, cache) => do
    let a ← (match cache with
      | some a => (pure a : ProbComp τ)
      | none => ($ᵗ τ : ProbComp τ))
    -- run `implFam a` on query `t` and the current state
    let (u, state') ← (implFam a t) state
    pure (u, (state', some a))

omit [spec.Fintype] [spec.Inhabited] in
/-- **Auxiliary for `probOutput_simulateQ_greedyLazy_run'_eq`**.

For any adversary `oa : OracleComp spec α`, running it under `greedyLazy implFam` starting
from the augmented state `(s, some a)` (cache pre-populated to `a`) yields
the same output distribution as running it directly under `implFam a`
starting from `s`. -/
private theorem probOutput_simulateQ_greedyLazy_run'_some_eq
    (implFam : τ → QueryImpl spec (StateT σ ProbComp))
    (oa : OracleComp spec α) (a : τ) (s : σ) :
    evalDist ((simulateQ (implFam a) oa).run' s) =
      evalDist ((simulateQ (greedyLazy implFam) oa).run' (s, some a)) := by
  revert s
  induction oa using OracleComp.inductionOn with
  | pure x => intro s; simp [simulateQ_pure]
  | query_bind t k ih =>
    intro s
    apply evalDist_ext
    intro y
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, StateT.run'_eq, StateT.run_bind, map_bind]
    -- Unfold `greedyLazy` at `some a` to a pure post-processing.
    have hg : (greedyLazy implFam t).run (s, some a) =
        (implFam a t).run s >>= fun p => (pure (p.1, p.2, some a) : ProbComp _) := by
      simp [greedyLazy, StateT.run]
    rw [hg]
    simp only [monad_norm]
    -- Apply the inductive hypothesis pointwise.
    refine probOutput_bind_congr' _ y fun p => ?_
    have := ih p.1 p.2
    simp only [StateT.run'_eq] at this
    exact congrFun (congrArg DFunLike.coe this) y

omit [spec.Fintype] [spec.Inhabited] in
/-- **External-sample commutation into `simulateQ` via greedy lazy sampling.**

Sampling `a ← $ᵗ τ` at the top level and then running `simulateQ (implFam a)`
on the adversary is output-equivalent to running `simulateQ (greedyLazy implFam)`
starting from an empty cache. Both sample `a` exactly once; in the lazy form,
the sample happens at the first invocation rather than at the top.

For multi-sample cases (e.g. two external scalars `a, b`), apply sequentially:
peel `a` with this lemma, then `b` on the resulting half-lazy impl. -/
theorem probOutput_simulateQ_greedyLazy_run'_eq
    (implFam : τ → QueryImpl spec (StateT σ ProbComp))
    (oa : OracleComp spec α) (s : σ) :
    evalDist (do
      let a ← ($ᵗ τ : ProbComp τ)
      (simulateQ (implFam a) oa).run' s) =
    evalDist ((simulateQ (greedyLazy implFam) oa).run' (s, none)) := by
  revert s
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro s
    apply evalDist_ext
    intro y
    simp [simulateQ_pure]
  | query_bind t k ih =>
    intro s
    apply evalDist_ext
    intro y
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, StateT.run'_eq, StateT.run_bind, map_bind]
    -- Unfold `greedyLazy` at `none`: samples `a`, runs `implFam a`, caches.
    have hg : (greedyLazy implFam t).run (s, none) =
        (do let a ← ($ᵗ τ : ProbComp τ)
            let p ← (implFam a t).run s
            pure (p.1, p.2, some a)) := by
      simp [greedyLazy, StateT.run]
    rw [hg]
    -- Push bind associativity on both sides so the outer `$ᵗ τ` is shared.
    simp only [monad_norm]
    -- Both sides now share the outer `$ᵗ τ >>= fun a => (implFam a t).run s >>= ...`;
    -- reduce to pointwise equality and close via the cached-case lemma.
    refine probOutput_bind_congr' _ y fun a => ?_
    refine probOutput_bind_congr' _ y fun p => ?_
    -- At this point, LHS continuation is `(simulateQ (implFam a) (k p.1)).run' p.2`
    -- and RHS continuation is `(simulateQ (greedyLazy implFam) (k p.1)).run' (p.2, some a)`
    -- (modulo the `Prod.fst <$> .run` / `.run'` conversion). Apply the cached lemma.
    have h_cached := probOutput_simulateQ_greedyLazy_run'_some_eq
      implFam (k p.1) a p.2
    simp only [StateT.run'_eq] at h_cached
    exact congrFun (congrArg DFunLike.coe h_cached) y

/-! ## Consume-site-lazy variant

`consumeLazy implFam hit` samples and caches the external `τ` only at queries
flagged by `hit : spec.Domain → Bool` — matching the pattern where the
external sample is consumed at specific oracle sites rather than on every
query. Requires the hypothesis that at non-hit queries, `implFam` is constant
in `τ` (its output distribution does not depend on the external value). -/

/-- **Consume-site-lazy lift.** Samples `a ← $ᵗ τ` only at queries where
`hit t = true` (and caches the first such sample). At `hit t = false`, uses
whatever is in the cache (or `default` if still empty) without observable
effect — under the hypothesis that `implFam` doesn't depend on `τ` at such
queries. -/
noncomputable def consumeLazy
    (implFam : τ → QueryImpl spec (StateT σ ProbComp))
    (hit : spec.Domain → Bool) [Inhabited τ] :
    QueryImpl spec (StateT (σ × Option τ) ProbComp) :=
  -- per-query handler: answer query `t` from augmented state `(state, cache)`,
  -- returning the response and the updated augmented state
  fun t (state, cache) => do
    if hit t then
      let a ← (match cache with
        | some a => (pure a : ProbComp τ)
        | none => ($ᵗ τ : ProbComp τ))
      let (u, state') ← (implFam a t) state
      pure (u, (state', some a))
    else
      let a : τ := cache.getD default
      let (u, state') ← (implFam a t) state
      pure (u, (state', cache))

omit [spec.Fintype] [spec.Inhabited] in
/-- Auxiliary for `probOutput_simulateQ_consumeLazy_run'_eq`.

For any adversary `oa : OracleComp spec α`, running it under `consumeLazy implFam hit`
starting from the augmented state `(s, some a)` (cache pre-populated to `a`)
yields the same output distribution as running it directly under
`implFam a` starting from `s`. -/
private theorem probOutput_simulateQ_consumeLazy_run'_some_eq
    (implFam : τ → QueryImpl spec (StateT σ ProbComp))
    (hit : spec.Domain → Bool) [Inhabited τ]
    (oa : OracleComp spec α) (a : τ) (s : σ) :
    evalDist ((simulateQ (implFam a) oa).run' s) =
      evalDist ((simulateQ (consumeLazy implFam hit) oa).run' (s, some a)) := by
  revert s
  induction oa using OracleComp.inductionOn with
  | pure x => intro s; simp [simulateQ_pure]
  | query_bind t k ih =>
    intro s
    apply evalDist_ext
    intro y
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, StateT.run'_eq, StateT.run_bind, map_bind]
    -- Unfold `consumeLazy` at `some a` — same behavior whether `hit t` or not.
    have hg : (consumeLazy implFam hit t).run (s, some a) =
        (implFam a t).run s >>= fun p => (pure (p.1, p.2, some a) : ProbComp _) := by
      simp only [consumeLazy, StateT.run]
      split_ifs <;> simp [Option.getD]
    rw [hg]
    simp only [monad_norm]
    refine probOutput_bind_congr' _ y fun p => ?_
    have := ih p.1 p.2
    simp only [StateT.run'_eq] at this
    exact congrFun (congrArg DFunLike.coe this) y

omit [spec.Fintype] [spec.Inhabited] in
/-- **External-sample consume-site commutation into `simulateQ`.**

If `implFam a` depends on `a` only at queries `t` with `hit t = true` (the
`h_indep` hypothesis), then sampling `a ← $ᵗ τ` at the top and running
`simulateQ (implFam a)` is output-equivalent to running
`simulateQ (consumeLazy implFam hit)` from the empty cache. The external
sample is effectively deferred to the first hit query. -/
theorem probOutput_simulateQ_consumeLazy_run'_eq
    (implFam : τ → QueryImpl spec (StateT σ ProbComp))
    (hit : spec.Domain → Bool) [Inhabited τ]
    (h_indep : ∀ (t : spec.Domain) (s : σ) (a₁ a₂ : τ),
      hit t = false → (implFam a₁ t).run s = (implFam a₂ t).run s)
    (oa : OracleComp spec α) (s : σ) :
    evalDist (do
      let a ← ($ᵗ τ : ProbComp τ)
      (simulateQ (implFam a) oa).run' s) =
    evalDist ((simulateQ (consumeLazy implFam hit) oa).run' (s, none)) := by
  revert s
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro s
    apply evalDist_ext
    intro y
    simp [simulateQ_pure]
  | query_bind t k ih =>
    intro s
    apply evalDist_ext
    intro y
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, StateT.run'_eq, StateT.run_bind, map_bind]
    by_cases h : hit t = true
    · -- Hit query at empty cache: sample `a`, cache it, delegate to cached-case for the rest.
      have hg : (consumeLazy implFam hit t).run (s, none) =
          (do let a ← ($ᵗ τ : ProbComp τ)
              let p ← (implFam a t).run s
              pure (p.1, p.2, some a)) := by
        simp [consumeLazy, StateT.run, h]
      rw [hg]
      -- Keep this in `do`/`<$>` form so the pointwise replacement `eq1` matches below.
      simp only [bind_assoc, pure_bind]
      refine probOutput_bind_congr' _ y fun a => ?_
      refine probOutput_bind_congr' _ y fun p => ?_
      have h_cached := probOutput_simulateQ_consumeLazy_run'_some_eq
        implFam hit (k p.1) a p.2
      simp only [StateT.run'_eq] at h_cached
      exact congrFun (congrArg DFunLike.coe h_cached) y
    · -- Non-hit query at empty cache: impl is `τ`-independent; commute the outer sample
      -- past this query via `probOutput_bind_bind_swap`, then apply IH.
      have h_false : hit t = false := by
        cases ht : hit t with
        | true => exact absurd ht h
        | false => rfl
      have hg : (consumeLazy implFam hit t).run (s, none) =
          (implFam (default : τ) t).run s >>= fun p =>
            (pure (p.1, p.2, (none : Option τ)) : ProbComp _) := by
        simp [consumeLazy, StateT.run, h_false, Option.getD]
      rw [hg]
      -- Keep this in `do`/`<$>` form so the pointwise replacement `eq1` matches below.
      simp only [bind_assoc, pure_bind]
      -- Goal:
      --   Pr[= y | do a ← $F; p ← impl a t s; simulateQ (impl a) (k p.1) .run' p.2]
      --   = Pr[= y | do p ← impl default t s;
      --        simulateQ (consumeLazy impl hit) (k p.1) .run' (p.2, none)]
      have h_impl : ∀ a : τ, (implFam a t).run s = (implFam default t).run s :=
        fun a => h_indep t s a default h_false
      -- Step 1: replace `impl a t s` with `impl default t s` in LHS (under `a ← $F`).
      have eq1 : Pr[= y | do
            let a ← ($ᵗ τ : ProbComp τ)
            let p ← (implFam a t).run s
            Prod.fst <$> (simulateQ (implFam a) (k p.1)).run p.2] =
          Pr[= y | do
            let a ← ($ᵗ τ : ProbComp τ)
            let p ← (implFam default t).run s
            Prod.fst <$> (simulateQ (implFam a) (k p.1)).run p.2] := by
        refine probOutput_bind_congr' _ y fun a => ?_
        rw [h_impl a]
      rw [eq1]
      -- Step 2: swap `a ← $F` past `p ← impl default t s`.
      rw [probOutput_bind_bind_swap (mx := ($ᵗ τ : ProbComp τ))
          (my := (implFam default t).run s)
          (f := fun a p =>
            Prod.fst <$> (simulateQ (implFam a) (k p.1)).run p.2) (z := y)]
      -- Step 3: pointwise over `p`, apply IH at `p.2` (converting `.run'` ↔ `fst <$> .run`).
      refine probOutput_bind_congr' _ y fun p => ?_
      have h_ih := ih p.1 p.2
      simp only [StateT.run'_eq] at h_ih
      exact congrFun (congrArg DFunLike.coe h_ih) y

end OracleComp.ProgramLogic.Relational
