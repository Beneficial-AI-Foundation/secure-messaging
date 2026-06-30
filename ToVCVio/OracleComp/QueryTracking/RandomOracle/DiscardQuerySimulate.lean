/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.OracleComp.SimSemantics.StateT.Basic
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.OracleComp.SimSemantics.Append

/-!
# Discarded random-oracle query removal under `simulateQ`

The lazy random oracle has the property that a *result-discarded* query at a point `d`, prepended
to any computation `p` that accesses the oracle *only through the random oracle*, is invisible in
the output distribution. Concretely, at the `OracleComp (D →ₒ R)` level:

```
𝒟[(simulateQ randomOracle ((D →ₒ R).query d >>= fun _ => p)).run' qc]
  = 𝒟[(simulateQ randomOracle p).run' qc]
```

(`evalDist_simulateQ_roImpl_discard_run'`). This is a genuine *resampling*/lazy-sampling
fact: pre-sampling `d` then running `p` has the same output marginal as running `p` fresh, because
`p` reads `d` only via `randomOracle` (which resamples on a cache miss) and, if `p` never queries
`d`, the extra cache entry is invisible to `run'`.

The Encrypt-then-MAC authenticity hop needs the *lifted* statement: an adversary `adv` over an
arbitrary spec is folded by `simulateQ` into a stateful interpreter whose state carries a lazy
random-oracle cache as one component (`σ × (D →ₒ R).QueryCache`); two interpreters `impl₁`,
`impl₂` agree on every query *except* that, for some queries, `impl₂` additionally performs a
**discarded** random-oracle query at a point `d` before running `impl₁`'s handler. Provided
`impl₁` accesses the cache component *only via the random oracle* (`RespectsRO impl₁`), the two
interpreters produce the same output distribution (`evalDist_simulateQ_run'_discardRO`).

The `RespectsRO` hypothesis is essential: the discard-removal is **false** for interpreters that
inspect the cache raw (e.g. a bare `get` reading `qc d`), since a discarded `randomOracle d` writes
`d ↦ r` (uniform) into the cache, which such an interpreter could observe. Routing every cache
access through `randomOracle` rules this out: a `randomOracle d` read resamples on a miss and is
hit-consistent, so a pre-sampled fresh entry is distributionally invisible.
-/

open OracleComp OracleSpec ENNReal

namespace OracleComp

variable {D R : Type} [DecidableEq D] [SampleableType R]
  {ι : Type} {spec : OracleSpec ι} {σ α : Type}

/-- The combined interpreter `unifSpec + (D →ₒ R)` into `StateT (D →ₒ R).QueryCache ProbComp`:
forward uniform-sampling queries (the cache passes through untouched) and answer `D →ₒ R` queries
with the lazy random oracle. This is the ambient handler against which a `RespectsRO` body is run:
the only cache access is via `randomOracle`. -/
noncomputable def roImpl (D R : Type) [DecidableEq D] [SampleableType R] :
    QueryImpl (unifSpec + (D →ₒ R)) (StateT (D →ₒ R).QueryCache ProbComp) :=
  unifFwdImpl (D →ₒ R) + (D →ₒ R).randomOracle

/-! ## The true absorption lemma

(The independent-bind swap helper `evalDist_bind_bind_swap` lives upstream in
`VCVio.EvalDist.Monad.Basic`.) -/

/-- Running `randomOracle` on a single query at `d` from a cache that misses `d`: sample uniformly
and cache the result. -/
private theorem randomOracle_run_none
    (d : D) (qc : (D →ₒ R).QueryCache) (hqc : qc d = none) :
    ((D →ₒ R).randomOracle d).run qc =
      (fun r => (r, qc.cacheQuery d r)) <$> ($ᵗ R) :=
  QueryImpl.withCaching_run_none _ hqc

/-- Running `randomOracle` on a single query at `d` from a cache that hits `d`: return the cached
value, cache unchanged. -/
private theorem randomOracle_run_some
    (d : D) (qc : (D →ₒ R).QueryCache) (r : R) (hqc : qc d = some r) :
    ((D →ₒ R).randomOracle d).run qc = pure (r, qc) :=
  QueryImpl.withCaching_run_some _ hqc

/-- Running `roImpl` on a uniform-sampling query leaves the cache unchanged: the response is a
uniform `ProbComp` sample and the cache `c` passes through. -/
private theorem roImpl_run_inl (n : unifSpec.Domain) (c : (D →ₒ R).QueryCache) :
    (roImpl D R (Sum.inl n)).run c =
      (fun u => (u, c)) <$> (liftM (OracleSpec.query n) : ProbComp _) := by
  rw [roImpl, QueryImpl.add_apply_inl]
  unfold unifFwdImpl
  rw [QueryImpl.liftTarget_apply, HasQuery.toQueryImpl]
  simp [StateT.run_monadLift, bind_pure_comp, HasQuery.query]

/-- **Resampling marginal.** For any `p` and any cache `qc` that *misses* `d`, pre-sampling a fresh
uniform value at `d` (writing it into the cache) and then running `simulateQ (roImpl D R) p` has
the same output distribution as running `simulateQ (roImpl D R) p` from `qc` directly.

Induction over `p`. On a uniform-sampling query the cache is untouched, so the IH applies on the
continuation directly. On a `D →ₒ R` query at `t`: if `t = d`, the pre-sampled side hits the cache
(deterministic) while the bare side misses and samples fresh — the two uniform samples are renamed
into each other. If `t ≠ d`, the `d`-entry is untouched and the continuation cache still misses
`d`, so the IH applies after commuting the two independent samples. -/
private theorem evalDist_uniformSample_bind_simulateQ_roImpl_run'
    {β : Type} (d : D) :
    ∀ (p : OracleComp (unifSpec + (D →ₒ R)) β) (qc : (D →ₒ R).QueryCache), qc d = none →
      𝒟[($ᵗ R) >>= fun r => (simulateQ (roImpl D R) p).run' (qc.cacheQuery d r)] =
        𝒟[(simulateQ (roImpl D R) p).run' qc] := by
  intro p
  induction p using OracleComp.inductionOn with
  | pure x =>
    intro qc _
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
    -- LHS: `($ᵗ R) >>= fun _ => pure x`; the constant marginal collapses.
    refine evalDist_ext fun y => ?_
    rw [probOutput_bind_const, probFailure_uniformSample]
    simp
  | query_bind t k ih =>
    intro qc hqc
    rcases t with n | t
    · -- Uniform-sampling query: cache untouched; IH applies on the continuation directly.
      have hredU : ∀ c : (D →ₒ R).QueryCache,
          (simulateQ (roImpl D R) (liftM ((unifSpec + (D →ₒ R)).query (Sum.inl n)) >>= k)).run' c =
            (liftM (OracleSpec.query (spec := unifSpec) n) :
                ProbComp ((unifSpec + (D →ₒ R)).Range (Sum.inl n))) >>= fun u =>
              (simulateQ (roImpl D R) (k u)).run' c := by
        intro c
        rw [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, roImpl_run_inl]
        simp [map_eq_bind_pure_comp, bind_assoc, StateT.run'_eq]
      simp only [hredU]
      -- Both sides: `query n` then continue. Commute the `d`-presample past the unif sample, apply
      -- the IH on each continuation (cache still misses `d`).
      rw [evalDist_bind_bind_swap ($ᵗ R)
        (liftM (OracleSpec.query (spec := unifSpec) n) :
          ProbComp ((unifSpec + (D →ₒ R)).Range (Sum.inl n)))
        (fun r u => (simulateQ (roImpl D R) (k u)).run' (qc.cacheQuery d r))]
      refine evalDist_ext fun x => ?_
      simp only [probOutput_bind_eq_tsum]
      refine tsum_congr fun u => ?_
      rw [← probOutput_bind_eq_tsum]
      exact congrArg
        (Pr[= u | (liftM (OracleSpec.query (spec := unifSpec) n) :
            ProbComp ((unifSpec + (D →ₒ R)).Range (Sum.inl n)))] * ·)
        (congrFun (congrArg DFunLike.coe (ih u qc hqc)) x)
    · -- `D →ₒ R` query at `t`. Reduce both runs to `randomOracle t` then continue.
      have hred : ∀ c : (D →ₒ R).QueryCache,
          (simulateQ (roImpl D R) (liftM ((unifSpec + (D →ₒ R)).query (Sum.inr t)) >>= k)).run' c =
            ((D →ₒ R).randomOracle t).run c >>= fun z =>
              (simulateQ (roImpl D R) (k z.1)).run' z.2 := by
        intro c
        simp only [roImpl, simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inr,
          StateT.run'_eq, StateT.run_bind, map_bind]
        rfl
      by_cases htd : t = d
      · -- `t = d`: pre-sampled side hits, bare side misses and samples fresh.
        subst htd
        simp only [hred]
        have hL : (($ᵗ R) >>= fun r =>
              ((D →ₒ R).randomOracle t).run (qc.cacheQuery t r) >>= fun z =>
                (simulateQ (roImpl D R) (k z.1)).run' z.2) =
            (($ᵗ R) >>= fun r =>
              (simulateQ (roImpl D R) (k r)).run' (qc.cacheQuery t r)) := by
          refine bind_congr fun r => ?_
          rw [randomOracle_run_some t (qc.cacheQuery t r) r (QueryCache.cacheQuery_self qc t r),
            pure_bind]
        have hR : (((D →ₒ R).randomOracle t).run qc >>= fun z =>
              (simulateQ (roImpl D R) (k z.1)).run' z.2) =
            (($ᵗ R) >>= fun r =>
              (simulateQ (roImpl D R) (k r)).run' (qc.cacheQuery t r)) := by
          rw [randomOracle_run_none t qc hqc]
          simp only [Function.comp_def, map_eq_bind_pure_comp,
            bind_assoc, pure_bind]
        rw [hL, hR]
      · -- `t ≠ d`: the `d`-entry is invisible to `query t`; continuation cache still misses `d`.
        simp only [hred]
        by_cases hqt : ∃ v, qc t = some v
        · obtain ⟨v, hv⟩ := hqt
          have hpres : ∀ r : R, (qc.cacheQuery d r) t = some v := by
            intro r; rw [QueryCache.cacheQuery_of_ne qc r htd, hv]
          rw [randomOracle_run_some t qc v hv, pure_bind]
          have hL : (($ᵗ R) >>= fun r =>
                ((D →ₒ R).randomOracle t).run (qc.cacheQuery d r) >>= fun z =>
                  (simulateQ (roImpl D R) (k z.1)).run' z.2) =
              (($ᵗ R) >>= fun r =>
                (simulateQ (roImpl D R) (k v)).run' (qc.cacheQuery d r)) := by
            refine bind_congr fun r => ?_
            rw [randomOracle_run_some t (qc.cacheQuery d r) v (hpres r), pure_bind]
          rw [hL]
          exact ih v qc hqc
        · push Not at hqt
          have hqtn : qc t = none := by cases h : qc t with
            | none => rfl
            | some v => exact absurd h (by simpa using hqt v)
          rw [randomOracle_run_none t qc hqtn]
          have hRHS : (((fun w => (w, qc.cacheQuery t w)) <$> ($ᵗ R)) >>= fun z =>
                (simulateQ (roImpl D R) (k z.1)).run' z.2) =
              (($ᵗ R) >>= fun w =>
                (simulateQ (roImpl D R) (k w)).run' (qc.cacheQuery t w)) := by
            rw [map_eq_bind_pure_comp]; simp [bind_assoc]
          rw [hRHS]
          have hmiss_t : ∀ r : R, (qc.cacheQuery d r) t = none := by
            intro r; rw [QueryCache.cacheQuery_of_ne qc r htd, hqtn]
          have hL : (($ᵗ R) >>= fun r =>
                ((D →ₒ R).randomOracle t).run (qc.cacheQuery d r) >>= fun z =>
                  (simulateQ (roImpl D R) (k z.1)).run' z.2) =
              (($ᵗ R) >>= fun r => ($ᵗ R) >>= fun w =>
                (simulateQ (roImpl D R) (k w)).run'
                  ((qc.cacheQuery d r).cacheQuery t w)) := by
            refine bind_congr fun r => ?_
            rw [randomOracle_run_none t (qc.cacheQuery d r) (hmiss_t r), map_eq_bind_pure_comp]
            simp [bind_assoc]
          rw [hL]
          rw [evalDist_bind_bind_swap ($ᵗ R) ($ᵗ R)
            (fun r w => (simulateQ (roImpl D R) (k w)).run'
              ((qc.cacheQuery d r).cacheQuery t w))]
          refine evalDist_ext fun x => ?_
          simp only [probOutput_bind_eq_tsum]
          refine tsum_congr fun w => ?_
          have hcomm : ∀ r : R, (qc.cacheQuery d r).cacheQuery t w =
              (qc.cacheQuery t w).cacheQuery d r := by
            intro r
            simp only [QueryCache.cacheQuery]
            exact (Function.update_comm htd w r qc).symm
          have hmiss_d : (qc.cacheQuery t w) d = none := by
            rw [QueryCache.cacheQuery_of_ne qc w (fun h => htd h.symm)]; exact hqc
          simp only [hcomm]
          rw [← probOutput_bind_eq_tsum]
          exact congrArg (Pr[= w | $ᵗ R] * ·)
            (congrFun (congrArg DFunLike.coe (ih w (qc.cacheQuery t w) hmiss_d)) x)

/-- **The true absorption lemma.** Prepending a result-discarded random-oracle query at `d` to a
computation `p` over `D →ₒ R` preserves the output distribution under `simulateQ randomOracle`.

This replaces the (false-for-arbitrary-tail) bare-cache "brick 2": the statement is true here
because `p` is an `OracleComp (unifSpec + (D →ₒ R))` — it can access the cache *only through* the
random oracle, never via a raw `get`. -/
theorem evalDist_simulateQ_roImpl_discard_run' {β : Type}
    (d : D) (p : OracleComp (unifSpec + (D →ₒ R)) β) (qc : (D →ₒ R).QueryCache) :
    𝒟[(simulateQ (roImpl D R)
        ((unifSpec + (D →ₒ R)).query (Sum.inr d) >>= fun _ => p)).run' qc] =
      𝒟[(simulateQ (roImpl D R) p).run' qc] := by
  -- Reduce the prepended query to `randomOracle d` then continue.
  have hred :
      (simulateQ (roImpl D R) ((unifSpec + (D →ₒ R)).query (Sum.inr d) >>= fun _ => p)).run' qc =
        ((D →ₒ R).randomOracle d).run qc >>= fun z =>
          (simulateQ (roImpl D R) p).run' z.2 := by
    simp only [roImpl, simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inr,
      StateT.run'_eq, StateT.run_bind, map_bind]
    rfl
  rw [hred]
  by_cases hqc : ∃ r, qc d = some r
  · -- Cache hit: the discarded query is deterministic, cache unchanged.
    obtain ⟨r, hr⟩ := hqc
    rw [randomOracle_run_some d qc r hr, pure_bind]
  · -- Cache miss: sample fresh `r`, cache at `d`, then run `p`; apply the resampling marginal.
    push Not at hqc
    have hqcn : qc d = none := by cases h : qc d with
      | none => rfl
      | some v => exact absurd h (by simpa using hqc v)
    rw [randomOracle_run_none d qc hqcn]
    have hL :
        𝒟[((fun r => (r, qc.cacheQuery d r)) <$> ($ᵗ R)) >>= fun z =>
            (simulateQ (roImpl D R) p).run' z.2] =
          𝒟[($ᵗ R) >>= fun r =>
            (simulateQ (roImpl D R) p).run' (qc.cacheQuery d r)] := by
      rw [map_eq_bind_pure_comp]; simp [bind_assoc]
    rw [hL]
    exact evalDist_uniformSample_bind_simulateQ_roImpl_run' d p qc hqcn

/-! ## The `RespectsRO` predicate -/

/-- An interpreter `impl : QueryImpl spec (StateT (σ × (D →ₒ R).QueryCache) ProbComp)` *respects the
random oracle* when its access to the `(D →ₒ R).QueryCache` component is *only via* the random
oracle: there is a body `B t s : OracleComp (unifSpec + (D →ₒ R)) (Range t × σ)` computing the
response and next `σ`-state as an `OracleComp` whose only oracles are uniform sampling and the
random oracle, such that running `impl t` on `(s, qc)` equals running `simulateQ (roImpl D R)
(B t s)` on `qc`, reshaping `((Range × σ) × QueryCache)` into `(Range × (σ × QueryCache))`.

Because the body's only cache access is the random oracle (resample-on-miss, hit-consistent),
it can never inspect the cache raw — exactly the condition under which a discarded RO query is
distributionally invisible. Uniform sampling (`unifSpec`) leaves the cache untouched. -/
def RespectsRO (impl : QueryImpl spec (StateT (σ × (D →ₒ R).QueryCache) ProbComp)) : Prop :=
  ∃ B : (t : spec.Domain) → σ → OracleComp (unifSpec + (D →ₒ R)) (spec.Range t × σ),
    ∀ (t : spec.Domain) (s : σ) (qc : (D →ₒ R).QueryCache),
      (impl t).run (s, qc) =
        (fun z : (spec.Range t × σ) × (D →ₒ R).QueryCache => (z.1.1, (z.1.2, z.2))) <$>
          (simulateQ (roImpl D R) (B t s)).run qc

/-! ## Compiling a `RespectsRO` simulation to the random oracle -/

/-- A `RespectsRO` body `B`, bundled as a `StateT σ (OracleComp (unifSpec + (D →ₒ R)))` query
implementation: each query computes its response and the next `σ`-state via `B t s`. -/
def bodyImpl (B : (t : spec.Domain) → σ → OracleComp (unifSpec + (D →ₒ R)) (spec.Range t × σ)) :
    QueryImpl spec (StateT σ (OracleComp (unifSpec + (D →ₒ R)))) :=
  fun t => StateT.mk fun s => B t s

/-- Inline a `RespectsRO` body `B` along an adversary `adv`, threading the `σ`-state as a *return
value*: a single `OracleComp (unifSpec + (D →ₒ R)) (α × σ)`. The `simulateQ impl₁` run over the
product state `(σ × cache)` then equals `simulateQ (roImpl D R)` of this compiled computation
(`run_simulateQ_eq_compile`). -/
def compile (B : (t : spec.Domain) → σ → OracleComp (unifSpec + (D →ₒ R)) (spec.Range t × σ))
    (adv : OracleComp spec α) (s : σ) : OracleComp (unifSpec + (D →ₒ R)) (α × σ) :=
  (simulateQ (bodyImpl B) adv).run s

omit [DecidableEq D] [SampleableType R] in
@[simp] lemma compile_pure
    (B : (t : spec.Domain) → σ → OracleComp (unifSpec + (D →ₒ R)) (spec.Range t × σ))
    (x : α) (s : σ) : compile (α := α) B (pure x) s = pure (x, s) := by
  simp [compile]

omit [DecidableEq D] [SampleableType R] in
lemma compile_query_bind
    (B : (t : spec.Domain) → σ → OracleComp (unifSpec + (D →ₒ R)) (spec.Range t × σ))
    (t : spec.Domain) (k : spec.Range t → OracleComp spec α) (s : σ) :
    compile (α := α) B (liftM (spec.query t) >>= k) s =
      B t s >>= fun z => compile B (k z.1) z.2 := by
  simp only [compile, bodyImpl, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    StateT.run_mk]

/-- **Bridge.** If `impl₁` `RespectsRO` with body `B`, then `simulateQ impl₁ adv` over the product
state `(σ × cache)` equals `simulateQ randomOracle (compile B adv s)` over the cache, with the
returned `σ`-state reshaped back into the product. -/
private theorem run_simulateQ_eq_compile
    (impl₁ : QueryImpl spec (StateT (σ × (D →ₒ R).QueryCache) ProbComp))
    (B : (t : spec.Domain) → σ → OracleComp (unifSpec + (D →ₒ R)) (spec.Range t × σ))
    (hB : ∀ (t : spec.Domain) (s : σ) (qc : (D →ₒ R).QueryCache),
      (impl₁ t).run (s, qc) =
        (fun z : (spec.Range t × σ) × (D →ₒ R).QueryCache => (z.1.1, (z.1.2, z.2))) <$>
          (simulateQ (roImpl D R) (B t s)).run qc)
    (adv : OracleComp spec α) (s : σ) (qc : (D →ₒ R).QueryCache) :
    (simulateQ impl₁ adv).run (s, qc) =
      (fun z : (α × σ) × (D →ₒ R).QueryCache => (z.1.1, (z.1.2, z.2))) <$>
        (simulateQ (roImpl D R) (compile B adv s)).run qc := by
  induction adv using OracleComp.inductionOn generalizing s qc with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, compile_pure, map_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [hB t s, compile_query_bind]
    simp only [simulateQ_bind, StateT.run_bind, map_bind, bind_map_left]
    refine bind_congr fun z => ?_
    exact ih z.1.1 z.1.2 z.2

/-- `run'` corollary of `run_simulateQ_eq_compile`: the output distribution of the product-state
simulation is the `Prod.fst`-marginal of the random-oracle simulation of the compiled computation,
which is itself `simulateQ randomOracle` of `Prod.fst <$> compile B adv s`. -/
private theorem run'_simulateQ_eq_compile
    (impl₁ : QueryImpl spec (StateT (σ × (D →ₒ R).QueryCache) ProbComp))
    (B : (t : spec.Domain) → σ → OracleComp (unifSpec + (D →ₒ R)) (spec.Range t × σ))
    (hB : ∀ (t : spec.Domain) (s : σ) (qc : (D →ₒ R).QueryCache),
      (impl₁ t).run (s, qc) =
        (fun z : (spec.Range t × σ) × (D →ₒ R).QueryCache => (z.1.1, (z.1.2, z.2))) <$>
          (simulateQ (roImpl D R) (B t s)).run qc)
    (adv : OracleComp spec α) (s : σ) (qc : (D →ₒ R).QueryCache) :
    (simulateQ impl₁ adv).run' (s, qc) =
      (simulateQ (roImpl D R) (Prod.fst <$> compile B adv s)).run' qc := by
  rw [StateT.run'_eq, run_simulateQ_eq_compile impl₁ B hB adv s qc, simulateQ_map,
    StateT.run'_eq, StateT.run_map, Functor.map_map, Functor.map_map]

/-! ## Discarded random-oracle query removal under `simulateQ` -/

/-- **Discarded random-oracle query removal under `simulateQ`.**

Let `impl₁`, `impl₂` be two interpreters of the adversary spec `spec` into
`StateT (σ × (D →ₒ R).QueryCache) ProbComp` whose state carries a lazy random-oracle cache for
`D →ₒ R` as its second component. Suppose `impl₁` `RespectsRO` (accesses the cache only via
`randomOracle`), and that on every query `t` from every state `(s, qc)`, either

* `impl₂` agrees with `impl₁`: `(impl₂ t).run (s, qc) = (impl₁ t).run (s, qc)`; or
* `impl₂` is `impl₁` *preceded by a result-discarded random-oracle query* at some point `d`:
  `(impl₂ t).run (s, qc) =
     ((D →ₒ R).randomOracle d).run qc >>= fun p => (impl₁ t).run (s, p.2)`.

Then the two interpreters produce the same output distribution: the discarded samples are never
observed (because `impl₁` reads the cache only through the random oracle), so even though they
perturb the cache state, the *output marginal* is unchanged.

The `RespectsRO` hypothesis is essential — without it, the statement is false: an interpreter that
reads the cache raw could detect the discarded sample. -/
theorem evalDist_simulateQ_run'_discardRO
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × (D →ₒ R).QueryCache) ProbComp))
    (h₁ : RespectsRO (D := D) (R := R) impl₁)
    (hstep : ∀ (t : spec.Domain) (s : σ) (qc : (D →ₒ R).QueryCache),
      (impl₂ t).run (s, qc) = (impl₁ t).run (s, qc) ∨
      ∃ d : D, (impl₂ t).run (s, qc) =
        ((D →ₒ R).randomOracle d).run qc >>= fun p => (impl₁ t).run (s, p.2))
    (adv : OracleComp spec α) (s₀ : σ) (qc₀ : (D →ₒ R).QueryCache) :
    𝒟[(simulateQ impl₂ adv).run' (s₀, qc₀)] =
      𝒟[(simulateQ impl₁ adv).run' (s₀, qc₀)] := by
  obtain ⟨B, hB⟩ := h₁
  -- `simulateQ` induction over `adv`, generalizing the whole product state `(s₀, qc₀)`.
  induction adv using OracleComp.inductionOn generalizing s₀ qc₀ with
  | pure x => rfl
  | query_bind t k ih =>
    rcases hstep t s₀ qc₀ with hmatch | ⟨d, hdisc⟩
    · -- Handlers agree on this query; recurse on the tail from every reachable state.
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind]
      rw [evalDist_map, evalDist_map, hmatch, evalDist_bind, evalDist_bind, map_bind, map_bind]
      refine bind_congr fun p => ?_
      have := ih p.1 p.2.1 p.2.2
      simpa only [StateT.run'_eq, evalDist_map] using this
    · -- `impl₂` prepends a discarded RO query; rewrite the tail by IH, then drop the discard.
      classical
      -- Abbreviate the per-step adversary and the compiled RO computation of its `impl₁`-tail.
      set adv' : OracleComp spec α := liftM (spec.query t) >>= k with hadv'
      set P : OracleComp (unifSpec + (D →ₒ R)) α := Prod.fst <$> compile B adv' s₀ with hP
      -- Both `(simulateQ implᵢ adv').run'` equal `simulateQ (roImpl D R) P` over the cache via the
      -- compile bridge (for impl₁) resp. the same bridge prefixed by a discarded query (impl₂).
      have hbridge : ∀ c : (D →ₒ R).QueryCache,
          (simulateQ impl₁ adv').run' (s₀, c) =
            (simulateQ (roImpl D R) P).run' c := by
        intro c; rw [hP]; exact run'_simulateQ_eq_compile impl₁ B hB adv' s₀ c
      -- Step 1: the `impl₁` side is `simulateQ (roImpl D R) P`.
      have key1 :
          𝒟[(simulateQ impl₁ adv').run' (s₀, qc₀)] =
            𝒟[(simulateQ (roImpl D R) P).run' qc₀] := by
        rw [hbridge]
      -- Step 2: the `impl₂` side is the discarded query prepended to that (`𝒟`-level).
      have key2 :
          𝒟[(simulateQ impl₂ adv').run' (s₀, qc₀)] =
            𝒟[(simulateQ (roImpl D R)
                ((unifSpec + (D →ₒ R)).query (Sum.inr d) >>= fun _ => P :
                  OracleComp (unifSpec + (D →ₒ R)) α)).run' qc₀] := by
        -- Reduce the prepended-query side to `𝒟[randomOracle d] >>= fun r => 𝒟[run' P at r.2]`.
        have hfoldc :
            (simulateQ (roImpl D R)
                ((unifSpec + (D →ₒ R)).query (Sum.inr d) >>= fun _ => P :
                  OracleComp (unifSpec + (D →ₒ R)) α)).run' qc₀ =
              ((D →ₒ R).randomOracle d).run qc₀ >>= fun r =>
                (simulateQ (roImpl D R) P).run' r.2 := by
          rw [roImpl]
          simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inr,
            StateT.run'_eq, StateT.run_bind, map_bind]
          rfl
        have hfold :
            𝒟[(simulateQ (roImpl D R)
                ((unifSpec + (D →ₒ R)).query (Sum.inr d) >>= fun _ => P :
                  OracleComp (unifSpec + (D →ₒ R)) α)).run' qc₀] =
              𝒟[((D →ₒ R).randomOracle d).run qc₀] >>= fun r =>
                𝒟[(simulateQ (roImpl D R) P).run' r.2] := by
          rw [hfoldc, evalDist_bind]
        rw [hfold]
        -- LHS: reduce `simulateQ impl₂ adv'` and apply `hdisc` to the head query.
        conv_lhs => rw [hadv']
        rw [show (simulateQ impl₂ (liftM (spec.query t) >>= k)).run' (s₀, qc₀) =
              Prod.fst <$> ((impl₂ t).run (s₀, qc₀) >>= fun z =>
                (simulateQ impl₂ (k z.1)).run z.2) from by
            simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind]]
        rw [evalDist_map, hdisc, bind_assoc, evalDist_bind, map_bind]
        refine bind_congr fun r => ?_
        -- Goal: `Prod.fst <$> 𝒟[impl₁ t then impl₂-tail] = 𝒟[(simulateQ randomOracle P).run' r.2]`.
        -- Push `Prod.fst` in, rewrite the impl₂-tail to impl₁ by IH, fold to `simulateQ impl₁`,
        -- then bridge to `P`.
        rw [← evalDist_map, map_bind]
        have hIH :
            𝒟[(impl₁ t).run (s₀, r.2) >>= fun z =>
                Prod.fst <$> (simulateQ impl₂ (k z.1)).run z.2] =
              𝒟[(impl₁ t).run (s₀, r.2) >>= fun z =>
                Prod.fst <$> (simulateQ impl₁ (k z.1)).run z.2] := by
          rw [evalDist_bind, evalDist_bind]
          refine bind_congr fun z => ?_
          have hih := ih z.1 z.2.1 z.2.2
          rw [StateT.run'_eq, StateT.run'_eq, evalDist_map, evalDist_map] at hih
          rw [evalDist_map, evalDist_map]
          simpa using hih
        rw [hIH]
        have hfold₁ :
            𝒟[(impl₁ t).run (s₀, r.2) >>= fun z =>
                Prod.fst <$> (simulateQ impl₁ (k z.1)).run z.2] =
              𝒟[(simulateQ impl₁ adv').run' (s₀, r.2)] := by
          rw [hadv']
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind,
            map_bind]
        rw [hfold₁, hbridge]
      rw [key1, key2, evalDist_simulateQ_roImpl_discard_run' d P qc₀]

end OracleComp
