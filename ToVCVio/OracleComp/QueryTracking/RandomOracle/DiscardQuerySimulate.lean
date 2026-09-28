/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.CryptoFoundations.PRF
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.OracleComp.SimSemantics.StateT.Basic
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.OracleComp.SimSemantics.Append

/-!
# Discarded random-oracle query removal under `simulateQ`

Let `p : OracleComp (unifSpec + (D →ₒ R)) β`, run against the lazy random oracle
`PRFScheme.prfIdealQueryImpl`. Prepending a query at `d` and discarding its result
does not change the output distribution:

```
𝒟[(simulateQ prfIdealQueryImpl (query d >>= fun _ => p)).run' qc]
  = 𝒟[(simulateQ prfIdealQueryImpl p).run' qc].
```

For a query implementation with state `σ × (D →ₒ R).QueryCache`,
`RespectsRO impl` states that each handler factors through an oracle computation
simulated by `prfIdealQueryImpl`. The theorem `evalDist_simulateQ_run'_discardRO` lifts
discarded-query removal to such query implementations.
-/

open OracleComp OracleSpec ENNReal
open PRFScheme (prfIdealQueryImpl prfIdealQueryImpl_apply_inr)

namespace OracleComp

variable {D R : Type} [DecidableEq D] [SampleableType R]
  {ι : Type} {spec : OracleSpec ι} {σ α : Type}

/-! ## Discarded-query absorption -/

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

/-- Running `prfIdealQueryImpl` on a uniform-sampling query leaves the cache unchanged: the
response is a uniform `ProbComp` sample and the cache `c` passes through. -/
private theorem prfIdealQueryImpl_run_inl (n : unifSpec.Domain) (c : (D →ₒ R).QueryCache) :
    (prfIdealQueryImpl (D := D) (R := R) (Sum.inl n)).run c =
      (fun u => (u, c)) <$> (liftM (OracleSpec.query n) : ProbComp _) := by
  rw [prfIdealQueryImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
    HasQuery.toQueryImpl]
  simp [StateT.run_monadLift, bind_pure_comp, HasQuery.query]

/-- **Resampling marginal.** For any `p` and any cache `qc` that *misses* `d`, pre-sampling a fresh
uniform value at `d` (writing it into the cache) and then running `simulateQ prfIdealQueryImpl p`
has the same output distribution as running `simulateQ prfIdealQueryImpl p` from `qc` directly.

Induction over `p`. On a uniform-sampling query the cache is untouched, so the IH applies on the
continuation directly. On a `D →ₒ R` query at `t`: if `t = d`, the pre-sampled side hits the cache
(deterministic) while the bare side misses and samples fresh — the two uniform samples are renamed
into each other. If `t ≠ d`, the `d`-entry is untouched and the continuation cache still misses
`d`, so the IH applies after commuting the two independent samples. -/
theorem evalDist_uniformSample_bind_simulateQ_prfIdealQueryImpl_run'
    {β : Type} (d : D) :
    ∀ (p : OracleComp (unifSpec + (D →ₒ R)) β) (qc : (D →ₒ R).QueryCache), qc d = none →
      𝒟[($ᵗ R) >>= fun r => (simulateQ prfIdealQueryImpl p).run' (qc.cacheQuery d r)] =
        𝒟[(simulateQ prfIdealQueryImpl p).run' qc] := by
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
          (simulateQ prfIdealQueryImpl
              (liftM ((unifSpec + (D →ₒ R)).query (Sum.inl n)) >>= k)).run' c =
            (liftM (OracleSpec.query (spec := unifSpec) n) :
                ProbComp ((unifSpec + (D →ₒ R)).Range (Sum.inl n))) >>= fun u =>
              (simulateQ prfIdealQueryImpl (k u)).run' c := by
        intro c
        rw [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind,
          prfIdealQueryImpl_run_inl]
        simp [map_eq_bind_pure_comp, bind_assoc, StateT.run'_eq]
      simp only [hredU]
      -- Both sides: `query n` then continue. Commute the `d`-presample past the unif sample, apply
      -- the IH on each continuation (cache still misses `d`).
      rw [evalDist_bind_bind_swap ($ᵗ R)
        (liftM (OracleSpec.query (spec := unifSpec) n) :
          ProbComp ((unifSpec + (D →ₒ R)).Range (Sum.inl n)))
        (fun r u => (simulateQ prfIdealQueryImpl (k u)).run' (qc.cacheQuery d r))]
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
          (simulateQ prfIdealQueryImpl
              (liftM ((unifSpec + (D →ₒ R)).query (Sum.inr t)) >>= k)).run' c =
            ((D →ₒ R).randomOracle t).run c >>= fun z =>
              (simulateQ prfIdealQueryImpl (k z.1)).run' z.2 := by
        intro c
        simp only [simulateQ_bind, simulateQ_spec_query, prfIdealQueryImpl_apply_inr,
          StateT.run'_eq, StateT.run_bind, map_bind]
        rfl
      by_cases htd : t = d
      · -- `t = d`: pre-sampled side hits, bare side misses and samples fresh.
        subst htd
        simp only [hred]
        have hL : (($ᵗ R) >>= fun r =>
              ((D →ₒ R).randomOracle t).run (qc.cacheQuery t r) >>= fun z =>
                (simulateQ prfIdealQueryImpl (k z.1)).run' z.2) =
            (($ᵗ R) >>= fun r =>
              (simulateQ prfIdealQueryImpl (k r)).run' (qc.cacheQuery t r)) := by
          refine bind_congr fun r => ?_
          rw [randomOracle_run_some t (qc.cacheQuery t r) r (QueryCache.cacheQuery_self qc t r),
            pure_bind]
        have hR : (((D →ₒ R).randomOracle t).run qc >>= fun z =>
              (simulateQ prfIdealQueryImpl (k z.1)).run' z.2) =
            (($ᵗ R) >>= fun r =>
              (simulateQ prfIdealQueryImpl (k r)).run' (qc.cacheQuery t r)) := by
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
                  (simulateQ prfIdealQueryImpl (k z.1)).run' z.2) =
              (($ᵗ R) >>= fun r =>
                (simulateQ prfIdealQueryImpl (k v)).run' (qc.cacheQuery d r)) := by
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
                (simulateQ prfIdealQueryImpl (k z.1)).run' z.2) =
              (($ᵗ R) >>= fun w =>
                (simulateQ prfIdealQueryImpl (k w)).run' (qc.cacheQuery t w)) := by
            rw [map_eq_bind_pure_comp]; simp [bind_assoc]
          rw [hRHS]
          have hmiss_t : ∀ r : R, (qc.cacheQuery d r) t = none := by
            intro r; rw [QueryCache.cacheQuery_of_ne qc r htd, hqtn]
          have hL : (($ᵗ R) >>= fun r =>
                ((D →ₒ R).randomOracle t).run (qc.cacheQuery d r) >>= fun z =>
                  (simulateQ prfIdealQueryImpl (k z.1)).run' z.2) =
              (($ᵗ R) >>= fun r => ($ᵗ R) >>= fun w =>
                (simulateQ prfIdealQueryImpl (k w)).run'
                  ((qc.cacheQuery d r).cacheQuery t w)) := by
            refine bind_congr fun r => ?_
            rw [randomOracle_run_none t (qc.cacheQuery d r) (hmiss_t r), map_eq_bind_pure_comp]
            simp [bind_assoc]
          rw [hL]
          rw [evalDist_bind_bind_swap ($ᵗ R) ($ᵗ R)
            (fun r w => (simulateQ prfIdealQueryImpl (k w)).run'
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

/-- Prepending a query at `d` and discarding its result preserves the output
distribution of a computation interpreted by `PRFScheme.prfIdealQueryImpl`. -/
theorem evalDist_simulateQ_prfIdealQueryImpl_discard_run' {β : Type}
    (d : D) (p : OracleComp (unifSpec + (D →ₒ R)) β) (qc : (D →ₒ R).QueryCache) :
    𝒟[(simulateQ (prfIdealQueryImpl (D := D) (R := R))
        ((unifSpec + (D →ₒ R)).query (Sum.inr d) >>= fun _ => p)).run' qc] =
      𝒟[(simulateQ prfIdealQueryImpl p).run' qc] := by
  -- Reduce the prepended query to `randomOracle d` then continue.
  have hred :
      (simulateQ (prfIdealQueryImpl (D := D) (R := R))
          ((unifSpec + (D →ₒ R)).query (Sum.inr d) >>= fun _ => p)).run' qc =
        ((D →ₒ R).randomOracle d).run qc >>= fun z =>
          (simulateQ prfIdealQueryImpl p).run' z.2 := by
    simp only [simulateQ_bind, simulateQ_spec_query, prfIdealQueryImpl_apply_inr,
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
            (simulateQ prfIdealQueryImpl p).run' z.2] =
          𝒟[($ᵗ R) >>= fun r =>
            (simulateQ prfIdealQueryImpl p).run' (qc.cacheQuery d r)] := by
      rw [map_eq_bind_pure_comp]; simp [bind_assoc]
    rw [hL]
    exact evalDist_uniformSample_bind_simulateQ_prfIdealQueryImpl_run' d p qc hqcn

/-! ## The `RespectsRO` predicate -/

/-- `RespectsRO impl` holds when each handler of `impl` is represented by a
computation over `unifSpec + (D →ₒ R)` interpreted by `prfIdealQueryImpl`. The representation
threads the auxiliary state `σ` as output data and leaves cache access to `prfIdealQueryImpl`. -/
def RespectsRO (impl : QueryImpl spec (StateT (σ × (D →ₒ R).QueryCache) ProbComp)) : Prop :=
  ∃ B : (t : spec.Domain) → σ → OracleComp (unifSpec + (D →ₒ R)) (spec.Range t × σ),
    ∀ (t : spec.Domain) (s : σ) (qc : (D →ₒ R).QueryCache),
      (impl t).run (s, qc) =
        (fun z : (spec.Range t × σ) × (D →ₒ R).QueryCache => (z.1.1, (z.1.2, z.2))) <$>
          (simulateQ prfIdealQueryImpl (B t s)).run qc

/-! ## Compiling a `RespectsRO` simulation to the random oracle -/

/-- A `RespectsRO` body `B`, bundled as a `StateT σ (OracleComp (unifSpec + (D →ₒ R)))` query
implementation: each query computes its response and the next `σ`-state via `B t s`. -/
def bodyImpl (B : (t : spec.Domain) → σ → OracleComp (unifSpec + (D →ₒ R)) (spec.Range t × σ)) :
    QueryImpl spec (StateT σ (OracleComp (unifSpec + (D →ₒ R)))) :=
  fun t => StateT.mk fun s => B t s

/-- Inline a `RespectsRO` body `B` along an adversary `adv`, threading the `σ`-state as a *return
value*: a single `OracleComp (unifSpec + (D →ₒ R)) (α × σ)`. The `simulateQ impl₁` run over the
product state `(σ × cache)` then equals `simulateQ prfIdealQueryImpl` of this compiled computation
(`run_simulateQ_eq_compile`). -/
def compile (B : (t : spec.Domain) → σ → OracleComp (unifSpec + (D →ₒ R)) (spec.Range t × σ))
    (adv : OracleComp spec α) (s : σ) : OracleComp (unifSpec + (D →ₒ R)) (α × σ) :=
  (simulateQ (bodyImpl B) adv).run s

omit [DecidableEq D] [SampleableType R] in
/-- `compile` on `pure`. -/
@[simp] private lemma compile_pure
    (B : (t : spec.Domain) → σ → OracleComp (unifSpec + (D →ₒ R)) (spec.Range t × σ))
    (x : α) (s : σ) : compile (α := α) B (pure x) s = pure (x, s) := by
  simp [compile]

omit [DecidableEq D] [SampleableType R] in
/-- `compile` on a `query >>= k`. -/
private lemma compile_query_bind
    (B : (t : spec.Domain) → σ → OracleComp (unifSpec + (D →ₒ R)) (spec.Range t × σ))
    (t : spec.Domain) (k : spec.Range t → OracleComp spec α) (s : σ) :
    compile (α := α) B (liftM (spec.query t) >>= k) s =
      B t s >>= fun z => compile B (k z.1) z.2 := by
  simp only [compile, bodyImpl, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    StateT.run_mk]

/-- **Bridge.** Let `pack s qc : S` store the auxiliary state `s` and the random-oracle cache `qc`
in the handler state. If every handler of `impl₁` runs as the body `B` simulated by
`prfIdealQueryImpl`, repacked, then so does the whole simulation of `adv`, with body
`compile B adv`. `RespectsRO` is the case `pack := Prod.mk`. -/
theorem run_simulateQ_eq_compile {S : Type} (pack : σ → (D →ₒ R).QueryCache → S)
    (impl₁ : QueryImpl spec (StateT S ProbComp))
    (B : (t : spec.Domain) → σ → OracleComp (unifSpec + (D →ₒ R)) (spec.Range t × σ))
    (hB : ∀ (t : spec.Domain) (s : σ) (qc : (D →ₒ R).QueryCache),
      (impl₁ t).run (pack s qc) =
        (fun z : (spec.Range t × σ) × (D →ₒ R).QueryCache => (z.1.1, pack z.1.2 z.2)) <$>
          (simulateQ prfIdealQueryImpl (B t s)).run qc)
    (adv : OracleComp spec α) (s : σ) (qc : (D →ₒ R).QueryCache) :
    (simulateQ impl₁ adv).run (pack s qc) =
      (fun z : (α × σ) × (D →ₒ R).QueryCache => (z.1.1, pack z.1.2 z.2)) <$>
        (simulateQ prfIdealQueryImpl (compile B adv s)).run qc := by
  induction adv using OracleComp.inductionOn generalizing s qc with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, compile_pure, map_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [hB t s, compile_query_bind]
    simp only [simulateQ_bind, StateT.run_bind, map_bind, bind_map_left]
    refine bind_congr fun z => ?_
    exact ih z.1.1 z.1.2 z.2

/-- `run'` corollary of `run_simulateQ_eq_compile`: the output distribution of the simulation
is that of `Prod.fst <$> compile B adv s` under `prfIdealQueryImpl`. -/
theorem run'_simulateQ_eq_compile {S : Type} (pack : σ → (D →ₒ R).QueryCache → S)
    (impl₁ : QueryImpl spec (StateT S ProbComp))
    (B : (t : spec.Domain) → σ → OracleComp (unifSpec + (D →ₒ R)) (spec.Range t × σ))
    (hB : ∀ (t : spec.Domain) (s : σ) (qc : (D →ₒ R).QueryCache),
      (impl₁ t).run (pack s qc) =
        (fun z : (spec.Range t × σ) × (D →ₒ R).QueryCache => (z.1.1, pack z.1.2 z.2)) <$>
          (simulateQ prfIdealQueryImpl (B t s)).run qc)
    (adv : OracleComp spec α) (s : σ) (qc : (D →ₒ R).QueryCache) :
    (simulateQ impl₁ adv).run' (pack s qc) =
      (simulateQ prfIdealQueryImpl (Prod.fst <$> compile B adv s)).run' qc := by
  rw [StateT.run'_eq, run_simulateQ_eq_compile pack impl₁ B hB adv s qc, simulateQ_map,
    StateT.run'_eq, StateT.run_map, Functor.map_map, Functor.map_map]

/-! ## Discarded random-oracle query removal under `simulateQ` -/

/-- Suppose `impl₁` satisfies `RespectsRO`. If each handler of `impl₂` either
equals the corresponding handler of `impl₁` or prepends one discarded
random-oracle query, then their simulated output distributions are equal. -/
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
      -- Both `(simulateQ implᵢ adv').run'` equal `simulateQ prfIdealQueryImpl P` over the cache via
      -- the compile bridge (for impl₁) resp. the same bridge prefixed by a discarded query (impl₂).
      have hbridge : ∀ c : (D →ₒ R).QueryCache,
          (simulateQ impl₁ adv').run' (s₀, c) =
            (simulateQ prfIdealQueryImpl P).run' c := by
        intro c; rw [hP]; exact run'_simulateQ_eq_compile Prod.mk impl₁ B hB adv' s₀ c
      -- Step 1: the `impl₁` side is `simulateQ prfIdealQueryImpl P`.
      have key1 :
          𝒟[(simulateQ impl₁ adv').run' (s₀, qc₀)] =
            𝒟[(simulateQ prfIdealQueryImpl P).run' qc₀] := by
        rw [hbridge]
      -- Step 2: the `impl₂` side is the discarded query prepended to that (`𝒟`-level).
      have key2 :
          𝒟[(simulateQ impl₂ adv').run' (s₀, qc₀)] =
            𝒟[(simulateQ prfIdealQueryImpl
                ((unifSpec + (D →ₒ R)).query (Sum.inr d) >>= fun _ => P :
                  OracleComp (unifSpec + (D →ₒ R)) α)).run' qc₀] := by
        -- Reduce the prepended-query side to `𝒟[randomOracle d] >>= fun r => 𝒟[run' P at r.2]`.
        have hfoldc :
            (simulateQ prfIdealQueryImpl
                ((unifSpec + (D →ₒ R)).query (Sum.inr d) >>= fun _ => P :
                  OracleComp (unifSpec + (D →ₒ R)) α)).run' qc₀ =
              ((D →ₒ R).randomOracle d).run qc₀ >>= fun r =>
                (simulateQ prfIdealQueryImpl P).run' r.2 := by
          simp only [simulateQ_bind, simulateQ_spec_query, prfIdealQueryImpl_apply_inr,
            StateT.run'_eq, StateT.run_bind, map_bind]
          rfl
        have hfold :
            𝒟[(simulateQ prfIdealQueryImpl
                ((unifSpec + (D →ₒ R)).query (Sum.inr d) >>= fun _ => P :
                  OracleComp (unifSpec + (D →ₒ R)) α)).run' qc₀] =
              𝒟[((D →ₒ R).randomOracle d).run qc₀] >>= fun r =>
                𝒟[(simulateQ prfIdealQueryImpl P).run' r.2] := by
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
      rw [key1, key2, evalDist_simulateQ_prfIdealQueryImpl_discard_run' d P qc₀]

end OracleComp
