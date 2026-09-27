/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.OracleComp.QueryTracking.LazySampling

/-!
# Sampling at a state-dependent first use

A sample from an arbitrary `ProbComp τ` can be drawn in advance or delayed
until the first oracle query whose input state satisfies `hit`. Before that
query, the implementation must be independent of the sample. Afterwards the
same cached value is reused. The joint-distribution theorem retains the
sample, adversary output, and final protocol state, so correlations between
components of a sampled record are preserved.
-/

open OracleComp OracleSpec ENNReal

namespace OracleComp.ProgramLogic.Relational

variable {ι : Type} {spec : OracleSpec ι} {σ α τ : Type}

/-- **Consume-site-lazy lift.** Samples `a ← sample` only at queries whose input state satisfies
`hit t s = true` (and caches the first such sample). At `hit t s = false`, uses
whatever is in the cache (or `default` if still empty) without observable
effect — under the hypothesis that `implFam` doesn't depend on `τ` at such
queries. -/
noncomputable def sampleOnDemand
    (sample : ProbComp τ)
    (implFam : τ → QueryImpl spec (StateT σ ProbComp))
    (hit : spec.Domain → σ → Bool) [Inhabited τ] :
    QueryImpl spec (StateT (σ × Option τ) ProbComp) :=
  -- per-query handler: answer query `t` from augmented state `(state, cache)`,
  -- returning the response and the updated augmented state
  fun t (state, cache) => do
    if hit t state then
      let a ← (match cache with
        | some a => (pure a : ProbComp τ)
        | none => sample)
      let (u, state') ← (implFam a t) state
      pure (u, (state', some a))
    else
      let a : τ := cache.getD default
      let (u, state') ← (implFam a t) state
      pure (u, (state', cache))

/-! ## Joint output-and-state consume-site commutation

The commutation is proved for the pair `(output, final state)` with the top-level sample
retained, `evalDist_simulateQ_sampleOnDemand_run_sample_eq`, and the `run'`-level statement
`probOutput_simulateQ_sampleOnDemand_run'_eq` is obtained from it by projection. Keeping the
state is what makes the statement inductive: the induction hypothesis is applied at the
post-query state. -/

/-- From a populated cache `some a`, `sampleOnDemand sample implFam hit` runs as
`implFam a` and never overwrites the cache. -/
theorem run_simulateQ_sampleOnDemand_some_eq
    (sample : ProbComp τ)
    (implFam : τ → QueryImpl spec (StateT σ ProbComp))
    (hit : spec.Domain → σ → Bool) [Inhabited τ]
    (oa : OracleComp spec α) (a : τ) (s : σ) :
    (simulateQ (sampleOnDemand sample implFam hit) oa).run (s, some a) =
      (fun p => (p.1, (p.2, some a))) <$> (simulateQ (implFam a) oa).run s := by
  -- One step from a populated cache behaves as `implFam a` and keeps the cache, whether or
  -- not `hit t`; `simulateQ_run_eq_of_snd_invariant` then fixes the cache along the whole run.
  have hg : ∀ (t : spec.Domain) (s : σ), (sampleOnDemand sample implFam hit t).run (s, some a) =
      (implFam a t).run s >>= fun p => (pure (p.1, p.2, some a) : ProbComp _) := by
    intro t s
    simp only [sampleOnDemand, StateT.run]
    split_ifs <;> simp [Option.getD]
  have hfix : QueryImpl.fixSndStateT (sampleOnDemand sample implFam hit) (some a) = implFam a := by
    funext t
    refine StateT.ext fun s => ?_
    simp [QueryImpl.fixSndStateT, hg, Prod.map]
  rw [simulateQ_run_eq_of_snd_invariant _ (some a) (fun t s x hx => ?_) oa s, hfix]
  rw [hg] at hx
  obtain ⟨p, -, hp⟩ := (mem_support_bind_iff _ _ _).mp hx
  rw [mem_support_pure_iff] at hp
  rw [hp]

/-- Let `oa : OracleComp spec α`, let `s : σ` be the starting state, and let `h_indep` say that
`implFam a` does not depend on `a` at queries `t` with `hit t s = false`. The eager run of `oa`
draws `a ← sample` up front and simulates `oa` with `implFam a` from `s`. The lazy run
simulates `oa` with `sampleOnDemand sample implFam hit` from `(s, none)`, drawing `a` at first use
and caches it. Then the two runs give the same joint law of `a`, the output and the final `σ`
state. In the lazy run `a` is read back from the cache. If no `hit` query fired, the cache is
still `none` and the run did not depend on `a`, so `a` is drawn afresh from `sample`. With
`pure default` there instead, `a` would always be `default` on those runs, while in the eager
run it follows `sample`. -/
theorem evalDist_simulateQ_sampleOnDemand_run_sample_eq
    (sample : ProbComp τ)
    (implFam : τ → QueryImpl spec (StateT σ ProbComp))
    (hit : spec.Domain → σ → Bool) [Inhabited τ]
    (h_indep : ∀ (t : spec.Domain) (s : σ) (a₁ a₂ : τ),
      hit t s = false → (implFam a₁ t).run s = (implFam a₂ t).run s)
    (oa : OracleComp spec α) (s : σ) :
    evalDist (do
      let a ← sample
      (fun z => (a, z)) <$> (simulateQ (implFam a) oa).run s) =
    evalDist (do
      let z ← (simulateQ (sampleOnDemand sample implFam hit) oa).run (s, none)
      let a ← (match z.2.2 with
               | some a => (pure a : ProbComp τ)
               | none => sample)
      pure (a, z.1, z.2.1)) := by
  revert s
  induction oa using OracleComp.inductionOn with
  | pure x =>
    -- No query fires, so the cache is still `none`: both sides are
    -- (distribution of `sample`) ⊗ (the trivial run).
    intro s
    simp [simulateQ_pure]
  | query_bind t k ih =>
    intro s
    by_cases h : hit t s = true
    · -- Hit query at empty cache: sample `a`, cache it, and let
      -- `run_simulateQ_sampleOnDemand_some_eq` carry `some a` to the end, where the completion
      -- `match` reads it back. Both sides are equal as terms, not merely in distribution.
      refine congrArg evalDist ?_
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
        OracleQuery.input_query, StateT.run_bind, map_bind, bind_assoc]
      have hg : (sampleOnDemand sample implFam hit t).run (s, none) =
          (do let a ← sample
              let p ← (implFam a t).run s
              pure (p.1, p.2, some a)) := by
        simp [sampleOnDemand, StateT.run, h]
      rw [hg]
      simp only [bind_assoc, pure_bind]
      refine bind_congr fun a => ?_
      refine bind_congr fun p => ?_
      rw [run_simulateQ_sampleOnDemand_some_eq sample implFam hit (k p.1) a p.2]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    · -- Non-hit query at empty cache: the impl is `τ`-independent here, so the outer
      -- sample commutes past this query and the induction hypothesis applies.
      have h_false : hit t s = false := by
        cases ht : hit t s with
        | true => exact absurd ht h
        | false => rfl
      apply evalDist_ext
      intro y
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
        OracleQuery.input_query, StateT.run_bind, map_bind]
      have hg : (sampleOnDemand sample implFam hit t).run (s, none) =
          (implFam (default : τ) t).run s >>= fun p =>
            (pure (p.1, p.2, (none : Option τ)) : ProbComp _) := by
        simp [sampleOnDemand, StateT.run, h_false, Option.getD]
      rw [hg]
      -- Keep this in `do`/`<$>` form so the pointwise replacement `eq1` matches below.
      simp only [bind_assoc, pure_bind]
      have h_impl : ∀ a : τ, (implFam a t).run s = (implFam default t).run s :=
        fun a => h_indep t s a default h_false
      -- Step 1: replace `implFam a t s` by `implFam default t s` in LHS (under `a ← sample`).
      have eq1 : Pr[= y | do
            let a ← sample
            let p ← (implFam a t).run s
            (fun z => (a, z)) <$> (simulateQ (implFam a) (k p.1)).run p.2] =
          Pr[= y | do
            let a ← sample
            let p ← (implFam default t).run s
            (fun z => (a, z)) <$> (simulateQ (implFam a) (k p.1)).run p.2] := by
        refine probOutput_bind_congr' _ y fun a => ?_
        rw [h_impl a]
      rw [eq1]
      -- Step 2: swap `a ← sample` past `p ← implFam default t s`.
      rw [probOutput_bind_bind_swap (mx := sample)
          (my := (implFam default t).run s)
          (f := fun a p =>
            (fun z => (a, z)) <$> (simulateQ (implFam a) (k p.1)).run p.2) (z := y)]
      -- Step 3: pointwise over `p`, apply the induction hypothesis at `p.2`.
      refine probOutput_bind_congr' _ y fun p => ?_
      exact congrFun (congrArg DFunLike.coe (ih p.1 p.2)) y

/-- Let `oa : OracleComp spec α`, let `s : σ` be the starting state, and let `h_indep` say that
`implFam a` does not depend on `a` at queries `t` with `hit t s = false`. The eager run of `oa`
draws `a ← sample` up front and simulates `oa` with `implFam a` from `s`. The lazy run simulates
`oa` with `sampleOnDemand sample implFam hit` from `(s, none)`. The two runs give the same joint law
of the output and the final `σ` state (the cache slot dropped). -/
theorem evalDist_simulateQ_sampleOnDemand_run_eq
    (sample : ProbComp τ)
    (implFam : τ → QueryImpl spec (StateT σ ProbComp))
    (hit : spec.Domain → σ → Bool) [Inhabited τ]
    (h_indep : ∀ (t : spec.Domain) (s : σ) (a₁ a₂ : τ),
      hit t s = false → (implFam a₁ t).run s = (implFam a₂ t).run s)
    (oa : OracleComp spec α) (s : σ) :
    evalDist (do
      let a ← sample
      (simulateQ (implFam a) oa).run s) =
    evalDist (Prod.map id Prod.fst <$>
      (simulateQ (sampleOnDemand sample implFam hit) oa).run (s, none)) := by
  -- Map the sample-preserving form by `Prod.snd`, dropping the `τ` component.
  have hplus := congrArg (fun d => (Prod.snd : τ × (α × σ) → α × σ) <$> d)
    (evalDist_simulateQ_sampleOnDemand_run_sample_eq sample implFam hit h_indep oa s)
  simp only [← evalDist_map] at hplus
  have hL : (Prod.snd : τ × (α × σ) → α × σ) <$> (do
        let a ← sample
        (fun z => (a, z)) <$> (simulateQ (implFam a) oa).run s) =
      (do let a ← sample
          (simulateQ (implFam a) oa).run s) := by
    simp [map_bind, Functor.map_map]
  have hR : (Prod.snd : τ × (α × σ) → α × σ) <$> (do
        let z ← (simulateQ (sampleOnDemand sample implFam hit) oa).run (s, none)
        let a ← (match z.2.2 with
                 | some a => (pure a : ProbComp τ)
                 | none => sample)
        pure (a, z.1, z.2.1)) =
      (do let z ← (simulateQ (sampleOnDemand sample implFam hit) oa).run (s, none)
          let _ ← (match z.2.2 with
                   | some a => (pure a : ProbComp τ)
                   | none => sample)
          (pure (z.1, z.2.1) : ProbComp (α × σ))) := by
    simp [map_bind, Functor.map_map]
  rw [hL, hR] at hplus
  rw [hplus]
  -- The completion draw is value-irrelevant and never fails, so it drops out.
  apply evalDist_ext
  intro y
  rw [map_eq_bind_pure_comp]
  refine probOutput_bind_congr' _ y fun z => ?_
  rcases z.2.2 with _ | a
  · simp [Prod.map]
  · simp [Prod.map]

/-- Let `oa : OracleComp spec α`, let `s : σ` be the starting state, and let `h_indep` say that
`implFam a` does not depend on `a` at queries `t` with `hit t s = false`. The eager run of `oa`
draws `a ← sample` up front and simulates `oa` with `implFam a` from `s`. The lazy run simulates
`oa` with `sampleOnDemand sample implFam hit` from `(s, none)`. The two runs give the same output
distribution. -/
theorem probOutput_simulateQ_sampleOnDemand_run'_eq
    (sample : ProbComp τ)
    (implFam : τ → QueryImpl spec (StateT σ ProbComp))
    (hit : spec.Domain → σ → Bool) [Inhabited τ]
    (h_indep : ∀ (t : spec.Domain) (s : σ) (a₁ a₂ : τ),
      hit t s = false → (implFam a₁ t).run s = (implFam a₂ t).run s)
    (oa : OracleComp spec α) (s : σ) :
    evalDist (do
      let a ← sample
      (simulateQ (implFam a) oa).run' s) =
    evalDist ((simulateQ (sampleOnDemand sample implFam hit) oa).run' (s, none)) := by
  have h := congrArg (fun d => (Prod.fst : α × σ → α) <$> d)
    (evalDist_simulateQ_sampleOnDemand_run_eq sample implFam hit h_indep oa s)
  simp only [← evalDist_map, map_bind, Functor.map_map] at h
  simpa only [StateT.run'_eq, Function.comp_def, Prod.map_fst, id] using h

end OracleComp.ProgramLogic.Relational
