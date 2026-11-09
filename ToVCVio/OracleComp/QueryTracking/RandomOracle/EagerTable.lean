/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-!
# Lazy random oracle equals eager table in the random oracle model

VCVio proves that the lazy random oracle equals an eagerly sampled uniform table for
computations whose only oracle is the hash oracle
(`OracleComp.evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTable`). This file extends
that to computations `OracleComp (unifSpec + (D →ₒ R)) α` run in the random oracle model,
where uniform queries pass through: the runtime `ProbCompRuntime.rom (D →ₒ R)` has the same
output distribution as drawing a uniform table `g : D → R` and then running the computation
with uniform queries kept probabilistic and hash queries answered by `g`. Candidate for
upstream VCVio, next to `VCVio/OracleComp/QueryTracking/RandomOracle/EagerTable.lean`.

## Main statements

* `OracleComp.evalDist_simulateQ_romImpl_run'_eq_tableExtending`: the cache-parametrized form,
  the induction vehicle.
* `OracleComp.rom_evalDist_empty_eq_uniformTable`: the empty-cache form, stated through the
  `rom` runtime.
-/

@[expose] public section

open MeasureTheory OracleSpec

namespace OracleComp

variable {D R : Type} [DecidableEq D] [Finite D] [SampleableType R] [SampleableType (D → R)]

/-- **Lazy random oracle equals eager table in the random oracle model, cache form.** Running
`oa` under `romImpl` from cache `c` has the same output distribution as drawing a uniform table
`g` and running `oa` with uniform queries passed through and hash queries answered by the table
that overlays `c` on `g`. -/
theorem evalDist_simulateQ_romImpl_run'_eq_tableExtending {α : Type} [MeasurableSpace α]
    (oa : OracleComp (unifSpec + (D →ₒ R)) α) (c : (D →ₒ R).QueryCache) :
    𝒟[(simulateQ (D →ₒ R).romImpl oa).run' c] =
      𝒟[do
        let g ← $ᵗ (D → R)
        simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn (tableExtending c g))) oa] := by
  classical
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a =>
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
    rw [evalDist_bind_const]
  | query_bind t k ih =>
    rcases t with n | t
    · -- A uniform query passes through on both sides; commute it with the table draw.
      have hl : (simulateQ (D →ₒ R).romImpl
            (liftM ((unifSpec + (D →ₒ R)).query (.inl n)) >>= k)).run' c =
          (unifSpec.query n : ProbComp _) >>= fun u =>
            (simulateQ (D →ₒ R).romImpl (k u)).run' c := by
        rw [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind,
          roSim.run_apply_inl, map_bind, bind_map_left]
        rfl
      have hr : ∀ g : D → R,
          simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn (tableExtending c g)))
              (liftM ((unifSpec + (D →ₒ R)).query (.inl n)) >>= k) =
            (unifSpec.query n : ProbComp _) >>= fun u =>
              simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn (tableExtending c g))) (k u) := by
        intro g
        rw [simulateQ_bind, simulateQ_spec_query]
        rfl
      rw [hl]
      simp_rw [hr]
      refine (evalDist_bind_congr _ _ _ fun u => ih u c).trans ?_
      exact evalDist_bind_bind_swap_of_uniform _ _ _
    · -- A hash query reads the cache on the lazy side and the overlaid table on the eager side.
      have hl : (simulateQ (D →ₒ R).romImpl
            (liftM ((unifSpec + (D →ₒ R)).query (.inr t)) >>= k)).run' c =
          ((D →ₒ R).randomOracle t).run c >>= fun p =>
            (simulateQ (D →ₒ R).romImpl (k p.1)).run' p.2 := by
        rw [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
        rfl
      have hr : ∀ g : D → R,
          simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn (tableExtending c g)))
              (liftM ((unifSpec + (D →ₒ R)).query (.inr t)) >>= k) =
            simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn (tableExtending c g)))
              (k (tableExtending c g t)) := by
        intro g
        rw [simulateQ_bind, simulateQ_spec_query]
        change (pure (tableExtending c g t) : ProbComp _) >>= _ = _
        rw [pure_bind]
      rw [hl]
      simp_rw [hr]
      rcases hc : c t with _ | u
      · -- Cache miss: absorb the fresh uniform answer into the table at `t`.
        let : MeasurableSpace R := ⊤
        rw [QueryImpl.withCaching_run_none _ hc, bind_map_left]
        set F : (D → R) → ProbComp α := fun g =>
          simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn (tableExtending c g)))
            (k (tableExtending c g t)) with hF
        have hk : ∀ (u : R) (g : D → R),
            simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn (tableExtending (c.cacheQuery t u) g)))
                (k u) = F (Function.update g t u) := by
          intro u g
          rw [hF, tableExtending_cacheQuery, tableExtending_update_of_none c g hc u]
          simp [tableExtending, hc]
        refine (evalDist_bind_congr _ _ _ fun u => ih u (c.cacheQuery t u)).trans ?_
        simp_rw [hk]
        exact evalDist_bind_bind_update ($ᵗ R) ($ᵗ (D → R))
          SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample t F
      · -- Cache hit: both sides answer with the cached value.
        rw [QueryImpl.withCaching_run_some _ hc, pure_bind, ih u c]
        have h : ∀ g : D → R, tableExtending c g t = u := fun g => by simp [tableExtending, hc]
        simp_rw [h]

/-- **Lazy random oracle equals eager table in the random oracle model.** Running `oa` in the
random oracle model from the empty cache has the same output distribution as drawing a uniform
table `g : D → R` and running `oa` with uniform queries passed through and hash queries answered
by `g`. -/
theorem rom_evalDist_empty_eq_uniformTable {α : Type} [MeasurableSpace α]
    (oa : OracleComp (unifSpec + (D →ₒ R)) α) :
    (ProbCompRuntime.rom (D →ₒ R)).evalDist oa =
      𝒟[do let g ← $ᵗ (D → R); simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn g)) oa] := by
  rw [ProbCompRuntime.rom_evalDist, evalDist_simulateQ_romImpl_run'_eq_tableExtending oa ∅]
  simp_rw [tableExtending_empty]

end OracleComp
