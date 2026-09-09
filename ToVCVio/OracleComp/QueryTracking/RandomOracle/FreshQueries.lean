/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.QueryTracking.RandomOracle.Basic

/-!
# Fresh distinct queries to the lazy random oracle are independent uniforms

Staging for upstream VCVio (mirrors `VCVio/OracleComp/QueryTracking/RandomOracle/Basic.lean`,
whose lemmas sit in `namespace randomOracle`).

A list of *distinct* points that are all *absent* from the starting cache misses the cache at
every step, so `randomOracle` samples a fresh uniform value for each of them: the fetch loop
`pts.mapM randomOracle`, run from such a cache, is a chain of i.i.d. uniform draws. This is
the sampling content of the ideal experiment for a non-adaptive reduction, which queries a
fixed list of points before running its own tail computation.

The continuation `body` is a plain oracle computation that cannot read the cache, so the final
cache is discarded by `run'` and the statement is an equality of `ProbComp` *terms*, not merely
of distributions: every step is `QueryImpl.withCaching_run_none`, which is exact.
-/

open OracleComp OracleSpec

namespace randomOracle

/-- **Distinct fresh queries to a lazy random oracle are independent uniforms.** Running
`pts.mapM randomOracle` from a cache `c` in which none of the (pairwise distinct) points of
`pts` is cached, then continuing with a cache-blind `body` and discarding the cache, is the
same computation as drawing `pts.length` independent uniform values and calling `body` on
them.

Both hypotheses are needed: without `hnd` a repeated point would be answered from the cache
by its earlier value, and without `hfresh` an already-cached point would be answered by the
value stored in `c` — in neither case by a fresh uniform draw. -/
theorem run'_mapM_randomOracle_fresh {D R β : Type} [DecidableEq D] [SampleableType R]
    (pts : List D) (c : (D →ₒ R).QueryCache)
    (hnd : pts.Nodup) (hfresh : ∀ t ∈ pts, c t = none)
    (body : List R → ProbComp β) :
    ((pts.mapM (fun t => ((D →ₒ R).randomOracle t)) >>= fun vs =>
        liftM (body vs) : StateT ((D →ₒ R).QueryCache) ProbComp β)).run' c =
      pts.mapM (fun _ => ($ᵗ R : ProbComp R)) >>= body := by
  induction pts generalizing c body with
  | nil =>
      -- No queries: the cache is never touched and `run'` erases the lifted continuation.
      rw [List.mapM_nil, List.mapM_nil, pure_bind, pure_bind]
      simp [StateT.run'_eq, StateT.run_monadLift]
  | cons t ts ih =>
      obtain ⟨hnotmem, hnd'⟩ := List.nodup_cons.mp hnd
      -- The head point is fresh, so its query is a cache miss.
      have hct : c t = none := hfresh t (by simp)
      -- After caching the head answer, every tail point is still fresh: it differs from `t`
      -- by `Nodup`, so the new entry is invisible to it.
      have hfresh' : ∀ u : R, ∀ t' ∈ ts, (c.cacheQuery t u) t' = none := by
        intro u t' ht'
        have hne : t' ≠ t := fun h => hnotmem (h ▸ ht')
        rw [QueryCache.cacheQuery_of_ne c u hne]
        exact hfresh t' (List.mem_cons_of_mem _ ht')
      have hunif : (uniformSampleImpl (spec := (D →ₒ R)) t) = ($ᵗ R : ProbComp R) := rfl
      -- Peel the head query: push `run'` through the leading bind only, then apply the
      -- cache-miss step, which exposes a top-level uniform draw on both sides.
      rw [List.mapM_cons, List.mapM_cons, bind_assoc, bind_assoc, StateT.run'_bind']
      simp only [bind_assoc, pure_bind]
      rw [QueryImpl.withCaching_run_none uniformSampleImpl hct]
      simp only [bind_map_left, hunif]
      exact bind_congr fun u =>
        ih (c.cacheQuery t u) hnd' (hfresh' u) (fun xs => body (u :: xs))

end randomOracle
