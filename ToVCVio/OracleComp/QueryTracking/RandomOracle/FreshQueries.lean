/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.QueryTracking.RandomOracle.Basic

/-!
# Fresh distinct queries to the lazy random oracle are independent uniforms

The lazily sampled random oracle `randomOracle` answers a point absent from its cache with a
fresh uniform draw. So querying it on a list of distinct, uncached points and then running a
continuation that does not touch the oracle is the same computation as drawing that many
independent uniform values. Candidate for upstream VCVio, next to
`VCVio/OracleComp/QueryTracking/RandomOracle/Basic.lean`.
-/

open OracleComp OracleSpec

namespace randomOracle

/-- Let `pts = x₁, …, x_q` be distinct points (`hnd`), none of them in the cache `c` (`hfresh`).
Querying the lazy random oracle at `x₁, …, x_q` from cache `c` and passing the answers to an
oracle-free `body` is the same computation as running `body` on `q` independent uniform samples
from `R`. -/
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
