/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import VCVio.OracleComp.QueryTracking.CachingOracle

/-!
# The queried point is cached after `withCaching`

Upstream `QueryImpl.withCaching_cache_le` states that a `withCaching` step only
extends the cache. This file adds the complementary fact: the final cache maps
the queried point to the returned answer. Both apply to `randomOracle`.
Candidate for upstream VCVio, next to `withCaching_cache_le` in
`VCVio/OracleComp/QueryTracking/CachingOracle.lean`.
-/

universe u v

open OracleComp OracleSpec

namespace QueryImpl

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec ι}
  {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]

/-- Let `t` be a query, and consider any possible outcome of a `withCaching` step
on `t`. Then the final cache maps `t` to the returned answer. -/
lemma withCaching_run_caches (so : QueryImpl spec m) (t : spec.Domain)
    (cache₀ : QueryCache spec) (z) (hz : z ∈ support ((so.withCaching t).run cache₀)) :
    z.2 t = some z.1 := by
  cases ht : cache₀ t with
  | some u =>
    rw [withCaching_run_some so ht, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact ht
  | none =>
    rw [withCaching_run_none so ht, support_map] at hz
    obtain ⟨v, _, rfl⟩ := hz
    exact QueryCache.cacheQuery_self cache₀ t v

end QueryImpl
