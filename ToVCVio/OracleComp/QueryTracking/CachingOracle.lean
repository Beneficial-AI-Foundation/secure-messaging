/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import VCVio.OracleComp.QueryTracking.CachingOracle

/-!
# A caching oracle records its answer in its table

Let `O` be a possibly randomized oracle that answers a query `x` with some `y ← O(x)`. The
caching oracle `Cache[O]` keeps a table `T` of past answers, where `T[x] = ⊥` means that `x`
has no entry:

```
Cache[O](x):
  if T[x] ≠ ⊥ then return T[x]
  y ← O(x)
  T[x] ← y
  return y
```

**Claim.** Fix a query `x` and an initial table `T`. Run `Cache[O](x)` from `T`, and let
`(y, T′)` be any possible outcome, where `y` is the returned answer and `T′` is the final table.
Then `T′[x] = y`.

**Lazy random oracle.** Let `O(x)` sample `y ←$ R_x`, where `R_x` is the set of answers to `x`.
Then `Cache[O]` is the lazy random oracle, so the claim holds for each of its queries.

**In Lean.**
* `Cache[O]` is `so.withCaching`, and the lazy random oracle is `randomOracle`;
* the claim is `withCaching_run_caches`

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
