/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
import VCVio.OracleComp.SimSemantics.StateT.Basic
import VCVio.OracleComp.ProbComp

/-!
# State counters bounded by adaptive queries

**Setting.** Let

- `spec : OracleSpec ι` be a query interface;
- `σ` be a state space;
- `count : σ → ℕ` be a measure of the state, e.g. the number of completed operations;
- `p : ι → Prop` be a predicate selecting queries to count;
- `oa : OracleComp spec α` be an adaptive oracle computation;
- `q : ℕ` be a query budget for `oa`.

The condition `oa.IsQueryBoundP p q` means that every oracle-response path
of `oa` contains at most `q` queries satisfying `p`.

A stateful implementation `impl : QueryImpl spec (StateT σ ProbComp)`
satisfies the *counter condition* if, for every query `t`, state `s`, and
`(a, s') ∈ support ((impl t).run s)`,
`count s' ≤ count s + (if p t then 1 else 0)`.
Thus each selected query increases the counter by at most one, and other
queries can only preserve or decrease it.

**Result.** `stateCounter_simulateQ_run_le`: if `impl` satisfies the counter condition, then
for every `oa` and `q` with `oa.IsQueryBoundP p q` and every initial state `s`, each supported
final state `s'` satisfies `count s' ≤ count s + q`.
-/

open OracleSpec

namespace OracleComp

/-- Let `impl` be a stateful oracle implementation, `count : σ → ℕ` a counter,
and `p` the predicate selecting queries to count. Assume that for every
query `t`, state `u`, and `(a, u')` in the support of `(impl t).run u`,
`count u' ≤ count u + (if p t then 1 else 0)`.

Let `oa` be a computation making at most `q`
queries satisfying `p` on each oracle-response path, `s` an initial state, and
`z ∈ support ((simulateQ impl oa).run s)`. Then `count z.2 ≤ count s + q`. -/
theorem stateCounter_simulateQ_run_le
    {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (count : σ → ℕ)
    (p : ι → Prop) [DecidablePred p]
    (hstep : ∀ t s z, z ∈ support ((impl t).run s) →
      count z.2 ≤ count s + if p t then 1 else 0)
    (oa : OracleComp spec α) (q : ℕ) (hq : oa.IsQueryBoundP p q)
    (s : σ) (z : α × σ) (hz : z ∈ support ((simulateQ impl oa).run s)) :
    count z.2 ≤ count s + q := by
  induction oa using OracleComp.inductionOn generalizing q s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Nat.le_add_right _ _
  | @query_bind t cont ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hq
    obtain ⟨hcan, hcont⟩ := hq
    rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    have hs := hstep t s y hy
    by_cases ht : p t
    · have hqpos : 0 < q := hcan.resolve_left (not_not_intro ht)
      have := ih y.1 (q - 1) (by simpa [ht] using hcont y.1) y.2 hz
      simp only [ht, ite_true] at hs
      omega
    · have := ih y.1 q (by simpa [ht] using hcont y.1) y.2 hz
      simp only [ht, ite_false] at hs
      omega

end OracleComp
