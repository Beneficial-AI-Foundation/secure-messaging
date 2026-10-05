/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.OracleComp.QueryTracking.QueryBound
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
  apply support_state_measure_le_of_isQueryBoundP impl count p ?_ ?_ oa q hq s z hz
  · intro t ht s z hz
    simpa [ht] using hstep t s z hz
  · intro t ht s z hz
    simpa [ht] using hstep t s z hz

end OracleComp
