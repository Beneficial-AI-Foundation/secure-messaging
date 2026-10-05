/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.SimSemantics.StateT.Basic
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
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

**Results.** For every `oa` and `q` with `oa.IsQueryBoundP p q`:

- `stateCounter_simulateQ_run_le`: if `impl` satisfies the counter condition,
  then for every initial state `s`, each supported final state `s'` satisfies
  `count s' ≤ count s + q`.
- `simulateQ_run_eq_of_query_eq_stateBudget`: let
  `left right : QueryImpl spec (StateT σ ProbComp)`, `Inv : σ → Prop`, and `Q : ℕ`. Assume
  - `left` preserves `Inv`;
  - `left` satisfies the counter condition;
  - `(left t).run u = (right t).run u` whenever `Inv u` and `count u ≤ Q`.

  Then `(simulateQ left oa).run s = (simulateQ right oa).run s` for every `s` with `Inv s` and
  `count s + q ≤ Q`.
-/

open OracleSpec

namespace OracleComp

/-- Let `impl` be a stateful oracle implementation, `count : σ → ℕ` a counter,
and `p` the predicate selecting queries to count. Assume that for every
query `t`, state `s`, and `(a, s')` in the support of `(impl t).run s`,
`count s' ≤ count s + (if p t then 1 else 0)`.

Then the counter grows by at most `q` along every execution: for every computation `oa`
making at most `q` queries satisfying `p` on each oracle-response path, every initial state `s`,
and every `z ∈ support ((simulateQ impl oa).run s)`,

```text
count z.2 ≤ count s + q.
```
-/
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

/-- Let `left` and `right` be stateful oracle implementations, `Inv` a state
invariant, `count` a state counter, `p` the predicate selecting queries to
count, and `Q : ℕ` a counter limit. Assume:

- `left` preserves `Inv`: for every query `t` and state `u` with `Inv u`, every `(a, u')` in
  the support of `(left t).run u` satisfies `Inv u'`;
- for every query `t`, state `u`, and `(a, u')` in the support of `(left t).run u`,
  `count u' ≤ count u + (if p t then 1 else 0)`;
- for every query `t` and state `u` with `Inv u` and `count u ≤ Q`,
  `(left t).run u = (right t).run u`.

Then, for every computation `oa` making at most `q` queries satisfying `p`
on each oracle-response path, and every state `s` with `Inv s` and
`count s + q ≤ Q`, the complete output/state computations are equal:

```text
(simulateQ left oa).run s = (simulateQ right oa).run s.
```
-/
theorem simulateQ_run_eq_of_query_eq_stateBudget
    {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    (left right : QueryImpl spec (StateT σ ProbComp))
    (Inv : σ → Prop) (count : σ → ℕ) (p : ι → Prop) [DecidablePred p] (Q : ℕ)
    (hpres : QueryImpl.PreservesInv left Inv)
    (hstep : ∀ t s z, z ∈ support ((left t).run s) →
      count z.2 ≤ count s + if p t then 1 else 0)
    (hagree : ∀ t s, Inv s → count s ≤ Q → (left t).run s = (right t).run s)
    (oa : OracleComp spec α) (q : ℕ) (hq : oa.IsQueryBoundP p q)
    (s : σ) (hs : Inv s) (hbudget : count s + q ≤ Q) :
    (simulateQ left oa).run s = (simulateQ right oa).run s := by
  induction oa using OracleComp.inductionOn generalizing q s with
  | pure a => simp
  | query_bind t cont ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    rw [← hagree t s hs (by omega)]
    apply bind_congr_of_forall_mem_support
    intro z hz
    refine ih z.1 _ (hq.2 z.1) z.2 (hpres t s hs z hz) ?_
    have hc := hstep t s z hz
    by_cases ht : p t
    · have hpos : 0 < q := hq.1.resolve_left (not_not_intro ht)
      simp only [ht, ↓reduceIte] at hc ⊢
      omega
    · simp only [ht, ↓reduceIte] at hc ⊢
      omega

end OracleComp
