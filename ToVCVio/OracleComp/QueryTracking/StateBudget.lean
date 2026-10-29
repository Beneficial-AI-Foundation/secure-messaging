/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.QueryTracking.QueryBound
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

/-- If a state functional `f` grows by at most one at every `p`-query and not at all at other
queries, then along any run in the support it grows by at most the `p`-query budget `n`. -/
theorem support_state_measure_le_of_isQueryBoundP
    {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (f : σ → ℕ)
    (p : ι → Prop) [DecidablePred p]
    (hstep_p : ∀ t, p t → ∀ s, ∀ z ∈ support ((impl t).run s), f z.2 ≤ f s + 1)
    (hstep_np : ∀ t, ¬ p t → ∀ s, ∀ z ∈ support ((impl t).run s), f z.2 ≤ f s)
    (oa : OracleComp spec α) (n : ℕ) (hq : oa.IsQueryBoundP p n) (s : σ) :
    ∀ z ∈ support ((simulateQ impl oa).run s), f z.2 ≤ f s + n := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure x =>
      intro z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simp
  | query_bind t oa ih =>
      intro z hz
      rw [isQueryBoundP_query_bind_iff] at hq
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨x, hx, hzx⟩ := hz
      have hrec := ih x.1 (if p t then n - 1 else n) (hq.2 x.1) x.2 z hzx
      by_cases hpt : p t
      · have h1 := hstep_p t hpt s x hx
        have h2 : 0 < n := hq.1.resolve_left (not_not_intro hpt)
        simp only [ite_eq_left hpt] at hrec
        omega
      · have h1 := hstep_np t hpt s x hx
        simp only [ite_eq_right hpt] at hrec
        omega

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
