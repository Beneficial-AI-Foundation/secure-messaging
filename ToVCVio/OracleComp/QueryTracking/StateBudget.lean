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

**Parameters.** Fix a specification `spec : OracleSpec ι`, implementation
`impl : QueryImpl spec (StateT σ ProbComp)`, counter `count : σ → ℕ`, and
decidable query predicate `p : ι → Prop`.

**Assumption.** For every query `t`, state `s`, and supported successor
`(a, s')`, require `count s' ≤ count s + (if p t then 1 else 0)`.

**Conclusion.** For every output type `α`, computation `oa : OracleComp spec α`,
budget `q : ℕ` with `oa.IsQueryBoundP p q`, initial state `s`, and supported
final pair `(x, s')`, `count s' ≤ count s + q`.

**Proof.** Induct on the adaptive computation and subtract each query's cost
from the remaining budget. The bound applies separately to every supported
response and successor state.
-/

open OracleSpec

namespace OracleComp

/-- Assume every supported successor of query `t` from state `s` satisfies
`count s' ≤ count s + (if p t then 1 else 0)`. For every computation `oa`,
budget `q` with `oa.IsQueryBoundP p q`, initial state `s`, and supported
final pair `z`, `count z.2 ≤ count s + q`. -/
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
  | pure a =>
    have hz' : z = (a, s) := by simpa using hz
    obtain rfl := hz'
    exact Nat.le_add_right _ _
  | query_bind t cont ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    have htail := ih y.1 _ (hq.2 y.1) y.2 hz
    have hhead := hstep t s y hy
    by_cases ht : p t
    · have hpos : 0 < q := hq.1.resolve_left (not_not_intro ht)
      simp only [ht, ↓reduceIte] at htail hhead
      omega
    · simp only [ht, ↓reduceIte] at htail hhead
      omega

end OracleComp
