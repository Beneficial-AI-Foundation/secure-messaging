/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.SimSemantics.StateT.Basic
import VCVio.OracleComp.ProbComp

/-!
# State counters bounded by a query budget

A natural-valued state counter may increase by at most one on queries
selected by a predicate and may not increase on other queries. A
syntactic query bound then bounds that counter on every supported
execution, even when queries are selected adaptively.
-/

open OracleSpec

namespace OracleComp

/-- If each query satisfying `p` increases state counter `count` by at
most one, and other queries do not increase it, then every supported run
of an adversary with at most `q` such queries ends with counter at most
`count s + q`. No monotonicity or exact-increment assumption is needed. -/
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
