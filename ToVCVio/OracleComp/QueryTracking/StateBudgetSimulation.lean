/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.OracleComp.QueryTracking.StateBudget
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv

/-!
# Equality of simulations within a query budget

Fix types `ι σ α : Type`, an oracle specification `spec : OracleSpec ι`,
implementations `left right : QueryImpl spec (StateT σ ProbComp)`, an
invariant `Inv : σ → Prop`, a counter `count : σ → ℕ`, a decidable query
predicate `p : ι → Prop`, and a limit `Q : ℕ`. Assume `left` preserves `Inv`.
For every query `t`, state `s`, and supported successor `(a, s')` under
`left`, require `count s' ≤ count s + (if p t then 1 else 0)`. For every
`t` and invariant `s` with `count s ≤ Q`, require equality of the two query
computations.

For every computation `oa : OracleComp spec α`, budget `q : ℕ` bounding
its `p`-selected queries on all response paths, and state `s` satisfying
`Inv s` and `count s + q ≤ Q`, the complete output/state computations under
`left` and `right` are equal. The proof inducts on `oa`, sharing each query's
response and successor state and subtracting its cost from the remaining
budget. Equality is needed only within the counter limit, allowing an
unbounded oracle interface to be compared with a finite family of hybrids.
-/

open OracleSpec

namespace OracleComp

/-- Equality of complete simulations under a state-counter limit.

**Assumptions.** `left` preserves `Inv`; a query increases `count` by at
most `1` if `p` holds and by at most `0` otherwise; and `left` and `right`
have equal response/state computations on `Inv` states with `count ≤ Q`.

**Conclusion.** If `oa` makes at most `q` queries selected by `p`, then its
two output/state computations from any `s` satisfying `Inv s` and
`count s + q ≤ Q` are equal. Query equality shares the supported successor
states, carrying the invariant and remaining budget through the induction. -/
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
