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

**Parameters.** Fix a specification `spec : OracleSpec ι`, implementation
`impl : QueryImpl spec (StateT σ ProbComp)`, counter `count : σ → ℕ`, and
decidable query predicate `p : ι → Prop`.

**Assumption.** For every query `t`, state `s`, and supported successor
`(a, s')`, require `count s' ≤ count s + (if p t then 1 else 0)`.

**Conclusion.** For every output type `α`, computation `oa : OracleComp spec α`,
budget `q : ℕ` with `oa.IsQueryBoundP p q`, initial state `s`, and supported
final pair `(x, s')`, `count s' ≤ count s + q`.

**Proof.** Separate the per-query estimate into counted and uncounted queries,
then apply the adaptive state-measure bound to each supported final state.
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
  apply support_state_measure_le_of_isQueryBoundP impl count p ?_ ?_ oa q hq s z hz
  · intro t ht s z hz
    simpa [ht] using hstep t s z hz
  · intro t ht s z hz
    simpa [ht] using hstep t s z hz

end OracleComp
