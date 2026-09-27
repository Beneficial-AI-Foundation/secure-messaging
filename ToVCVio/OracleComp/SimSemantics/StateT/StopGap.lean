/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.OracleComp.SimSemantics.StateT.Stop

/-!
# Cancellation of terminated paths

Fix types `ι σ : Type`, an oracle specification `spec : OracleSpec ι`,
implementations `left right : QueryImpl spec (StateT σ ProbComp)`, predicates
`Inv committed : σ → Prop`, and a termination test `stop : σ → Bool`.
The stopped simulation tests `stop` after each query and returns `false`
upon termination.

Assume `left` preserves `Inv`; both implementations preserve `committed`;
and `stop s = false` for every committed state `s`. For every query `t`
and invariant state `s`, require either equality of the two response/state
computations, or that every supported successor under either implementation
is committed. Finally, for every invariant state `s` with `stop s = true`
and Boolean continuation `oa`, require equal ordinary acceptance probabilities.

For every Boolean computation `oa` and initial state `s` satisfying `Inv`,
the signed difference of ordinary acceptance probabilities equals the
signed difference of stopped acceptance probabilities. The proof inducts
on `oa`: equal queries share a response/state sample, terminated continuations
cancel by assumption, and differing queries enter a preserved region where
termination is impossible. `committed` identifies that region; it need not
be a syntactic flag in the state.
-/

open OracleSpec ENNReal

namespace OracleComp

variable {ι σ : Type} {spec : OracleSpec ι}

/-- For every query `t`, Boolean continuation `cont`, and initial state `s`,
stopped and ordinary query/continuation runs have equal acceptance probability
if every supported query successor satisfies a preserved invariant `Inv`
with `∀ u, Inv u → stop u = false`. -/
private theorem probOutput_stoppedRun_query_eq
    (impl : QueryImpl spec (StateT σ ProbComp)) (stop : σ → Bool) (Inv : σ → Prop)
    (hpres : QueryImpl.PreservesInv impl Inv) (hstop : ∀ s, Inv s → stop s = false)
    (t : spec.Domain) (cont : spec.Range t → OracleComp spec Bool) (s : σ)
    (hnext : ∀ z ∈ support ((impl t).run s), Inv z.2) :
    Pr[= true | stoppedRun impl stop (liftM (OracleSpec.query t) >>= cont) s] =
      Pr[= true | (simulateQ impl (liftM (OracleSpec.query t) >>= cont)).run' s] := by
  rw [stoppedRun_query_bind]
  simp only [simulateQ_query_bind, OracleQuery.input_query,
    StateT.run'_eq, StateT.run_bind, map_bind, monadLift_self]
  apply probOutput_bind_congr
  intro z hz
  rw [hstop z.2 (hnext z hz)]
  simpa [StateT.run'_eq] using
    probOutput_stoppedRun_eq_of_inv impl stop Inv hpres hstop (cont z.1) z.2 (hnext z hz)

/-- Cross-addition identity for discarding common terminated paths.

**Assumptions.** `left` preserves `Inv`, and both implementations preserve
`committed`. Every committed state satisfies `stop = false`. On invariant states, each query
either has identical response/state computations in both implementations,
or every supported successor under either implementation is committed.
From invariant states satisfying `stop`, all Boolean continuations have
equal acceptance probabilities in the two ordinary simulations.

**Conclusion.** For any Boolean adversary `oa` and initial invariant state,
`pL + pRstop = pR + pLstop`, where `pL` and `pR` are ordinary acceptance
probabilities and `pLstop`, `pRstop` are acceptance probabilities under
`stoppedRun`. All four probabilities are elements of `ℝ≥0∞`. -/
theorem probOutput_stop_cross_add
    (left right : QueryImpl spec (StateT σ ProbComp))
    (Inv committed : σ → Prop) (stop : σ → Bool)
    (hleft : QueryImpl.PreservesInv left Inv)
    (hcommitL : QueryImpl.PreservesInv left committed)
    (hcommitR : QueryImpl.PreservesInv right committed)
    (hstop : ∀ s, committed s → stop s = false)
    (hquery : ∀ t s, Inv s →
      (left t).run s = (right t).run s ∨
      ((∀ z ∈ support ((left t).run s), committed z.2) ∧
       (∀ z ∈ support ((right t).run s), committed z.2)))
    (hdead : ∀ s, Inv s → stop s = true → ∀ oa : OracleComp spec Bool,
      Pr[= true | (simulateQ left oa).run' s] = Pr[= true | (simulateQ right oa).run' s])
    (oa : OracleComp spec Bool) (s : σ) (hs : Inv s) :
    Pr[= true | (simulateQ left oa).run' s] + Pr[= true | stoppedRun right stop oa s] =
      Pr[= true | (simulateQ right oa).run' s] + Pr[= true | stoppedRun left stop oa s] := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp [stoppedRun_pure]
  | query_bind t cont ih =>
    rcases hquery t s hs with heq | ⟨hnextL, hnextR⟩
    · rw [stoppedRun_query_bind, stoppedRun_query_bind]
      simp only [simulateQ_query_bind, OracleQuery.input_query,
        StateT.run'_eq, StateT.run_bind, map_bind, monadLift_self]
      dsimp only [OracleSpec.query, OracleQuery.cont, OracleQuery.input]
      simp only [← heq]
      simp only [probOutput_bind_eq_tsum]
      rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
      apply tsum_congr
      intro z
      by_cases hz : z ∈ support ((left t).run s)
      · have hi := hleft t s hs z hz
        rw [← mul_add, ← mul_add]
        congr 1
        cases hb : stop z.2
        · simpa [hb, StateT.run'_eq] using ih z.1 z.2 hi
        · simpa [hb, StateT.run'_eq] using hdead z.2 hi hb (cont z.1)
      · simp [probOutput_eq_zero_of_not_mem_support hz]
    · rw [probOutput_stoppedRun_query_eq left stop committed hcommitL hstop t cont s hnextL,
        probOutput_stoppedRun_query_eq right stop committed hcommitR hstop t cont s hnextR]
      exact add_comm _ _

/-- Signed acceptance-probability difference is preserved by termination.

**Assumptions.** `left` preserves `Inv`; both implementations preserve
`committed`; committed states satisfy `stop = false`; and each query on an
invariant state either agrees in both implementations or enters committed
states under both. At invariant states satisfying `stop`, all ordinary
Boolean continuations have equal acceptance probabilities.

**Conclusion.** For any Boolean adversary `oa` and initial state `s`
satisfying `Inv`, the real-valued difference between the two ordinary
acceptance probabilities equals the difference between their stopped
acceptance probabilities. Terminated executions return `false`. -/
theorem signed_gap_stoppedRun_eq
    (left right : QueryImpl spec (StateT σ ProbComp))
    (Inv committed : σ → Prop) (stop : σ → Bool)
    (hleft : QueryImpl.PreservesInv left Inv)
    (hcommitL : QueryImpl.PreservesInv left committed)
    (hcommitR : QueryImpl.PreservesInv right committed)
    (hstop : ∀ s, committed s → stop s = false)
    (hquery : ∀ t s, Inv s →
      (left t).run s = (right t).run s ∨
      ((∀ z ∈ support ((left t).run s), committed z.2) ∧
       (∀ z ∈ support ((right t).run s), committed z.2)))
    (hdead : ∀ s, Inv s → stop s = true → ∀ oa : OracleComp spec Bool,
      Pr[= true | (simulateQ left oa).run' s] = Pr[= true | (simulateQ right oa).run' s])
    (oa : OracleComp spec Bool) (s : σ) (hs : Inv s) :
    (Pr[= true | (simulateQ left oa).run' s]).toReal -
        (Pr[= true | (simulateQ right oa).run' s]).toReal =
      (Pr[= true | stoppedRun left stop oa s]).toReal -
        (Pr[= true | stoppedRun right stop oa s]).toReal := by
  have h := congrArg ENNReal.toReal
    (probOutput_stop_cross_add left right Inv committed stop hleft hcommitL hcommitR
      hstop hquery hdead oa s hs)
  rw [ENNReal.toReal_add (by simp) (by simp),
    ENNReal.toReal_add (by simp) (by simp)] at h
  linarith

end OracleComp
