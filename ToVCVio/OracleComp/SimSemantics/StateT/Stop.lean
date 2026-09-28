/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
import VCVio.OracleComp.SimSemantics.OptionT.Basic
import ToVCVio.EvalDist.Monad.Basic

/-!
# Terminating a stateful simulation

**Parameters.** Fix types `ι σ : Type`, `spec : OracleSpec ι`, an
implementation `impl : QueryImpl spec (StateT σ ProbComp)`, and a test
`stop : σ → Bool`.

**Query semantics.** `stopOnState impl stop` processes query `t` from state
`s` by sampling `(a, s') ← (impl t).run s`. If `stop s' = true`, it returns
`none` in `OptionT` and retains `s'`. Otherwise it returns response `a` and
continues from `s'`. The test is applied to each query's successor state.
An immediate `pure a` computation returns `a` for every initial state.

**Boolean experiment.** `stoppedRun impl stop oa s` returns the Boolean
output of `oa` if execution completes, and `false` if execution terminates
through `OptionT`.

**Preservation theorem.** For every invariant `Inv : σ → Prop` preserved
by `impl` and satisfying `∀ s', Inv s' → stop s' = false`, every computation
`oa : OracleComp spec Bool`, and state `s : σ` with `Inv s`,
`Pr[= true | stoppedRun impl stop oa s] = Pr[= true | (simulateQ impl oa).run' s]`.
-/

open OracleSpec OracleComp ENNReal

namespace OracleComp

variable {ι σ : Type} {spec : OracleSpec ι}

/-- Execute a query under `impl`, then test `stop` on its successor state.
If the test is true, return `none` with that state; otherwise return the
query response as `some` and continue the adversary's computation. -/
def stopOnState (impl : QueryImpl spec (StateT σ ProbComp)) (stop : σ → Bool) :
    QueryImpl spec (OptionT (StateT σ ProbComp)) :=
  fun t => OptionT.mk fun s => do
    let (answer, next) ← (impl t).run s
    pure (if stop next then none else some answer, next)

/-- For every implementation, query, and initial state, if `stop` is false
on every supported successor, the stopped query's joint distribution is
the ordinary response/state distribution with each response wrapped in `some`. -/
theorem evalDist_stopOnState_eq_of_support
    (impl : QueryImpl spec (StateT σ ProbComp)) (stop : σ → Bool)
    (t : spec.Domain) (s : σ)
    (hstop : ∀ z ∈ support ((impl t).run s), stop z.2 = false) :
    𝒟[((stopOnState impl stop t).run).run s] =
      𝒟[(fun z => (some z.1, z.2)) <$> (impl t).run s] := by
  change 𝒟[(do
    let z ← (impl t).run s
    pure (if stop z.2 then none else some z.1, z.2))] = _
  rw [map_eq_pure_bind]
  apply evalDist_bind_congr
  intro z hz
  simp [hstop z hz]

/-- Run a Boolean adversary `oa` from `s` using `stopOnState impl stop`.
Return its output if it completes, and `false` if a query terminates it. -/
def stoppedRun (impl : QueryImpl spec (StateT σ ProbComp)) (stop : σ → Bool)
    (oa : OracleComp spec Bool) (s : σ) : ProbComp Bool :=
  (fun z => z.1.getD false) <$> ((simulateQ (stopOnState impl stop) oa).run).run s

/-- For every Boolean `a` and state `s`, the stopped execution of `pure a`
equals `pure a`. -/
theorem stoppedRun_pure (impl : QueryImpl spec (StateT σ ProbComp)) (stop : σ → Bool)
    (a : Bool) (s : σ) : stoppedRun impl stop (pure a) s = pure a := by
  simp [stoppedRun, OptionT.run_pure]

/-- A stopped execution first performs the next query. It returns `false`
if `stop` holds on the resulting state, and otherwise executes the
adversary's response-dependent continuation from that state. -/
theorem stoppedRun_query_bind (impl : QueryImpl spec (StateT σ ProbComp)) (stop : σ → Bool)
    (t : spec.Domain) (cont : spec.Range t → OracleComp spec Bool) (s : σ) :
    stoppedRun impl stop (liftM (OracleSpec.query t) >>= cont) s = (do
      let z ← (impl t).run s
      if stop z.2 then pure false else stoppedRun impl stop (cont z.1) z.2) := by
  simp only [stoppedRun, simulateQ_query_bind, OracleQuery.input_query,
    monadLift_self, OptionT.run_bind, Option.elimM, StateT.run_bind]
  change (fun z => z.1.getD false) <$> ((do
    let z ← (impl t).run s
    pure (if stop z.2 then none else some z.1, z.2)) >>= fun y =>
      (y.1.elim (pure none)
        (fun a => (simulateQ (stopOnState impl stop) (cont a)).run)).run y.2) = _
  simp only [bind_assoc, pure_bind, map_bind]
  apply bind_congr
  intro z
  cases hb : stop z.2
  · rfl
  · change (fun out : Option Bool × σ => out.1.getD false) <$>
      (pure (none, z.2) : ProbComp (Option Bool × σ)) = pure false
    simp

/-- Stopping preserves acceptance probability on invariant states.

**Assumptions.** Each query of `impl` preserves `Inv`, and `Inv s'` implies
`stop s' = false` for every state `s'`.

**Conclusion.** For any Boolean adversary `oa` and initial state `s`
satisfying `Inv`, its stopped and ordinary runs have equal probabilities
of returning `true`. -/
theorem probOutput_stoppedRun_eq_of_inv
    (impl : QueryImpl spec (StateT σ ProbComp)) (stop : σ → Bool) (Inv : σ → Prop)
    (hpres : QueryImpl.PreservesInv impl Inv) (hstop : ∀ s, Inv s → stop s = false)
    (oa : OracleComp spec Bool) (s : σ) (hs : Inv s) :
    Pr[= true | stoppedRun impl stop oa s] =
      Pr[= true | (simulateQ impl oa).run' s] := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp [stoppedRun_pure]
  | query_bind t cont ih =>
    rw [stoppedRun_query_bind]
    simp only [simulateQ_query_bind, OracleQuery.input_query,
      StateT.run'_eq, StateT.run_bind, map_bind]
    apply probOutput_bind_congr
    intro z hz
    have hi := hpres t s hs z hz
    rw [hstop z.2 hi]
    simpa [StateT.run'_eq] using ih z.1 z.2 hi

end OracleComp
