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

**Parameters.** Fix types `ι σ : Type`, `spec : OracleSpec ι`, and a Boolean
oracle computation `oa : OracleComp spec Bool`.

**Boolean output.** For `impl : QueryImpl spec (OptionT (StateT σ ProbComp))`
and `s : σ`, `optionRun impl oa s` runs `oa` under `impl` from `s`. It returns
the output of `oa` if execution completes and `false` if a query returns
`none`. The final state is discarded.

**Stopping on a state test.** For `impl : QueryImpl spec (StateT σ ProbComp)`
and `stop : σ → Bool`, `stopOnState impl stop` answers query `t` in state `s`
by sampling `(a, s') ← (impl t).run s`. It returns `none` with state `s'` if
`stop s' = true`, and `some a` with state `s'` otherwise. Then
`stoppedRun impl stop = optionRun (stopOnState impl stop)`.

**Main results.**

- `probOutput_optionRun_eq_of_state_map`: let `f` map `left` states to
  `right` states and let `Inv` hold on every continuing successor of a `left`
  query from an `Inv` state. If every `right` query from `f s` has the
  distribution of the `left` query from `s` with its successor mapped through
  `f`, then `Pr[= true | optionRun right oa (f s)] = Pr[= true | optionRun left oa s]`
  for every `s` with `Inv s`.
- `probOutput_stoppedRun_eq_of_inv`: if `impl` preserves `Inv` and
  `Inv s' → stop s' = false` for every `s'`, then
  `Pr[= true | stoppedRun impl stop oa s] = Pr[= true | (simulateQ impl oa).run' s]`
  for every `s` with `Inv s`.
-/

open OracleSpec OracleComp ENNReal

namespace OracleComp

variable {ι σ : Type} {spec : OracleSpec ι}

/-! ### Boolean output of an `OptionT` simulation -/

/-- Execute Boolean computation `oa` under `impl` from `s`; return its output
on completion and `false` if an oracle terminates through `OptionT`. -/
def optionRun (impl : QueryImpl spec (OptionT (StateT σ ProbComp)))
    (oa : OracleComp spec Bool) (s : σ) : ProbComp Bool :=
  (fun z => z.1.getD false) <$> ((simulateQ impl oa).run).run s

/-- For every implementation, Boolean `a`, and initial state, executing
`pure a` through `optionRun` returns `a`. -/
theorem optionRun_pure (impl : QueryImpl spec (OptionT (StateT σ ProbComp)))
    (a : Bool) (s : σ) : optionRun impl (pure a) s = pure a := by
  simp [optionRun, OptionT.run_pure]

/-- For every query `t`, Boolean continuation `cont`, and state `s`, the
simulation first samples the query's optional response and successor state.
It returns `false` for `none` and resumes `cont a` for `some a`. -/
theorem optionRun_query_bind (impl : QueryImpl spec (OptionT (StateT σ ProbComp)))
    (t : spec.Domain) (cont : spec.Range t → OracleComp spec Bool) (s : σ) :
    optionRun impl (liftM (OracleSpec.query t) >>= cont) s = (do
      let z ← ((impl t).run).run s
      match z.1 with
      | none => pure false
      | some a => optionRun impl (cont a) z.2) := by
  simp only [optionRun, simulateQ_query_bind, OracleQuery.input_query,
    monadLift_self, OptionT.run_bind, Option.elimM, StateT.run_bind, map_bind]
  apply bind_congr
  intro z
  cases z.1 <;> simp [StateT.run_pure]

/-- Fix implementations `left` and `right`, a state map `f`, and an
invariant `Inv` on left states. Assume that every continuing left query
preserves `Inv`, and for every query `t` and invariant state `s`, the right
kernel at `f s` equals the left kernel followed by mapping its successor
through `f`. Then every Boolean adversary has equal acceptance probabilities
from `s` and `f s`, with termination returning `false` in both simulations. -/
theorem probOutput_optionRun_eq_of_state_map {τ : Type}
    (left : QueryImpl spec (OptionT (StateT σ ProbComp)))
    (right : QueryImpl spec (OptionT (StateT τ ProbComp)))
    (f : σ → τ) (Inv : σ → Prop)
    (hpres : ∀ t s, Inv s → ∀ z ∈ support (((left t).run).run s),
      z.1.isSome → Inv z.2)
    (hstep : ∀ t s, Inv s →
      𝒟[((right t).run).run (f s)] =
        𝒟[Prod.map id f <$> ((left t).run).run s])
    (oa : OracleComp spec Bool) (s : σ) (hs : Inv s) :
    Pr[= true | optionRun right oa (f s)] = Pr[= true | optionRun left oa s] := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure b => simp [optionRun_pure]
  | query_bind t cont ih =>
    rw [optionRun_query_bind, optionRun_query_bind]
    trans Pr[= true | do
      let z ← Prod.map id f <$> ((left t).run).run s
      match z.1 with
      | none => pure false
      | some a => optionRun right (cont a) z.2]
    · apply probOutput_congr rfl
      simp only [evalDist_bind, hstep t s hs]
    · simp only [bind_map_left]
      apply probOutput_bind_congr
      intro z hz
      simp only [Prod.map]
      cases hr : z.1 with
      | none => rfl
      | some a =>
        exact ih a z.2 (hpres t s hs z hz (by simp [hr]))

/-! ### Stopping on a state test -/

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

/-- Fix two stateful implementations and a state map `f`. For query `t`
from left state `s`, suppose the right kernel at `f s` equals the left
kernel followed by mapping the successor through `f`, and every supported
left successor has `stop = false`. Lifting the right query into `OptionT`
then equals stopping the left query and mapping its successor through `f`. -/
theorem evalDist_lift_eq_stopOnState_map {τ : Type}
    (left : QueryImpl spec (StateT σ ProbComp))
    (right : QueryImpl spec (StateT τ ProbComp)) (f : σ → τ)
    (stop : σ → Bool) (t : spec.Domain) (s : σ)
    (hmap : 𝒟[(right t).run (f s)] = 𝒟[Prod.map id f <$> (left t).run s])
    (hstop : ∀ z ∈ support ((left t).run s), stop z.2 = false) :
    𝒟[((liftM (right t) : OptionT (StateT τ ProbComp) (spec.Range t)).run).run (f s)] =
      𝒟[Prod.map id f <$> ((stopOnState left stop t).run).run s] := by
  rw [evalDist_map, evalDist_stopOnState_eq_of_support left stop t s hstop]
  simp only [OptionT.liftM_def, OptionT.lift, OptionT.run_mk,
    StateT.run_map, bind_pure_comp, evalDist_map, hmap,
    Functor.map_map]
  rfl

/-- Run a Boolean adversary `oa` from `s` using `stopOnState impl stop`:
`optionRun (stopOnState impl stop) oa s`. It returns the output of `oa` if
execution completes and `false` if a query stops it. -/
def stoppedRun (impl : QueryImpl spec (StateT σ ProbComp)) (stop : σ → Bool)
    (oa : OracleComp spec Bool) (s : σ) : ProbComp Bool :=
  optionRun (stopOnState impl stop) oa s

/-- For every Boolean `a` and state `s`, the stopped execution of `pure a`
equals `pure a`. -/
theorem stoppedRun_pure (impl : QueryImpl spec (StateT σ ProbComp)) (stop : σ → Bool)
    (a : Bool) (s : σ) : stoppedRun impl stop (pure a) s = pure a :=
  optionRun_pure _ a s

/-- A stopped execution first performs the next query. It returns `false`
if `stop` holds on the resulting state, and otherwise executes the
adversary's response-dependent continuation from that state. -/
theorem stoppedRun_query_bind (impl : QueryImpl spec (StateT σ ProbComp)) (stop : σ → Bool)
    (t : spec.Domain) (cont : spec.Range t → OracleComp spec Bool) (s : σ) :
    stoppedRun impl stop (liftM (OracleSpec.query t) >>= cont) s = (do
      let z ← (impl t).run s
      if stop z.2 then pure false else stoppedRun impl stop (cont z.1) z.2) := by
  rw [stoppedRun, optionRun_query_bind]
  change (do
    let z ← (do
      let z ← (impl t).run s
      pure (if stop z.2 then none else some z.1, z.2))
    match z.1 with
    | none => pure false
    | some a => optionRun (stopOnState impl stop) (cont a) z.2) = _
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro z
  cases stop z.2 <;> rfl

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
