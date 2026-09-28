/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.OracleComp.SimSemantics.StateT.Stop

/-!
# Boolean output of a terminating stateful simulation

For an implementation `impl : QueryImpl spec (OptionT (StateT σ ProbComp))`,
a Boolean oracle computation `oa`, and initial state `s`, `optionRun`
returns the computation's output on completion and `false` on termination.
The query recurrence separates termination (`none`) from a supported
response (`some a`) followed by the adversary's continuation from the
successor state. The final state is discarded in both cases.

The state-map theorem lifts a per-query joint-distribution equality to
equality of acceptance probabilities. Its invariant need only persist on
successors for which execution continues.
-/

open OracleSpec

namespace OracleComp

variable {ι σ : Type} {spec : OracleSpec ι}

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

end OracleComp
