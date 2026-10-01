/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
import VCVio.OracleComp.SimSemantics.OptionT.Basic
import ToVCVio.EvalDist.Monad.Basic

/-!
# Stopping stateful simulations and comparing their outputs

**Setting.** Let

- `spec : OracleSpec ι` be a query interface;
- `σ` be a state space;
- `oa : OracleComp spec Bool` be an adaptive Boolean oracle computation.

**Boolean output.** For an implementation
`impl : QueryImpl spec (OptionT (StateT σ ProbComp))` and an initial state `s`,
`optionRun impl oa s` returns the output of `oa` on completion, or `false`
if a query returns `none`. It discards the final state.

**Stopping rule.** For an implementation `impl : QueryImpl spec (StateT σ ProbComp)`
and a test `stop : σ → Bool`, `stopOnState impl stop` answers a query `t`
from state `s` by sampling `(a, s') ← (impl t).run s`.
It returns `(none, s')` if `stop s' = true`,
and `(some a, s')` otherwise. The Boolean execution is
`stoppedRun impl stop oa s := optionRun (stopOnState impl stop) oa s`.

**Results.** Under the hypotheses in the corresponding theorem docstrings:

- `probOutput_optionRun_eq_of_state_map` lifts equality of query distributions
  under a state map to equality of probabilities of returning `true`.
- `probOutput_stoppedRun_eq_of_inv` shows that stopping preserves the probability
  of returning `true` when a preserved invariant ensures `stop = false`.
- `signed_gap_stoppedRun_eq` shows that stopping preserves the signed difference
  between two simulations' probabilities of returning `true`.
-/

open OracleSpec OracleComp ENNReal

namespace OracleComp

variable {ι σ : Type} {spec : OracleSpec ι}

/-! ### Boolean output of an `OptionT` simulation -/

/-- Execute `oa` under `impl` from state `s`. Return the output bit on
completion, or `false` if a query returns `none`; discard the final state. -/
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

/-- Let `left` and `right` be oracle implementations with state spaces `σ`
and `τ`, `f : σ → τ` a state map, and `Inv : σ → Prop` an invariant. Assume
that for every query `t` and state `s` satisfying `Inv s`:

- each supported `left` response/state pair `(some a, s')` satisfies `Inv s'`;
- the joint distribution of response and next state under `right` from `f s`
  equals that under `left` from `s` after mapping the next state through `f`.

Then, for every Boolean computation `oa` and state `s` satisfying `Inv s`,
`optionRun right oa (f s)` and `optionRun left oa s` return `true` with equal
probability. -/
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

/-- Let `left` and `right` be stateful implementations and `f : σ → τ` a
state map. For a query `t` and state `s`, assume that the joint response/state
distribution under `right` from `f s` equals that under `left` from `s` after
mapping the next state through `f`. Assume also that `stop s' = false` for
every supported `left` successor `s'`.

Then lifting `right t` into `OptionT` from `f s` has the same joint
distribution as `stopOnState left stop t` from `s` with its next state
mapped through `f`. -/
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

/-- Let `impl` preserve an invariant `Inv : σ → Prop`, and assume
`stop u = false` for every state `u` satisfying `Inv u`. Then, for every
Boolean computation `oa` and initial state `s` satisfying `Inv s`,
`stoppedRun impl stop oa s` and `(simulateQ impl oa).run' s` return `true`
with equal probability. -/
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

/-! ### Cancellation of terminated paths -/

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

/-- Under the hypotheses of `signed_gap_stoppedRun_eq`, for every Boolean
computation `oa` and initial state satisfying `Inv`,
`p_left + p_right_stop = p_right + p_left_stop`, where `p_left` and `p_right`
are the probabilities of returning `true` in the ordinary simulations,
and `p_left_stop` and `p_right_stop` are those in the stopped simulations. -/
private theorem probOutput_stop_cross_add
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

/-- Let `left` and `right` be stateful oracle implementations,
`Inv, committed : σ → Prop` be state predicates, and `stop : σ → Bool` be
a stopping test. Here `committed` marks states from which execution continues
without stopping. Assume:

- `left` preserves `Inv`, and both implementations preserve `committed`;
- for every state `u`, `committed u` implies `stop u = false`;
- for every query `t` and state `u` satisfying `Inv u`, either
  `(left t).run u = (right t).run u`, or every supported successor under
  either implementation satisfies `committed`;
- for every state `u` with `Inv u` and `stop u = true`, every Boolean
  computation has equal probabilities of returning `true` under `left`
  and `right` from `u`.

For every Boolean computation `oa` and initial state `s` satisfying `Inv s`,
let `p_left`, `p_right` be its probabilities of returning `true` in the
ordinary simulations, and `p_left_stop`, `p_right_stop` those in the stopped
simulations. Then `p_left - p_right = p_left_stop - p_right_stop`, with
subtraction in `ℝ`. -/
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
