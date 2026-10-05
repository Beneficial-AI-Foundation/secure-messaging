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

- `ι` be a type and `spec : OracleSpec ι` a query interface with query type `spec.Domain = ι`
  and answer type `spec.Range t` for each query `t : ι`;
- `σ` be a state space, `s : σ` a state, and `stop : σ → Bool` a test on states;
- `oa : OracleComp spec Bool` be a Boolean oracle computation;
- `impl : QueryImpl spec (OptionT (StateT σ ProbComp))` and
  `base : QueryImpl spec (StateT σ ProbComp)` be stateful oracles.

**Notation.**

Write `O(t; u)` for the computation in which a stateful oracle `O` answers a query
`t : spec.Domain` from a state `u : σ`; it returns the answer together with the successor state.
The possible answers depend on the type of `O`:

- if `O` has the type of `base`, it always answers with some `a : spec.Range t`, and
  `O(t; u)` is `(O t).run u`;
- if `O` has the type of `impl`, it may also answer `⊥`, which stands for `none`, while an
  answer `a ≠ ⊥` stands for `some a`; here `O(t; u)` is `((O t).run).run u`.

**Definitions.**

`optionRun impl oa s : ProbComp Bool` runs `oa` from `s`, answering its queries
with `impl`. It returns the output bit of `oa` if no answer is `⊥`, and `false` at the first
answer `⊥` without issuing further queries; the final state is discarded.

```text
Base case:
  optionRun(impl, return b, s) = return b
Induction:
  optionRun(impl, (a ← query(t); cont(a)), s) =
      (a, s') ← impl(t; s)
      if a = ⊥ then return false
      optionRun(impl, cont(a), s')
```

`stopOnState base stop : QueryImpl spec (OptionT (StateT σ ProbComp))` answers each query as
`base` does, except that the answer becomes `⊥` when `stop` holds on the successor state:

```text
stopOnState(base, stop)(t; s) =
  (a, s') ← base(t; s)
  if stop(s') = true then return (⊥, s')
  return (a, s')
```

`stoppedRun base stop oa s : ProbComp Bool` runs `oa` from `s`, answering its queries with `base`.
It returns `false` at the first query whose successor state satisfies `stop`, and otherwise the
output bit of `oa`: `stoppedRun base stop oa s = optionRun (stopOnState base stop) oa s`.

The same run without stopping is `(simulateQ base oa).run' s : ProbComp Bool`: `simulateQ base oa`
replaces each query `t` of `oa` by `base t`, and `.run' s` starts from `s` and discards the final
state.

**Results.** A run *accepts* if it returns `true`.

- `probOutput_optionRun_eq_of_state_map`: for two oracles `left` and `right` of the type of
  `impl`, whose state spaces are related by a map `f`: if `right` answers each query from `f u` as
  `left` does from `u`, then `left` from `s` and `right` from `f s` accept with the same
  probability. The agreement is needed only at states satisfying an invariant of `left`.
- `probOutput_stoppedRun_eq_of_inv`: stopping has no effect when an invariant of `base` keeps
  `stop` false; the stopped and ordinary runs accept with the same probability.
- `signed_gap_stoppedRun_eq`: if two oracles `left` and `right` of the type of `base` answer
  queries identically until both enter states where `stop` stays false, and accept with equal
  probability from every state where `stop` holds, then stopping both runs leaves the difference
  of their acceptance probabilities unchanged.
-/

open OracleSpec OracleComp ENNReal

namespace OracleComp

variable {ι σ : Type} {spec : OracleSpec ι}

/-! ### Boolean output of an `OptionT` simulation -/

/-- Execute an oracle computation `oa : OracleComp spec Bool` from an initial
state `s : σ`, answering its queries with the stateful implementation
`impl : QueryImpl spec (OptionT (StateT σ ProbComp))`. Return the output bit
on completion, or `false` if a query returns `none`; discard the final state. -/
def optionRun (impl : QueryImpl spec (OptionT (StateT σ ProbComp)))
    (oa : OracleComp spec Bool) (s : σ) : ProbComp Bool :=
  (fun z => z.1.getD false) <$> ((simulateQ impl oa).run).run s

/-- For every implementation, Boolean `a`, and initial state, executing
`pure a` through `optionRun` returns `a`. -/
theorem optionRun_pure (impl : QueryImpl spec (OptionT (StateT σ ProbComp)))
    (a : Bool) (s : σ) : optionRun impl (pure a) s = pure a := by
  simp [optionRun, OptionT.run_pure]

/-- For a query `t : spec.Domain` and continuation
`cont : spec.Range t → OracleComp spec Bool`, the following computations are equal:

```text
optionRun(impl, (a ← query(t); cont(a)), s) =
  (a, s') ← impl(t; s)
  if a = ⊥ then return false
  optionRun(impl, cont(a), s')
```
-/
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

- every `(some a, s')` in the support of `((left t).run).run s` satisfies `Inv s'`;
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

/-- Stateful oracle implementation for `spec` that answers each query as `impl` does, except
that the answer becomes `none` when `stop` holds on the successor state; that state is kept. -/
def stopOnState (impl : QueryImpl spec (StateT σ ProbComp)) (stop : σ → Bool) :
    QueryImpl spec (OptionT (StateT σ ProbComp)) :=
  fun t => OptionT.mk fun s => do
    let (answer, next) ← (impl t).run s
    pure (if stop next then none else some answer, next)

/-- For every query `t` and state `s`, if `stop s' = false` for every `(a, s')` in the support
of `(impl t).run s`, then the joint distribution of response and next state under
`stopOnState impl stop t` is that of `(impl t).run s` with each response wrapped in `some`. -/
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
every `(a, s')` in the support of `(left t).run s`.

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

/-- Run a Boolean computation `oa` from `s`, answering its queries with `impl`; return `false` at
the first query whose successor state satisfies `stop`, and otherwise the output bit of `oa`.
By definition, `stoppedRun impl stop oa s = optionRun (stopOnState impl stop) oa s`. -/
def stoppedRun (impl : QueryImpl spec (StateT σ ProbComp)) (stop : σ → Bool)
    (oa : OracleComp spec Bool) (s : σ) : ProbComp Bool :=
  optionRun (stopOnState impl stop) oa s

/-- For every Boolean `a` and state `s`, the stopped execution of `pure a`
equals `pure a`. -/
theorem stoppedRun_pure (impl : QueryImpl spec (StateT σ ProbComp)) (stop : σ → Bool)
    (a : Bool) (s : σ) : stoppedRun impl stop (pure a) s = pure a :=
  optionRun_pure _ a s

/-- For a query `t : spec.Domain` and continuation
`cont : spec.Range t → OracleComp spec Bool`, the following computations are equal:

```text
stoppedRun(impl, stop, (a ← query(t); cont(a)), s) =
  (a, s') ← impl(t; s)
  if stop(s') = true then return false
  stoppedRun(impl, stop, cont(a), s')
```
-/
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

/-- If `impl` preserves `Inv`, `Inv u` implies `stop u = false`, and every `(a, s')` in the
support of `(impl t).run s` satisfies `Inv s'`, then the stopped and ordinary runs of
`a ← query(t); cont(a)` from `s` return `true` with equal probability. -/
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
- for every query `t` and state `u` satisfying `Inv u`, one of the following holds:
  - `(left t).run u = (right t).run u`, or
  - every `(a, u')` in the support of `(left t).run u` or of `(right t).run u` satisfies
    `committed u'`;
- for every state `u` with `Inv u` and `stop u = true`, every Boolean
  computation has equal probabilities of returning `true` under `left`
  and `right` from `u`.

For every Boolean computation `oa` and initial state `s` satisfying `Inv s`,
let `p_left`, `p_right` be its probabilities of returning `true` in the
ordinary simulations, and `p_left_stop`, `p_right_stop` those in the stopped
simulations.

Then `p_left - p_right = p_left_stop - p_right_stop`, with subtraction in `ℝ`. -/
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
