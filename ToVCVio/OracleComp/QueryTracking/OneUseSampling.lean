/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.OracleComp.SimSemantics.StateT.Stop

/-!
# Sampling a parameter once or at every oracle query

**Setting.** Let

- `sample : ProbComp τ` be a randomized computation returning a parameter
  `a : τ`, and let `S := support sample` be the set of values it returns
  with positive probability;
- `impl : τ → QueryImpl spec (OptionT (StateT σ ProbComp))` be a family of
  randomized stateful oracle implementations indexed by `a : τ`, with query
  interface `spec` and state space `σ`.

For an adaptive adversary `oa : OracleComp spec Bool` and initial state
`s : σ`, let `Run(I, oa, s) := optionRun I oa s` run `oa` with oracle implementation `I` from
`s`. It returns the adversary's output bit, or `false` if an oracle returns `none`.

**Two experiments.** Define

```text
G_once(oa, s):
  a ← sample
  return Run(impl a, oa, s)

G_each(oa, s):
  return Run(sampleEachQuery sample impl, oa, s)
```

Here `sampleEachQuery sample impl` answers each query `t` by drawing a fresh
independent `a ← sample` and running `impl a t` from the current state.

**Main theorem** (`optionRun_sample_once_eq_sampleEachQuery`).
Fix arbitrary state predicates `Inv, used : σ → Prop`
and a test `hit : spec.Domain → σ → Bool`, with the following roles:

- `Inv` is the state invariant;
- `used s` marks states after which every query has the same joint distribution of response and
  next state under `impl a` for all `a ∈ S`;
- `hit t s = true` marks a query `t` in state `s` whose joint distribution of response and next
  state under `impl a` may vary with `a ∈ S`.

Assume that for every query `t`, state `s` satisfying `Inv s`, and parameters
`a, a' ∈ S`:

1. Every `(some r, s')` in the support of `((impl a t).run).run s` satisfies `Inv s'`.
2. If `used s`, every such `s'` also satisfies `used s'`.
3. If `hit t s = false`, running `impl a t` and `impl a' t` from `s` gives
   the same joint distribution of response and next state.
4. If `used s`, then `hit t s = false`.
5. If `hit t s = true`, every such `s'` satisfies `used s'`.

By 2, 4, and 5, a query with `hit t s = true` occurs only in a state without `used` and leads to
states with `used`, so every execution from an `Inv` state contains at most one such query.

Then, for every adaptive adversary `oa : OracleComp spec Bool` and
initial state `s` satisfying `Inv s`,
`Pr[G_once(oa, s) = true] = Pr[G_each(oa, s) = true]`.

**Stopped executions** (`stoppedRun_sample_once_eq`). Now let
`impl : τ → QueryImpl spec (StateT σ ProbComp)` and `target : QueryImpl spec (StateT σ ProbComp)`
be oracle implementations whose answers are never `none`, and `stop : σ → Bool` a test on states.
Assume conditions 1–5 for the queries `(impl a t).run s`, with conditions 1, 2, and 5 required
only for successors `s'` with `stop s' = false`. Assume also that `target` answers each query
from each state `s` with `Inv s` with the averaged distribution:
`𝒟[a ← sample; (impl a t).run s] = 𝒟[(target t).run s]`. Then, for every `oa` and `s` with
`Inv s`, `Pr[a ← sample; stoppedRun (impl a) stop oa s = true] =
Pr[stoppedRun target stop oa s = true]`.
-/

open OracleSpec ENNReal

namespace OracleComp

variable {ι σ τ : Type} {spec : OracleSpec ι}

/-- Stateful oracle implementation for `spec`: given a parameter sampler
`sample` and a family of oracle implementations `impl a`, it answers each
query `t` in state `s` by drawing a fresh `a ← sample` and running `impl a t`
from `s`, returning the optional response and next state. -/
def sampleEachQuery (sample : ProbComp τ)
    (impl : τ → QueryImpl spec (OptionT (StateT σ ProbComp))) :
    QueryImpl spec (OptionT (StateT σ ProbComp)) :=
  fun t => OptionT.mk fun s => do
    let a ← sample
    ((impl a t).run).run s

/-- For every query `t` and state `s`, running `sampleEachQuery sample impl t`
from `s` equals drawing `a ← sample` and then running `impl a t` from `s`. -/
theorem sampleEachQuery_run (sample : ProbComp τ)
    (impl : τ → QueryImpl spec (OptionT (StateT σ ProbComp)))
    (t : spec.Domain) (s : σ) :
    ((sampleEachQuery sample impl t).run).run s = (do
      let a ← sample
      ((impl a t).run).run s) := by
  rfl

/-- Computations equal in distribution give the same event probability after a common
continuation. -/
private theorem prEvent_bind_congr_of_evalDistEq {α : Type} {mx my : ProbComp α}
    (h : mx =ᵈ my) (f : α → ProbComp Prop) : prEvent (mx >>= f) = prEvent (my >>= f) := by
  simpa only [id_map'] using (h.bind (f := f) (g := f) fun _ ↦ .rfl).prEvent_eq fun x ↦ x

/-- For `a ∈ support sample` and `s` with `Inv s` and `used s`,
`optionRun (impl a) oa s` and `optionRun (sampleEachQuery sample impl) oa s`
return `true` with equal probability, given that queries preserve `Inv` and
`used`, and that query distributions from `used` states do not depend on the
parameter. -/
private theorem optionRun_sampleEachQuery_eq_of_used
    (sample : ProbComp τ) (impl : τ → QueryImpl spec (OptionT (StateT σ ProbComp)))
    (Inv used : σ → Prop)
    (hpres : ∀ a ∈ support sample, ∀ t s, Inv s →
      ∀ z ∈ support (((impl a t).run).run s), z.1.isSome → Inv z.2)
    (hused : ∀ a ∈ support sample, ∀ t s, Inv s → used s →
      ∀ z ∈ support (((impl a t).run).run s), z.1.isSome → used z.2)
    (hindep : ∀ t s, Inv s → used s → ∀ a ∈ support sample, ∀ a' ∈ support sample,
      ((impl a t).run).run s =ᵈ ((impl a' t).run).run s)
    (oa : OracleComp spec Bool) (a : τ) (ha : a ∈ support sample)
    (s : σ) (hs : Inv s) (hu : used s) :
    Pr{let x ← optionRun (impl a) oa s}[x = true] =
      Pr{let x ← optionRun (sampleEachQuery sample impl) oa s}[x = true] := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure b => simp [optionRun_pure]
  | query_bind t cont ih =>
    rw [optionRun_query_bind, optionRun_query_bind]
    simp only [sampleEachQuery_run, bind_assoc]
    trans Pr{let x ← (do
      let z ← ((impl a t).run).run s
      match z.1 with
      | none => pure false
      | some answer => optionRun (sampleEachQuery sample impl) (cont answer) z.2)}[x = true]
    · simp only [map_bind]
      refine prEvent_bind_congr_of_support _ _ _ ?_
      intro z hz
      cases hr : z.1 with
      | none => rfl
      | some answer =>
        have hc : z.1.isSome := by simp [hr]
        simpa only [hr] using ih answer z.2 (hpres a ha t s hs z hz hc)
          (hused a ha t s hs hu z hz hc)
    · symm
      trans Pr{let x ← (do
        let _ ← sample
        let z ← ((impl a t).run).run s
        match z.1 with
        | none => pure false
        | some answer => optionRun (sampleEachQuery sample impl) (cont answer) z.2)}[x = true]
      · simp only [map_bind]
        refine prEvent_bind_congr_of_support _ _ _ ?_
        intro a' ha'
        refine (prEvent_bind_congr_of_evalDistEq (hindep t s hs hu a' ha' a ha) _).trans
          (prEvent_bind_congr_of_support _ _ _ fun z _ ↦ ?_)
        rcases z with ⟨_ | _, _⟩ <;> rfl
      · rw [map_bind]
        exact prEvent_bind_const _ _

/-- For every Boolean adversary `oa` and state `s` with `Inv s`, drawing
`a ← sample` once and running `optionRun (impl a) oa s` returns `true` with
the same probability as `optionRun (sampleEachQuery sample impl) oa s`,
provided that for all `a, a' ∈ support sample`, queries `t`, and states `u`
with `Inv u`:

- every `(some r, u')` in the support of `((impl a t).run).run u` satisfies
  `Inv u'`, and also `used u'` if `used u`;
- if `hit t u = false`, then `((impl a t).run).run u =ᵈ ((impl a' t).run).run u`;
- if `used u`, then `hit t u = false`;
- if `hit t u = true`, then every `(some r, u')` in the support of
  `((impl a t).run).run u` satisfies `used u'`. -/
theorem optionRun_sample_once_eq_sampleEachQuery
    (sample : ProbComp τ) (impl : τ → QueryImpl spec (OptionT (StateT σ ProbComp)))
    (Inv used : σ → Prop) (hit : spec.Domain → σ → Bool)
    (hpres : ∀ a ∈ support sample, ∀ t s, Inv s →
      ∀ z ∈ support (((impl a t).run).run s), z.1.isSome → Inv z.2)
    (hused : ∀ a ∈ support sample, ∀ t s, Inv s → used s →
      ∀ z ∈ support (((impl a t).run).run s), z.1.isSome → used z.2)
    (hindep : ∀ t s, Inv s → hit t s = false →
      ∀ a ∈ support sample, ∀ a' ∈ support sample,
      ((impl a t).run).run s =ᵈ ((impl a' t).run).run s)
    (hnohit : ∀ t s, Inv s → used s → hit t s = false)
    (hfirst : ∀ a ∈ support sample, ∀ t s, Inv s → hit t s = true →
      ∀ z ∈ support (((impl a t).run).run s), z.1.isSome → used z.2)
    (oa : OracleComp spec Bool) (s : σ) (hs : Inv s) :
    Pr{let x ← do let a ← sample; optionRun (impl a) oa s}[x = true] =
      Pr{let x ← optionRun (sampleEachQuery sample impl) oa s}[x = true] := by
  obtain ⟨a₀, ha₀⟩ := OracleComp.support_nonempty sample
  induction oa using OracleComp.inductionOn generalizing s with
  | pure b => cases b <;> simp [optionRun_pure, prEvent_const_of_not, prEvent_true_eq_one]
  | query_bind t cont ih =>
    simp_rw [optionRun_query_bind]
    simp only [sampleEachQuery_run, bind_assoc]
    cases hh : hit t s with
    | false =>
      trans Pr{let x ← (do
        let a ← sample
        let z ← ((impl a₀ t).run).run s
        match z.1 with
        | none => pure false
        | some answer => optionRun (impl a) (cont answer) z.2)}[x = true]
      · simp only [map_bind]
        refine prEvent_bind_congr_of_support _ _ _ ?_
        intro a ha
        refine (prEvent_bind_congr_of_evalDistEq (hindep t s hs hh a ha a₀ ha₀) _).trans
          (prEvent_bind_congr_of_support _ _ _ fun z _ ↦ ?_)
        rcases z with ⟨_ | _, _⟩ <;> rfl
      · simp only [map_bind]
        rw [prEvent_bind_bind_swap]
        trans Pr{let x ← (do
          let z ← ((impl a₀ t).run).run s
          match z.1 with
          | none => pure false
          | some answer => optionRun (sampleEachQuery sample impl) (cont answer) z.2)}[x = true]
        · simp only [map_bind]
          refine prEvent_bind_congr_of_support _ _ _ ?_
          intro z hz
          cases hr : z.1 with
          | none => simp
          | some answer =>
            have hc : z.1.isSome := by simp [hr]
            simpa only [hr, map_bind] using ih answer z.2 (hpres a₀ ha₀ t s hs z hz hc)
        · symm
          trans Pr{let x ← (do
            let _ ← sample
            let z ← ((impl a₀ t).run).run s
            match z.1 with
            | none => pure false
            | some answer => optionRun (sampleEachQuery sample impl) (cont answer) z.2)}[x = true]
          · simp only [map_bind]
            refine prEvent_bind_congr_of_support _ _ _ ?_
            intro a ha
            refine (prEvent_bind_congr_of_evalDistEq (hindep t s hs hh a ha a₀ ha₀) _).trans
              (prEvent_bind_congr_of_support _ _ _ fun z _ ↦ ?_)
            rcases z with ⟨_ | _, _⟩ <;> rfl
          · rw [map_bind]
            exact prEvent_bind_const _ _
    | true =>
      simp only [map_bind]
      refine prEvent_bind_congr_of_support _ _ _ ?_
      intro a ha
      refine prEvent_bind_congr_of_support _ _ _ ?_
      intro z hz
      cases hr : z.1 with
      | none => rfl
      | some answer =>
        have hc : z.1.isSome := by simp [hr]
        simpa only [hr] using optionRun_sampleEachQuery_eq_of_used sample impl Inv used
          hpres hused (fun t s hi hu => hindep t s hi (hnohit t s hi hu))
          (cont answer) a ha z.2 (hpres a ha t s hs z hz hc)
          (hfirst a ha t s hs hh z hz hc)

/-- Let `impl a` (for `a : τ`) and `target` be stateful oracle implementations for `spec` with
state space `σ`, and let `stop : σ → Bool`. Write `S := support sample`. For every Boolean
computation `oa` and state `s` with `Inv s`,
`Pr[= true | a ← sample; stoppedRun (impl a) stop oa s] =
  Pr[= true | stoppedRun target stop oa s]`,
provided that for all `a, a' ∈ S`, queries `t`, and states `u` with `Inv u`, writing
"continuing successor" for every `(r, u')` in the support of `(impl a t).run u` with
`stop u' = false`:

- every continuing successor satisfies `Inv u'`, and also `used u'` if `used u`;
- if `hit t u = false`, then `𝒟[(impl a t).run u] = 𝒟[(impl a' t).run u]`;
- if `used u`, then `hit t u = false`;
- if `hit t u = true`, then every continuing successor satisfies `used u'`;
- `𝒟[a ← sample; (impl a t).run u] = 𝒟[(target t).run u]`. -/
theorem stoppedRun_sample_once_eq
    (sample : ProbComp τ) (impl : τ → QueryImpl spec (StateT σ ProbComp))
    (target : QueryImpl spec (StateT σ ProbComp)) (stop : σ → Bool)
    (Inv used : σ → Prop) (hit : spec.Domain → σ → Bool)
    (hpres : ∀ a ∈ support sample, ∀ t s, Inv s →
      ∀ z ∈ support ((impl a t).run s), stop z.2 = false → Inv z.2)
    (hused : ∀ a ∈ support sample, ∀ t s, Inv s → used s →
      ∀ z ∈ support ((impl a t).run s), stop z.2 = false → used z.2)
    (hindep : ∀ t s, Inv s → hit t s = false →
      ∀ a ∈ support sample, ∀ a' ∈ support sample,
      𝒟[(impl a t).run s] = 𝒟[(impl a' t).run s])
    (hnohit : ∀ t s, Inv s → used s → hit t s = false)
    (hfirst : ∀ a ∈ support sample, ∀ t s, Inv s → hit t s = true →
      ∀ z ∈ support ((impl a t).run s), stop z.2 = false → used z.2)
    (havg : ∀ t s, Inv s →
      𝒟[do let a ← sample; (impl a t).run s] = 𝒟[(target t).run s])
    (oa : OracleComp spec Bool) (s : σ) (hs : Inv s) :
    Pr[= true | do let a ← sample; stoppedRun (impl a) stop oa s] =
      Pr[= true | stoppedRun target stop oa s] := by
  have hpres' : ∀ a ∈ support sample, ∀ t s, Inv s →
      ∀ z ∈ support (((stopOnState (impl a) stop t).run).run s), z.1.isSome → Inv z.2 := by
    intro a ha t s hs z hz hsome
    obtain ⟨y, hy, hstop, hzy⟩ := exists_of_mem_support_stopOnState _ stop t s z hz hsome
    exact hzy ▸ hpres a ha t s hs y hy hstop
  unfold stoppedRun
  rw [optionRun_sample_once_eq_sampleEachQuery sample (fun a => stopOnState (impl a) stop)
    Inv used hit hpres'
    (fun a ha t s hs hu z hz hsome => by
      obtain ⟨y, hy, hstop, hzy⟩ := exists_of_mem_support_stopOnState _ stop t s z hz hsome
      exact hzy ▸ hused a ha t s hs hu y hy hstop)
    (fun t s hs hh a ha a' ha' => by
      rw [stopOnState_run_eq_map, stopOnState_run_eq_map, evalDist_map, evalDist_map,
        hindep t s hs hh a ha a' ha'])
    hnohit
    (fun a ha t s hs hh z hz hsome => by
      obtain ⟨y, hy, hstop, hzy⟩ := exists_of_mem_support_stopOnState _ stop t s z hz hsome
      exact hzy ▸ hfirst a ha t s hs hh y hy hstop) oa s hs]
  refine (probOutput_optionRun_eq_of_state_map _ (stopOnState target stop) id Inv ?_ ?_
    oa s hs).symm
  · intro t s hs z hz hsome
    rw [sampleEachQuery_run] at hz
    obtain ⟨a, ha, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    exact hpres' a ha t s hs z hz hsome
  · intro t s hs
    rw [Prod.map_id, id_map, sampleEachQuery_run]
    have h : (do let a ← sample; ((stopOnState (impl a) stop t).run).run s) =
        (fun y => (if stop y.2 then none else some y.1, y.2)) <$>
          (do let a ← sample; (impl a t).run s) := by
      simp only [stopOnState_run_eq_map, map_bind]
    rw [h, stopOnState_run_eq_map, evalDist_map, evalDist_map, havg t s hs]
    rfl

end OracleComp
