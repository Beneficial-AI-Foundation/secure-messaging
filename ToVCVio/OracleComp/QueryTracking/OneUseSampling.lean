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
      𝒟[((impl a t).run).run s] = 𝒟[((impl a' t).run).run s])
    (oa : OracleComp spec Bool) (a : τ) (ha : a ∈ support sample)
    (s : σ) (hs : Inv s) (hu : used s) :
    Pr[= true | optionRun (impl a) oa s] =
      Pr[= true | optionRun (sampleEachQuery sample impl) oa s] := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure b => simp [optionRun_pure]
  | query_bind t cont ih =>
    rw [optionRun_query_bind, optionRun_query_bind]
    simp only [sampleEachQuery_run, bind_assoc]
    trans Pr[= true | do
      let z ← ((impl a t).run).run s
      match z.1 with
      | none => pure false
      | some answer => optionRun (sampleEachQuery sample impl) (cont answer) z.2]
    · apply probOutput_bind_congr
      intro z hz
      cases hr : z.1 with
      | none => rfl
      | some answer =>
        have hc : z.1.isSome := by simp [hr]
        simpa only [hr] using ih answer z.2 (hpres a ha t s hs z hz hc)
          (hused a ha t s hs hu z hz hc)
    · symm
      trans Pr[= true | do
        let _ ← sample
        let z ← ((impl a t).run).run s
        match z.1 with
        | none => pure false
        | some answer => optionRun (sampleEachQuery sample impl) (cont answer) z.2]
      · apply probOutput_bind_congr
        intro a' ha'
        apply probOutput_congr rfl
        simp only [evalDist_bind, hindep t s hs hu a' ha' a ha]
        apply bind_congr
        intro z
        cases z.1 <;> rfl
      · simp only [probOutput_bind_const, probFailure_eq_zero, tsub_zero, one_mul]

/-- For every Boolean adversary `oa` and state `s` with `Inv s`, drawing
`a ← sample` once and running `optionRun (impl a) oa s` returns `true` with
the same probability as `optionRun (sampleEachQuery sample impl) oa s`,
provided that for all `a, a' ∈ support sample`, queries `t`, and states `u`
with `Inv u`:

- every `(some r, u')` in the support of `((impl a t).run).run u` satisfies
  `Inv u'`, and also `used u'` if `used u`;
- if `hit t u = false`, then `𝒟[((impl a t).run).run u] = 𝒟[((impl a' t).run).run u]`;
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
      𝒟[((impl a t).run).run s] = 𝒟[((impl a' t).run).run s])
    (hnohit : ∀ t s, Inv s → used s → hit t s = false)
    (hfirst : ∀ a ∈ support sample, ∀ t s, Inv s → hit t s = true →
      ∀ z ∈ support (((impl a t).run).run s), z.1.isSome → used z.2)
    (oa : OracleComp spec Bool) (s : σ) (hs : Inv s) :
    Pr[= true | do let a ← sample; optionRun (impl a) oa s] =
      Pr[= true | optionRun (sampleEachQuery sample impl) oa s] := by
  have hne : (support sample).Nonempty := by
    simp [Set.nonempty_iff_ne_empty, ← probFailure_eq_one_iff]
  obtain ⟨a₀, ha₀⟩ := hne
  induction oa using OracleComp.inductionOn generalizing s with
  | pure b => simp [optionRun_pure]
  | query_bind t cont ih =>
    simp_rw [optionRun_query_bind]
    simp only [sampleEachQuery_run, bind_assoc]
    cases hh : hit t s with
    | false =>
      trans Pr[= true | do
        let a ← sample
        let z ← ((impl a₀ t).run).run s
        match z.1 with
        | none => pure false
        | some answer => optionRun (impl a) (cont answer) z.2]
      · apply probOutput_bind_congr
        intro a ha
        apply probOutput_congr rfl
        simp only [evalDist_bind, hindep t s hs hh a ha a₀ ha₀]
        apply bind_congr
        intro z
        cases z.1 <;> rfl
      · rw [probOutput_bind_bind_swap]
        trans Pr[= true | do
          let z ← ((impl a₀ t).run).run s
          match z.1 with
          | none => pure false
          | some answer => optionRun (sampleEachQuery sample impl) (cont answer) z.2]
        · apply probOutput_bind_congr
          intro z hz
          cases hr : z.1 with
          | none => simp
          | some answer =>
            have hc : z.1.isSome := by simp [hr]
            simpa only [hr] using ih answer z.2 (hpres a₀ ha₀ t s hs z hz hc)
        · symm
          trans Pr[= true | do
            let _ ← sample
            let z ← ((impl a₀ t).run).run s
            match z.1 with
            | none => pure false
            | some answer => optionRun (sampleEachQuery sample impl) (cont answer) z.2]
          · apply probOutput_bind_congr
            intro a ha
            apply probOutput_congr rfl
            simp only [evalDist_bind, hindep t s hs hh a ha a₀ ha₀]
            apply bind_congr
            intro z
            cases z.1 <;> rfl
          · simp only [probOutput_bind_const, probFailure_eq_zero, tsub_zero, one_mul]
    | true =>
      apply probOutput_bind_congr
      intro a ha
      apply probOutput_bind_congr
      intro z hz
      cases hr : z.1 with
      | none => rfl
      | some answer =>
        have hc : z.1.isSome := by simp [hr]
        simpa only [hr] using optionRun_sampleEachQuery_eq_of_used sample impl Inv used
          hpres hused (fun t s hi hu => hindep t s hi (hnohit t s hi hu))
          (cont answer) a ha z.2 (hpres a ha t s hs z hz hc)
          (hfirst a ha t s hs hh z hz hc)

end OracleComp
