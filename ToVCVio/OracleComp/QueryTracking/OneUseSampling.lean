/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.OracleComp.SimSemantics.StateT.OptionOutput

/-!
# One-use sampling in a terminating stateful simulation

**Parameters.** Fix a sampler `sample : ProbComp τ`, a family
`impl : τ → QueryImpl spec (OptionT (StateT σ ProbComp))`, state predicates
`Inv used`, and a use test `hit : spec.Domain → σ → Bool`.

**Assumptions.** Every supported query successor with a returned response
preserves `Inv`, and preserves `used` whenever it already holds. For every
invariant state and query with `hit = false`, the response/state computation
is equal for all parameter values. Every invariant used state has
`hit = false`. For a query with `hit = true`, every supported successor
with a returned response satisfies `used`.

**Statement.** For every Boolean adversary and initial invariant state,
sampling the parameter once before execution and sampling it afresh at
each query give equal acceptance probabilities. Termination returns `false`.

**Proof.** Before use, commute the sample past parameter-independent queries.
At use, couple the two samples. Every continuing successor then satisfies
`used`, so subsequent query computations are parameter-independent.
-/

open OracleSpec ENNReal

namespace OracleComp

variable {ι σ τ : Type} {spec : OracleSpec ι}

/-- At each query, draw `a ← sample` and execute `impl a` from the current
state. Its optional response and successor are returned unchanged. -/
def sampleEachQuery (sample : ProbComp τ)
    (impl : τ → QueryImpl spec (OptionT (StateT σ ProbComp))) :
    QueryImpl spec (OptionT (StateT σ ProbComp)) :=
  fun t => OptionT.mk fun s => do
    let a ← sample
    ((impl a t).run).run s

/-- For every query and initial state, `sampleEachQuery` runs the query
kernel with a freshly drawn parameter, retaining its response and successor. -/
theorem sampleEachQuery_run (sample : ProbComp τ)
    (impl : τ → QueryImpl spec (OptionT (StateT σ ProbComp)))
    (t : spec.Domain) (s : σ) :
    ((sampleEachQuery sample impl t).run).run s = (do
      let a ← sample
      ((impl a t).run).run s) := by
  rfl

/-- Assume `Inv` and `used` persist along continuing queries, and every query
on an invariant used state has the same computation for all parameter values.
For every fixed parameter, Boolean adversary, and invariant used initial
state, fixing the parameter and resampling it per query have equal acceptance. -/
theorem optionRun_sampleEachQuery_eq_of_used
    (sample : ProbComp τ) (impl : τ → QueryImpl spec (OptionT (StateT σ ProbComp)))
    (Inv used : σ → Prop)
    (hpres : ∀ a t s, Inv s → ∀ z ∈ support (((impl a t).run).run s),
      z.1.isSome → Inv z.2)
    (hused : ∀ a t s, Inv s → used s → ∀ z ∈ support (((impl a t).run).run s),
      z.1.isSome → used z.2)
    (hindep : ∀ t s, Inv s → used s → ∀ a a',
      ((impl a t).run).run s = ((impl a' t).run).run s)
    (oa : OracleComp spec Bool) (a : τ) (s : σ) (hs : Inv s) (hu : used s) :
    Pr[= true | optionRun (impl a) oa s] =
      Pr[= true | optionRun (sampleEachQuery sample impl) oa s] := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure b => simp [optionRun_pure]
  | query_bind t cont ih =>
    rw [optionRun_query_bind, optionRun_query_bind]
    simp only [sampleEachQuery_run, bind_assoc]
    have heq : ∀ a', ((impl a' t).run).run s = ((impl a t).run).run s :=
      fun a' => hindep t s hs hu a' a
    simp_rw [heq]
    simp only [probOutput_bind_const, probFailure_eq_zero, tsub_zero, one_mul]
    apply probOutput_bind_congr
    intro z hz
    cases hr : z.1 with
    | none => simp
    | some answer =>
      have ha : z.1.isSome := by simp [hr]
      simpa [hr] using ih answer z.2 (hpres a t s hs z hz ha) (hused a t s hs hu z hz ha)

/-- Assume every continuing query preserves `Inv` and an established `used`
predicate. On invariant states, `hit = false` gives parameter-independent
query computations; `used` implies `hit = false`; and continuing successors
of a query with `hit = true` satisfy `used`.

For every Boolean adversary and initial invariant state, sampling once
before execution and sampling at each query have equal probabilities of
returning `true`, with terminated executions returning `false`. -/
theorem optionRun_sample_once_eq_sampleEachQuery [Inhabited τ]
    (sample : ProbComp τ) (impl : τ → QueryImpl spec (OptionT (StateT σ ProbComp)))
    (Inv used : σ → Prop) (hit : spec.Domain → σ → Bool)
    (hpres : ∀ a t s, Inv s → ∀ z ∈ support (((impl a t).run).run s),
      z.1.isSome → Inv z.2)
    (hused : ∀ a t s, Inv s → used s → ∀ z ∈ support (((impl a t).run).run s),
      z.1.isSome → used z.2)
    (hindep : ∀ t s, Inv s → hit t s = false → ∀ a a',
      ((impl a t).run).run s = ((impl a' t).run).run s)
    (hnohit : ∀ t s, Inv s → used s → hit t s = false)
    (hfirst : ∀ a t s, Inv s → hit t s = true →
      ∀ z ∈ support (((impl a t).run).run s), z.1.isSome → used z.2)
    (oa : OracleComp spec Bool) (s : σ) (hs : Inv s) :
    Pr[= true | do let a ← sample; optionRun (impl a) oa s] =
      Pr[= true | optionRun (sampleEachQuery sample impl) oa s] := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure b => simp [optionRun_pure]
  | query_bind t cont ih =>
    simp_rw [optionRun_query_bind]
    simp only [sampleEachQuery_run, bind_assoc]
    cases hh : hit t s with
    | false =>
      have heq : ∀ a, ((impl a t).run).run s = ((impl default t).run).run s :=
        fun a => hindep t s hs hh a default
      simp_rw [heq]
      rw [probOutput_bind_bind_swap]
      simp only [probOutput_bind_const, probFailure_eq_zero, tsub_zero, one_mul]
      apply probOutput_bind_congr
      intro z hz
      cases hr : z.1 with
      | none => simp
      | some answer =>
        have ha : z.1.isSome := by simp [hr]
        simpa [hr] using ih answer z.2 (hpres default t s hs z hz ha)
    | true =>
      apply probOutput_bind_congr
      intro a _
      apply probOutput_bind_congr
      intro z hz
      cases hr : z.1 with
      | none => simp
      | some answer =>
        have ha : z.1.isSome := by simp [hr]
        simpa [hr] using optionRun_sampleEachQuery_eq_of_used sample impl Inv used
          hpres hused (fun t s hi hu => hindep t s hi (hnohit t s hi hu))
          (cont answer) a z.2 (hpres a t s hs z hz ha) (hfirst a t s hs hh z hz ha)


/-- Supported-parameter form of one-use sampling. Assume invariant and
used-state preservation for every `a ∈ support sample`; parameter
independence compares supported values, and each continuing first use
establishes `used`. Then eager and per-query sampling have equal acceptance
probabilities for every Boolean adversary and invariant initial state. -/
theorem optionRun_sample_once_eq_sampleEachQuery_of_support
    (sample : ProbComp τ) (impl : τ → QueryImpl spec (OptionT (StateT σ ProbComp)))
    (Inv used : σ → Prop) (hit : spec.Domain → σ → Bool)
    (hpres : ∀ a ∈ support sample, ∀ t s, Inv s →
      ∀ z ∈ support (((impl a t).run).run s), z.1.isSome → Inv z.2)
    (hused : ∀ a ∈ support sample, ∀ t s, Inv s → used s →
      ∀ z ∈ support (((impl a t).run).run s), z.1.isSome → used z.2)
    (hindep : ∀ t s, Inv s → hit t s = false →
      ∀ a ∈ support sample, ∀ a' ∈ support sample,
      ((impl a t).run).run s = ((impl a' t).run).run s)
    (hnohit : ∀ t s, Inv s → used s → hit t s = false)
    (hfirst : ∀ a ∈ support sample, ∀ t s, Inv s → hit t s = true →
      ∀ z ∈ support (((impl a t).run).run s), z.1.isSome → used z.2)
    (oa : OracleComp spec Bool) (s : σ) (hs : Inv s) :
    Pr[= true | do let a ← sample; optionRun (impl a) oa s] =
      Pr[= true | optionRun (sampleEachQuery sample impl) oa s] := by
  classical
  have hne : (support sample).Nonempty := by
    simp [Set.nonempty_iff_ne_empty, ← probFailure_eq_one_iff]
  obtain ⟨a₀, ha₀⟩ := hne
  let adjust (a : τ) := if a ∈ support sample then a else a₀
  have hadjust (a : τ) : adjust a ∈ support sample := by
    dsimp [adjust]
    split <;> assumption
  have hadjust_eq (a : τ) (ha : a ∈ support sample) : adjust a = a := by
    simp [adjust, ha]
  let adjusted := fun a => impl (adjust a)
  let : Inhabited τ := ⟨a₀⟩
  calc
    _ = Pr[= true | do let a ← sample; optionRun (adjusted a) oa s] := by
      apply probOutput_bind_congr
      intro a ha
      simp only [adjusted, hadjust_eq a ha]
    _ = Pr[= true | optionRun (sampleEachQuery sample adjusted) oa s] :=
      optionRun_sample_once_eq_sampleEachQuery sample adjusted Inv used hit
        (fun a => hpres _ (hadjust a))
        (fun a => hused _ (hadjust a))
        (fun t s hi hh a a' => hindep t s hi hh _ (hadjust a) _ (hadjust a'))
        hnohit (fun a => hfirst _ (hadjust a)) oa s hs
    _ = _ := by
      apply probOutput_optionRun_eq_of_state_map
        (sampleEachQuery sample impl) (sampleEachQuery sample adjusted) id (fun _ => True)
      · intros; trivial
      · intro t s _
        simp only [sampleEachQuery_run, id_eq, Prod.map_id, id_map]
        apply evalDist_bind_congr
        intro a ha
        simp only [adjusted, hadjust_eq a ha]
      · trivial

end OracleComp
