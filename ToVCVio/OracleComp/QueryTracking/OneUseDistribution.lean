/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.OracleComp.QueryTracking.OneUseSampling

/-!
# One-use sampling from equality of query distributions

**Parameters.** Fix a sampler, a parameterized terminating oracle family,
invariant and used-state predicates, and a query-dependent use test.

**Assumptions.** For each supported parameter, continuing queries preserve
the invariant and established used states. Outside use, supported parameters
give equal joint distributions of response and successor. Used states have
no further uses; a continuing first use establishes the used predicate.

**Conclusion.** For every Boolean adversary and invariant initial state,
eager sampling and per-query sampling have equal acceptance probabilities.
The distribution premise permits a query to perform parameter-dependent
sampling whose result is discarded before returning its response and state.
-/

open OracleSpec ENNReal

namespace OracleComp

variable {ι σ τ : Type} {spec : OracleSpec ι}

/-- Assume supported parameters preserve `Inv` and `used` on continuing
queries, and all supported parameters have equal query distributions on
invariant used states. Then fixing any supported parameter and resampling
it at every query give equal acceptance probabilities from those states. -/
theorem optionRun_sampleEachQuery_eq_of_used_evalDist
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

/-- Assume invariant and used-state preservation for supported parameters,
equality of query distributions outside use, absence of use in used states,
and establishment of `used` at each continuing first use. For every Boolean
adversary and invariant initial state, eager and per-query parameter sampling
have equal acceptance probabilities. Terminated executions return `false`. -/
theorem optionRun_sample_once_eq_sampleEachQuery_of_evalDist
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
        simpa only [hr] using optionRun_sampleEachQuery_eq_of_used_evalDist sample impl Inv used
          hpres hused (fun t s hi hu => hindep t s hi (hnohit t s hi hu))
          (cont answer) a ha z.2 (hpres a ha t s hs z hz hc)
          (hfirst a ha t s hs hh z hz hc)

end OracleComp
