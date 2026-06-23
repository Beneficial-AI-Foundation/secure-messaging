/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# Identical-until-bad with a decoupled base monad (missing VCVio brick)

VCVio's fundamental lemma of game playing, `tvDist_simulateQ_le_probEvent_output_bad`
(`VCVio/ProgramLogic/Relational/SimulateQ.lean`), is stated for query implementations whose
base monad is `OracleComp spec` for the **same** `spec` the adversary queries:

```
impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec))
oa : OracleComp spec α
```

In our setting the adversary `adv` is over a *combined* spec (`aeadOneTimeCCASpec = unifSpec +
encrypt + decrypt`), but the game oracle implementation **fully resolves** the encrypt/decrypt
oracles, leaving the base monad `ProbComp = OracleComp unifSpec`. So the adversary-spec and the
base-spec genuinely differ, and the VCVio lemma does not apply as stated.

This file states the **base-monad-decoupled** variant: the adversary spec `spec` (folded by
`simulateQ`) is independent of the base monad `OracleComp spec₂` (for an arbitrary `spec₂`). The
proof is the *same* induction as the VCVio lemma — only the base monad is threaded as a separate
`spec₂` instead of being forced equal to `spec`. It therefore strictly generalizes the VCVio
lemma:

* `spec₂ := spec`     recovers VCVio's `tvDist_simulateQ_le_probEvent_output_bad`;
* `spec₂ := unifSpec` gives the `ProbComp`-base corollary the EtM authenticity hop consumes
  (`tvDist_simulateQ_le_probEvent_output_bad_probComp`).

## Status

`tvDist_simulateQ_le_probEvent_output_bad_base` (and the `_probComp` corollary) are proved
(sorry-free), together with the three private helpers. They are a mechanical decoupling of an
existing VCVio lemma (no new probabilistic content). TODO(upstream): replace the VCVio lemma's
`OracleComp spec` base with an arbitrary `OracleComp spec₂` and delete this brick (the EtM hop
would then call the upstream lemma directly at `spec₂ := unifSpec`).
-/

open OracleComp OracleSpec ENNReal

namespace ToVCVio

/-! ## Ported private helpers (base monad `OracleComp spec₂`)

These three lemmas mirror the private helpers of VCVio's
`tvDist_simulateQ_le_probEvent_output_bad` (`VCVio/ProgramLogic/Relational/SimulateQ.lean`),
with the base monad re-threaded from `OracleComp spec` to an *independent* `OracleComp spec₂`.
The induction is identical; only the base spec is generalized. -/

variable {σ : Type} {ι ι₂ : Type} {spec : OracleSpec ι} {spec₂ : OracleSpec ι₂}
  [IsUniformSpec spec₂] {α : Type}

/-- Once the output bad flag has fired, a simulation started from a bad state never produces a
non-bad output. Decoupled-base port of the corresponding VCVio helper. -/
private lemma probOutput_simulateQ_run_eq_zero_of_bad_base
    (impl : QueryImpl spec (StateT σ (OracleComp spec₂)))
    (bad : σ → Prop)
    (h_mono : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl t).run s), bad x.2)
    (oa : OracleComp spec α) (s₀ : σ) (h_bad : bad s₀)
    (x : α) (s : σ) (hs : ¬bad s) :
    Pr[= (x, s) | (simulateQ impl oa).run s₀] = 0 := by
  induction oa using OracleComp.inductionOn generalizing s₀ with
  | pure a =>
    rw [simulateQ_pure]
    show Pr[= (x, s) | (pure a : StateT σ (OracleComp spec₂) α).run s₀] = 0
    simp only [StateT.run_pure, probOutput_eq_zero_iff, support_pure, Set.mem_singleton_iff,
      Prod.ext_iff, not_and]
    rintro rfl rfl
    exact hs h_bad
  | query_bind t oa ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, probOutput_eq_zero_iff, support_bind, Set.mem_iUnion, exists_prop,
      Prod.exists, not_exists, not_and]
    intro u s' h_mem
    rw [← probOutput_eq_zero_iff]
    exact ih u s' (h_mono t s₀ h_bad (u, s') h_mem)

open scoped Classical in
/-- Two implementations that agree on non-bad output transitions yield equal output
probabilities for any non-bad final state. Decoupled-base port. -/
private lemma probOutput_simulateQ_run_eq_of_not_output_bad_base
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec₂)))
    (h_agree_good : ∀ (t : spec.Domain) (s : σ) (u : spec.Range t) (s' : σ),
      Pr[= (u, (s', false)) | (impl₁ t).run (s, false)] =
        Pr[= (u, (s', false)) | (impl₂ t).run (s, false)])
    (h_mono₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (h_mono₂ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₂ t).run p), z.2.2 = true)
    (oa : OracleComp spec α) (s₀ : σ) (x : α) (s : σ) :
    Pr[= (x, (s, false)) | (simulateQ impl₁ oa).run (s₀, false)] =
      Pr[= (x, (s, false)) | (simulateQ impl₂ oa).run (s₀, false)] := by
  induction oa using OracleComp.inductionOn generalizing s₀ with
  | pure a =>
    simp only [simulateQ_pure]
  | query_bind t oa ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
    refine tsum_congr ?_
    rintro ⟨u, ⟨s', b⟩⟩
    cases b with
    | true =>
      have h₁ : Pr[= (x, (s, false)) | (simulateQ impl₁ (oa u)).run (s', true)] = 0 :=
        probOutput_simulateQ_run_eq_zero_of_bad_base impl₁ (fun p : σ × Bool => p.2 = true)
          h_mono₁ (oa u) (s', true) rfl x (s, false) (by simp)
      have h₂ : Pr[= (x, (s, false)) | (simulateQ impl₂ (oa u)).run (s', true)] = 0 :=
        probOutput_simulateQ_run_eq_zero_of_bad_base impl₂ (fun p : σ × Bool => p.2 = true)
          h_mono₂ (oa u) (s', true) rfl x (s, false) (by simp)
      simp [h₁, h₂]
    | false =>
      rw [h_agree_good t s₀ u s', ih u s']

open scoped Classical in
/-- The probability the bad flag has fired is equal across the two implementations.
Decoupled-base port. -/
private lemma probEvent_output_bad_eq_base
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec₂)))
    (h_agree_good : ∀ (t : spec.Domain) (s : σ) (u : spec.Range t) (s' : σ),
      Pr[= (u, (s', false)) | (impl₁ t).run (s, false)] =
        Pr[= (u, (s', false)) | (impl₂ t).run (s, false)])
    (h_mono₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (h_mono₂ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₂ t).run p), z.2.2 = true)
    (oa : OracleComp spec α) (s₀ : σ) :
    Pr[fun z : α × σ × Bool => z.2.2 = true | (simulateQ impl₁ oa).run (s₀, false)] =
      Pr[fun z : α × σ × Bool => z.2.2 = true | (simulateQ impl₂ oa).run (s₀, false)] := by
  set sim₁ := (simulateQ impl₁ oa).run (s₀, false)
  set sim₂ := (simulateQ impl₂ oa).run (s₀, false)
  have h₁ := probEvent_compl sim₁ (fun z : α × σ × Bool => z.2.2 = true)
  have h₂ := probEvent_compl sim₂ (fun z : α × σ × Bool => z.2.2 = true)
  simp only [NeverFail.probFailure_eq_zero, tsub_zero] at h₁ h₂
  have h_not_eq :
      Pr[fun z : α × σ × Bool => ¬z.2.2 = true | sim₁] =
        Pr[fun z : α × σ × Bool => ¬z.2.2 = true | sim₂] := by
    rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
    refine tsum_congr ?_
    rintro ⟨a, s, b⟩
    by_cases hb : b = true
    · simp [hb]
    · have hb' : b = false := by cases b <;> simp_all
      subst hb'
      simpa using
        probOutput_simulateQ_run_eq_of_not_output_bad_base impl₁ impl₂ h_agree_good
          h_mono₁ h_mono₂ oa s₀ a s
  have hne₁ : Pr[fun z : α × σ × Bool => ¬z.2.2 = true | sim₁] ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top probEvent_le_one
  calc Pr[fun z : α × σ × Bool => z.2.2 = true | sim₁]
      = 1 - Pr[fun z : α × σ × Bool => ¬z.2.2 = true | sim₁] := by
        rw [← h₁]; exact (ENNReal.add_sub_cancel_right hne₁).symm
    _ = 1 - Pr[fun z : α × σ × Bool => ¬z.2.2 = true | sim₂] := by rw [h_not_eq]
    _ = Pr[fun z : α × σ × Bool => z.2.2 = true | sim₂] := by
        rw [← h₂]; exact ENNReal.add_sub_cancel_right
          (ne_top_of_le_ne_top one_ne_top probEvent_le_one)

/-- **Identical until bad, output-bad flag, decoupled base monad.** Base-monad-generalized variant
of VCVio's `tvDist_simulateQ_le_probEvent_output_bad`: the adversary spec `spec` (folded by
`simulateQ`) is independent of the base monad `OracleComp spec₂`. The two implementations need only
agree on **non-bad output transitions** from non-bad input states (they may disagree on the firing
step), and the bad flag must be monotone (once `true`, stays `true`). Then the TV distance between
the two simulations is bounded by the probability the flag fires in `impl₁`.

Instantiating `spec₂ := spec` recovers the VCVio lemma; `spec₂ := unifSpec` gives the `ProbComp`
corollary `tvDist_simulateQ_le_probEvent_output_bad_probComp`. -/
theorem tvDist_simulateQ_le_probEvent_output_bad_base
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec₂)))
    (oa : OracleComp spec α) (s₀ : σ)
    (h_agree_good : ∀ (t : spec.Domain) (s : σ) (u : spec.Range t) (s' : σ),
      Pr[= (u, (s', false)) | (impl₁ t).run (s, false)] =
        Pr[= (u, (s', false)) | (impl₂ t).run (s, false)])
    (h_mono₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (h_mono₂ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₂ t).run p), z.2.2 = true) :
    tvDist ((simulateQ impl₁ oa).run' (s₀, false))
        ((simulateQ impl₂ oa).run' (s₀, false))
      ≤ Pr[fun z : α × σ × Bool => z.2.2 = true |
          (simulateQ impl₁ oa).run (s₀, false)].toReal := by
  -- Same induction as `tvDist_simulateQ_le_probEvent_output_bad`; base monad is `OracleComp spec₂`
  -- rather than `OracleComp spec`. Mechanical decoupling; see module docstring.
  classical
  set sim₁ := (simulateQ impl₁ oa).run (s₀, false)
  set sim₂ := (simulateQ impl₂ oa).run (s₀, false)
  have h_eq : ∀ (z : α × σ × Bool), ¬(z.2.2 = true) → Pr[= z | sim₁] = Pr[= z | sim₂] := by
    rintro ⟨x, s, b⟩ hb
    have hb' : b = false := by cases b <;> simp_all
    subst hb'
    exact probOutput_simulateQ_run_eq_of_not_output_bad_base impl₁ impl₂ h_agree_good
      h_mono₁ h_mono₂ oa s₀ x s
  have h_event_eq :
      Pr[fun z : α × σ × Bool => z.2.2 = true | sim₁] =
        Pr[fun z : α × σ × Bool => z.2.2 = true | sim₂] :=
    probEvent_output_bad_eq_base impl₁ impl₂ h_agree_good h_mono₁ h_mono₂ oa s₀
  have h_tv_joint :
      tvDist sim₁ sim₂ ≤ Pr[fun z : α × σ × Bool => z.2.2 = true | sim₁].toReal :=
    tvDist_le_probEvent_of_probOutput_eq_of_not (mx := sim₁) (my := sim₂)
      (fun z : α × σ × Bool => z.2.2 = true) h_eq h_event_eq
  have h_map :
      tvDist ((simulateQ impl₁ oa).run' (s₀, false))
          ((simulateQ impl₂ oa).run' (s₀, false))
        ≤ tvDist sim₁ sim₂ := by
    simpa [sim₁, sim₂, StateT.run'] using
      (tvDist_map_le (m := OracleComp spec₂) (α := α × σ × Bool) (β := α) Prod.fst sim₁ sim₂)
  exact le_trans h_map h_tv_joint

/-- **Identical until bad, output-bad flag, `ProbComp` base.** The `spec₂ := unifSpec` corollary of
`tvDist_simulateQ_le_probEvent_output_bad_base`, consumed by the EtM authenticity hop (whose game
oracles fully resolve the encrypt/decrypt oracles down to `ProbComp = OracleComp unifSpec`). -/
theorem tvDist_simulateQ_le_probEvent_output_bad_probComp
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) ProbComp))
    (oa : OracleComp spec α) (s₀ : σ)
    (h_agree_good : ∀ (t : spec.Domain) (s : σ) (u : spec.Range t) (s' : σ),
      Pr[= (u, (s', false)) | (impl₁ t).run (s, false)] =
        Pr[= (u, (s', false)) | (impl₂ t).run (s, false)])
    (h_mono₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (h_mono₂ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₂ t).run p), z.2.2 = true) :
    tvDist ((simulateQ impl₁ oa).run' (s₀, false))
        ((simulateQ impl₂ oa).run' (s₀, false))
      ≤ Pr[fun z : α × σ × Bool => z.2.2 = true |
          (simulateQ impl₁ oa).run (s₀, false)].toReal :=
  tvDist_simulateQ_le_probEvent_output_bad_base impl₁ impl₂ oa s₀ h_agree_good h_mono₁ h_mono₂

end ToVCVio
