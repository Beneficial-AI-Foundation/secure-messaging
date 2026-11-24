/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import VCVio.ProgramLogic.Relational.SimulateQ.UntilBad
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Output-Projected Identical-Until-Bad

VCVio's `measureETVDist_simulateQ_run'_le_prEvent_bad` bounds the total variation distance
between the outputs of two simulations whose implementations agree on every event until a
monotone bad predicate holds. `measureTVDist_simulateQ_le_prEvent_output_bad_base` specialises
it to a bad flag stored next to the state and to agreement stated pointwise on good-to-good
transitions.

`prEvent_simulateQ_run_and_not_bad_eq_of_inv` and `prEvent_simulateQ_run_bad_eq_of_inv` are
VCVio's `prEvent_simulateQ_run_and_not_bad_eq` and `prEvent_simulateQ_run_bad_eq` with a state
invariant: the two implementations need to agree, and to keep bad states bad, only on states
that satisfy the invariant. `ToVCVio.OracleComp.SimSemantics.StateT.IdenticalUntilBadInvariant`
bounds the distance of the output events under an invariant. The two theorems here give
equalities, for events of the output and the final state.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace OracleComp.ProgramLogic.Relational

variable {σ : Type} {ι ι₂ : Type} {spec : OracleSpec ι} {spec₂ : OracleSpec ι₂}
  [OracleSpec.AnswerMeasure spec₂] {α : Type}

/-- **Identical until bad, output-bad flag, decoupled base monad.**

The adversary spec `spec` folded by `simulateQ` is independent of the base monad
`OracleComp spec₂`. The implementations need only agree on non-bad output
transitions from non-bad input states, and the bad flag must remain set once it
fires. The observable output distance is then bounded by the bad-event probability
in the first simulation. -/
theorem measureTVDist_simulateQ_le_prEvent_output_bad_base [MeasurableSpace α]
    [∀ t, Finite (spec₂.Range t)]
    (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec₂)))
    (oa : OracleComp spec α) (s₀ : σ)
    (h_agree_good : ∀ (t : spec.Domain) (s : σ) (u : spec.Range t) (s' : σ),
      Pr{let x ← (impl₁ t).run (s, false)}[x = (u, (s', false))] =
        Pr{let x ← (impl₂ t).run (s, false)}[x = (u, (s', false))])
    (h_mono₁ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (h_mono₂ : ∀ (t : spec.Domain) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((impl₂ t).run p), z.2.2 = true) :
    measureTVDist ((simulateQ impl₁ oa).run' (s₀, false))
        ((simulateQ impl₂ oa).run' (s₀, false))
      ≤ Pr{let z ← (simulateQ impl₁ oa).run (s₀, false)}[z.2.2 = true].toReal := by
  have h_agree : ∀ t (p : σ × Bool), ¬p.2 = true → ∀ q : spec.Range t × σ × Bool → Prop,
      Pr{let z ← (impl₁ t).run p}[q z ∧ ¬z.2.2 = true] =
        Pr{let z ← (impl₂ t).run p}[q z ∧ ¬z.2.2 = true] := by
    rintro t ⟨s, b⟩ hb q
    obtain rfl : b = false := by simpa only [Bool.not_eq_true] using hb
    exact prEvent_and_not_flag_eq_of_forall_prEvent_eq (h_agree_good t s) q
  rw [measureTVDist_eq_toReal_measureETVDist]
  exact ENNReal.toReal_mono (prEvent_ne_top _)
    (measureETVDist_simulateQ_run'_le_prEvent_bad impl₁ impl₂ (fun p => p.2 = true) h_agree
      h_mono₁ h_mono₂ oa (s₀, false))

section Inv

variable {ι : Type} {spec : OracleSpec ι} {ι' : Type} {spec' : OracleSpec ι'} {σ α : Type}

/-- `impl` on the states that satisfy `Inv`. On the other states it answers as `impl` but keeps
the state. -/
private def restrictInv (impl : QueryImpl spec (StateT σ (OracleComp spec'))) (Inv : σ → Prop)
    [DecidablePred Inv] : QueryImpl spec (StateT σ (OracleComp spec')) :=
  fun t => StateT.mk fun s =>
    if Inv s then (impl t).run s else (fun z => (z.1, s)) <$> (impl t).run s

/-- Let `impl` keep `Inv`. Then from a state with `Inv`, `restrictInv impl Inv` and `impl` give
the same simulation. -/
private theorem simulateQ_restrictInv_run (impl : QueryImpl spec (StateT σ (OracleComp spec')))
    (Inv : σ → Prop) [DecidablePred Inv]
    (hinv : ∀ t s, Inv s → ∀ z ∈ support ((impl t).run s), Inv z.2)
    (oa : OracleComp spec α) (s₀ : σ) (hs₀ : Inv s₀) :
    (simulateQ (restrictInv impl Inv) oa).run s₀ = (simulateQ impl oa).run s₀ := by
  have h := OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv' (restrictInv impl Inv) impl
    Inv id (fun t s hs z hz => by
      simp only [restrictInv, StateT.run_mk, hs, ↓reduceIte] at hz
      exact hinv t s hs z hz)
    (fun t s hs => by simp only [restrictInv, StateT.run_mk, hs, ↓reduceIte, Prod.map_id, id_map,
      id_eq]) oa s₀ hs₀
  simpa only [Prod.map_id, id_map, id_eq] using h

variable [OracleSpec.AnswerMeasure spec']

/-- The hypotheses of `prEvent_simulateQ_run_and_not_bad_eq` for `restrictInv impl₁ Inv` and
`restrictInv impl₂ Inv`, with `bad ∨ ¬Inv` as the bad predicate. -/
private theorem restrictInv_untilBad (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec')))
    (Inv bad : σ → Prop) [DecidablePred Inv]
    (h_agree : ∀ t s, Inv s → ¬bad s → ∀ q : spec.Range t × σ → Prop,
      Pr{let z ← (impl₁ t).run s}[q z ∧ ¬bad z.2] =
        Pr{let z ← (impl₂ t).run s}[q z ∧ ¬bad z.2])
    (h_mono₁ : ∀ t s, Inv s → bad s → ∀ z ∈ support ((impl₁ t).run s), bad z.2)
    (h_mono₂ : ∀ t s, Inv s → bad s → ∀ z ∈ support ((impl₂ t).run s), bad z.2) :
    (∀ t s, ¬(bad s ∨ ¬Inv s) → ∀ q : spec.Range t × σ → Prop,
      Pr{let z ← (restrictInv impl₁ Inv t).run s}[q z ∧ ¬(bad z.2 ∨ ¬Inv z.2)] =
        Pr{let z ← (restrictInv impl₂ Inv t).run s}[q z ∧ ¬(bad z.2 ∨ ¬Inv z.2)]) ∧
    (∀ t s, (bad s ∨ ¬Inv s) →
      ∀ z ∈ support ((restrictInv impl₁ Inv t).run s), bad z.2 ∨ ¬Inv z.2) ∧
    (∀ t s, (bad s ∨ ¬Inv s) →
      ∀ z ∈ support ((restrictInv impl₂ Inv t).run s), bad z.2 ∨ ¬Inv z.2) := by
  have hmono (impl : QueryImpl spec (StateT σ (OracleComp spec')))
      (h_mono : ∀ t s, Inv s → bad s → ∀ z ∈ support ((impl t).run s), bad z.2) :
      ∀ t s, (bad s ∨ ¬Inv s) →
        ∀ z ∈ support ((restrictInv impl Inv t).run s), bad z.2 ∨ ¬Inv z.2 := by
    intro t s hs z hz
    by_cases hi : Inv s
    · simp only [restrictInv, StateT.run_mk, hi, ↓reduceIte] at hz
      exact .inl (h_mono t s hi (hs.resolve_right (not_not.mpr hi)) z hz)
    · simp only [restrictInv, StateT.run_mk, hi, ↓reduceIte, support_map, Set.mem_image] at hz
      obtain ⟨y, -, rfl⟩ := hz
      exact .inr hi
  refine ⟨fun t s hs q => ?_, hmono impl₁ h_mono₁, hmono impl₂ h_mono₂⟩
  have hi : Inv s := not_not.mp fun h => hs (.inr h)
  have hb : ¬bad s := fun h => hs (.inl h)
  simp only [restrictInv, StateT.run_mk, hi, ↓reduceIte]
  have hcongr (mx : OracleComp spec' (spec.Range t × σ)) :
      Pr{let z ← mx}[q z ∧ ¬(bad z.2 ∨ ¬Inv z.2)] =
        Pr{let z ← mx}[(q z ∧ Inv z.2) ∧ ¬bad z.2] :=
    prEvent_congr mx _ _ fun z => by tauto
  rw [hcongr, hcongr]
  exact h_agree t s hi hb _

/-- **Identical until bad, with an invariant.** Let two implementations keep `Inv`, agree on
good-to-good steps from states with `Inv`, and keep bad states with `Inv` bad. Then from a state
with `Inv`, their simulations give every event the same probability away from a bad final
state. -/
theorem prEvent_simulateQ_run_and_not_bad_eq_of_inv
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec'))) (Inv bad : σ → Prop)
    (hinv₁ : ∀ t s, Inv s → ∀ z ∈ support ((impl₁ t).run s), Inv z.2)
    (hinv₂ : ∀ t s, Inv s → ∀ z ∈ support ((impl₂ t).run s), Inv z.2)
    (h_agree : ∀ t s, Inv s → ¬bad s → ∀ q : spec.Range t × σ → Prop,
      Pr{let z ← (impl₁ t).run s}[q z ∧ ¬bad z.2] =
        Pr{let z ← (impl₂ t).run s}[q z ∧ ¬bad z.2])
    (h_mono₁ : ∀ t s, Inv s → bad s → ∀ z ∈ support ((impl₁ t).run s), bad z.2)
    (h_mono₂ : ∀ t s, Inv s → bad s → ∀ z ∈ support ((impl₂ t).run s), bad z.2)
    (oa : OracleComp spec α) (s₀ : σ) (hs₀ : Inv s₀) (p : α × σ → Prop) :
    Pr{let z ← (simulateQ impl₁ oa).run s₀}[p z ∧ ¬bad z.2] =
      Pr{let z ← (simulateQ impl₂ oa).run s₀}[p z ∧ ¬bad z.2] := by
  classical
  obtain ⟨h_agree', h_mono₁', h_mono₂'⟩ :=
    restrictInv_untilBad impl₁ impl₂ Inv bad h_agree h_mono₁ h_mono₂
  have h := prEvent_simulateQ_run_and_not_bad_eq (restrictInv impl₁ Inv) (restrictInv impl₂ Inv)
    (fun s => bad s ∨ ¬Inv s) h_agree' h_mono₁' h_mono₂' oa s₀ p
  rw [simulateQ_restrictInv_run impl₁ Inv hinv₁ oa s₀ hs₀,
    simulateQ_restrictInv_run impl₂ Inv hinv₂ oa s₀ hs₀] at h
  have hcongr (impl : QueryImpl spec (StateT σ (OracleComp spec')))
      (hinv : ∀ t s, Inv s → ∀ z ∈ support ((impl t).run s), Inv z.2) :
      Pr{let z ← (simulateQ impl oa).run s₀}[p z ∧ ¬(bad z.2 ∨ ¬Inv z.2)] =
        Pr{let z ← (simulateQ impl oa).run s₀}[p z ∧ ¬bad z.2] :=
    prEvent_congr_of_support _ _ _ fun z hz => by
      have := simulateQ_run_preserves_inv_of_query impl Inv hinv oa s₀ hs₀ z hz
      tauto
  rwa [hcongr impl₁ hinv₁, hcongr impl₂ hinv₂] at h

/-- **Identical until bad, with an invariant.** Under the hypotheses of
`prEvent_simulateQ_run_and_not_bad_eq_of_inv`, the two simulations end in a bad state with the
same probability. -/
theorem prEvent_simulateQ_run_bad_eq_of_inv
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec'))) (Inv bad : σ → Prop)
    (hinv₁ : ∀ t s, Inv s → ∀ z ∈ support ((impl₁ t).run s), Inv z.2)
    (hinv₂ : ∀ t s, Inv s → ∀ z ∈ support ((impl₂ t).run s), Inv z.2)
    (h_agree : ∀ t s, Inv s → ¬bad s → ∀ q : spec.Range t × σ → Prop,
      Pr{let z ← (impl₁ t).run s}[q z ∧ ¬bad z.2] =
        Pr{let z ← (impl₂ t).run s}[q z ∧ ¬bad z.2])
    (h_mono₁ : ∀ t s, Inv s → bad s → ∀ z ∈ support ((impl₁ t).run s), bad z.2)
    (h_mono₂ : ∀ t s, Inv s → bad s → ∀ z ∈ support ((impl₂ t).run s), bad z.2)
    (oa : OracleComp spec α) (s₀ : σ) (hs₀ : Inv s₀) :
    Pr{let z ← (simulateQ impl₁ oa).run s₀}[bad z.2] =
      Pr{let z ← (simulateQ impl₂ oa).run s₀}[bad z.2] := by
  have h := prEvent_simulateQ_run_and_not_bad_eq_of_inv impl₁ impl₂ Inv bad hinv₁ hinv₂ h_agree
    h_mono₁ h_mono₂ oa s₀ hs₀ fun _ => True
  simp only [true_and] at h
  have hc (impl : QueryImpl spec (StateT σ (OracleComp spec'))) :
      Pr{let z ← (simulateQ impl oa).run s₀}[bad z.2] =
        1 - Pr{let z ← (simulateQ impl oa).run s₀}[¬bad z.2] := by
    rw [prEvent_not_eq_one_sub, ENNReal.sub_sub_cancel ENNReal.one_ne_top (prEvent_le_one _)]
  rw [hc impl₁, hc impl₂, h]

end Inv

end OracleComp.ProgramLogic.Relational
