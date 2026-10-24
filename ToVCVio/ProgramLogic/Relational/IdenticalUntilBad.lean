/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# Output-Projected Identical-Until-Bad

VCVio's `measureETVDist_simulateQ_run'_le_prEvent_bad` bounds the total variation distance
between the outputs of two simulations whose implementations agree on every event until a
monotone bad predicate holds. The theorem below specialises it to a bad flag stored next to the
state and to agreement stated pointwise on good-to-good transitions.
-/

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

end OracleComp.ProgramLogic.Relational
