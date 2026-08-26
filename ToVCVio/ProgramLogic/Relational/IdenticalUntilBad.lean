/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# Output-Projected Identical-Until-Bad

VCVio's `tvDist_simulateQ_run_le_probEvent_output_bad` bounds the total variation
distance between the joint output-and-state distributions of two simulations whose
implementations agree until a monotone bad flag fires. This file supplies the
output-only corollary used by SecureMessaging: project both runs with `StateT.run'`
and apply data processing for total variation distance.
-/

open OracleComp OracleSpec ENNReal

namespace OracleComp.ProgramLogic.Relational

variable {σ : Type} {ι ι₂ : Type} {spec : OracleSpec ι} {spec₂ : OracleSpec ι₂}
  [IsUniformSpec spec₂] {α : Type}

/-- **Identical until bad, output-bad flag, decoupled base monad.**

The adversary spec `spec` folded by `simulateQ` is independent of the base monad
`OracleComp spec₂`. The implementations need only agree on non-bad output
transitions from non-bad input states, and the bad flag must remain set once it
fires. The observable output distance is then bounded by the bad-event probability
in the first simulation.

This is the output projection of VCVio's heterogeneous joint-distribution theorem
`tvDist_simulateQ_run_le_probEvent_output_bad`. -/
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
  calc
    tvDist ((simulateQ impl₁ oa).run' (s₀, false))
        ((simulateQ impl₂ oa).run' (s₀, false))
      ≤ tvDist ((simulateQ impl₁ oa).run (s₀, false))
          ((simulateQ impl₂ oa).run (s₀, false)) := by
        rw [StateT.run'_eq, StateT.run'_eq]
        exact tvDist_map_le (m := OracleComp spec₂) (α := α × σ × Bool) (β := α)
          Prod.fst _ _
    _ ≤ Pr[fun z : α × σ × Bool => z.2.2 = true |
          (simulateQ impl₁ oa).run (s₀, false)].toReal :=
      tvDist_simulateQ_run_le_probEvent_output_bad impl₁ impl₂ oa s₀ h_agree_good h_mono₁ h_mono₂

end OracleComp.ProgramLogic.Relational
