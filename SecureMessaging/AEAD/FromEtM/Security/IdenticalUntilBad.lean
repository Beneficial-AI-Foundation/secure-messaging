/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.ProgramLogic.Relational.IdenticalUntilBad

/-!
# Identical-until-bad, `ProbComp` base (EtM call-site corollary)

The generic, base-monad-decoupled identical-until-bad lemma
`tvDist_simulateQ_le_probEvent_output_bad_base` lives in the upstream-candidate brick
`ToVCVio.ProgramLogic.Relational.IdenticalUntilBad` (it strictly generalizes VCVio's
`tvDist_simulateQ_le_probEvent_output_bad` by threading the base monad as an independent `spec₂`).

This file keeps only the `spec₂ := unifSpec` specialization the EtM authenticity hop consumes: its
game oracles fully resolve the encrypt/decrypt oracles down to `ProbComp = OracleComp unifSpec`, so
the base monad is `ProbComp`. Per the upstreaming plan, only the general `spec₂` form is proposed to
VCVio; this `ProbComp` corollary stays local at the call site.
-/

open OracleComp OracleSpec ENNReal

namespace etmAEAD

variable {σ : Type} {ι : Type} {spec : OracleSpec ι} {α : Type}

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
  OracleComp.ProgramLogic.Relational.tvDist_simulateQ_le_probEvent_output_bad_base
    impl₁ impl₂ oa s₀ h_agree_good h_mono₁ h_mono₂

end etmAEAD
