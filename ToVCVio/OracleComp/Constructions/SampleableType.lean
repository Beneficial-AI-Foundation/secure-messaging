/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.Constructions.SampleableType
import VCVio.EvalDist.Prod

/-!
# `SampleableType` instance for `Prod`, and uniqueness of the uniform law

Provides `SampleableType (α × β)` from `SampleableType α` and `SampleableType β`,
sampling each component independently, and `evalDist_eq_uniformSample_of_uniform`:
a computation with full support and pointwise-constant output probability is the
uniform sample.
-/

namespace ToVCVio

open OracleComp ENNReal

private lemma selectElem_prod_as_seq (α β : Type) [SampleableType α] [SampleableType β] :
    (do let a ← ($ᵗ α : ProbComp α); let b ← ($ᵗ β : ProbComp β); pure (a, b) :
      ProbComp (α × β)) =
    Prod.mk <$> ($ᵗ α : ProbComp α) <*> ($ᵗ β : ProbComp β) := by
  simp [seq_eq_bind_map, monad_norm]

/-- Uniform sampling on a product decomposes into independent sampling of each component. -/
lemma uniformSample_prod_eq_bind (α β : Type) [SampleableType α] [SampleableType β] :
    ($ᵗ (α × β) : ProbComp (α × β)) = (do
      let a ← ($ᵗ α : ProbComp α)
      let b ← ($ᵗ β : ProbComp β)
      pure (a, b)) := by
  change Prod.mk <$> ($ᵗ α : ProbComp α) <*> ($ᵗ β : ProbComp β) = _
  exact (selectElem_prod_as_seq α β).symm

/-- Let `oa : ProbComp β` output every element of `β` (`hsupp`) and give any two elements the
same probability (`huni : Pr[= x | oa] = Pr[= y | oa]`). Then `oa` has the same distribution
as the uniform sample: `evalDist oa = evalDist ($ᵗ β)`. -/
theorem evalDist_eq_uniformSample_of_uniform {β : Type} [SampleableType β]
    (oa : ProbComp β) (hsupp : ∀ x : β, x ∈ support oa)
    (huni : ∀ x y : β, Pr[= x | oa] = Pr[= y | oa]) :
    evalDist oa = evalDist ($ᵗ β) := by
  let : Fintype β := Fintype.ofFinite β
  refine evalDist_ext fun x => ?_
  have h2 : Pr[= x | ($ᵗ β)] = (Fintype.card β : ℝ≥0∞)⁻¹ :=
    probOutput_uniformSample β x
  let h : SampleableType β := ⟨oa, hsupp, huni⟩
  have h1 : Pr[= x | oa] = (Fintype.card β : ℝ≥0∞)⁻¹ :=
    probOutput_uniformSample (hα := h) β x
  exact h1.trans h2.symm

end ToVCVio
