/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.Constructions.SampleableType
import VCVio.EvalDist.Prod

/-!
# Uniform sampling on products, and uniqueness of the uniform law

`uniformSample_prod_eq_bind` unfolds upstream's `SampleableType (α × β)` instance
into two independent component samples, and `evalDist_eq_uniformSample_of_uniform`
shows that a computation with full support and pointwise-constant output
probability is the uniform sample.
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

/-- Let `oa : ProbComp β` give any two elements the same probability
(`huni : Pr[= x | oa] = Pr[= y | oa]`). Then `oa` has the same distribution
as the uniform sample: `𝒮[oa] = 𝒮[$ᵗ β]`. -/
theorem evalDist_eq_uniformSample_of_uniform {β : Type} [SampleableType β]
    (oa : ProbComp β) (huni : ∀ x y : β, Pr[= x | oa] = Pr[= y | oa]) :
    𝒮[oa] = 𝒮[$ᵗ β] := by
  let : Fintype β := Fintype.ofFinite β
  refine evalSPMF_ext fun x => ?_
  rw [probOutput_uniformSample β x]
  have hsum : ∑ y : β, Pr[= y | oa] = 1 := sum_probOutput_eq_one (by simp)
  simp only [huni _ x, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hsum)

end ToVCVio
