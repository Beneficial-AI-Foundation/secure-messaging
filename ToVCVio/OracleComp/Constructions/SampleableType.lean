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
probability is the uniform sample. `probOutput_true_bitGuess_eq_half` says that guessing a
uniform bit succeeds with probability exactly `1 / 2` when the bit does not affect the
distribution of the guesser's input.
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

/-- Guessing a uniform bit `b` from a sample of `dist par b` succeeds with probability exactly
`1 / 2` when `dist par true` and `dist par false` have the same distribution for every `par`.
This is the shape of an indistinguishability experiment with a setup phase (sampling `par`)
whose real and ideal distributions coincide, so its guessing advantage is `0`. -/
lemma probOutput_true_bitGuess_eq_half {Par X : Type} (setup : ProbComp Par)
    (dist : Par → Bool → ProbComp X) (adversary : Par → X → ProbComp Bool)
    (h : ∀ par, 𝒟[dist par true] = 𝒟[dist par false]) :
    Pr[= true | do
      let b ← $ᵗ Bool
      let par ← setup
      let x ← dist par b
      let b' ← adversary par x
      return b == b'] = 1 / 2 := by
  have hf : 𝒟[do let par ← setup; let x ← dist par true; adversary par x] =
      𝒟[do let par ← setup; let x ← dist par false; adversary par x] := by
    simp only [evalDist_bind, h]
  have := probOutput_decide_eq_uniformBool_half
    (fun b => do let par ← setup; let x ← dist par b; adversary par x) hf
  simpa [bind_assoc, Bool.beq_eq_decide_eq] using this

end ToVCVio
