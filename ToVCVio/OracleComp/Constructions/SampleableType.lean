/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.EvalDist.Prod
public import VCVio.OracleComp.EvalDist.Sum

/-!
# Uniqueness of the uniform law

`evalDistEq_uniformSample_of_uniform` shows that a computation with pointwise-constant output
probability is equal in distribution to the uniform sample. `prEvent_true_bitGuess_eq_half`
says that guessing a uniform bit succeeds with probability exactly `1 / 2` when the bit does
not affect the distribution of the guesser's input.
-/

@[expose] public section

namespace ToVCVio

open OracleComp ENNReal

/-- Let `oa : ProbComp β` give any two elements the same probability
(`huni : Pr[oa = x] = Pr[oa = y]`). Then `oa` is equal in distribution to the uniform sample
`$ᵗ β`. -/
theorem evalDistEq_uniformSample_of_uniform {β : Type} [SampleableType β]
    (oa : ProbComp β) (huni : ∀ x y : β, Pr{let z ← oa}[z = x] = Pr{let z ← oa}[z = y]) :
    oa =ᵈ ($ᵗ β) := by
  let : Fintype β := Fintype.ofFinite β
  refine evalDistEq_of_forall_prEvent_eq_output fun x => ?_
  rw [SampleableType.prEvent_uniformSample_eq_singleton]
  refine ENNReal.eq_inv_of_mul_eq_one_left ?_
  calc Pr{let z ← oa}[z = x] * (Fintype.card β : ℝ≥0∞)
      = ∑ y : β, Pr{let z ← oa}[z = y] := by
        simp only [Finset.sum_congr rfl fun y _ => huni y x, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, mul_comm]
    _ = 1 := by rw [← tsum_fintype (L := .unconditional β)]; exact tsum_prEvent_eq_one oa

/-- Guessing a uniform bit `b` from a sample of `dist par b` succeeds with probability exactly
`1 / 2` when `dist par true` and `dist par false` are equal in distribution for every `par`.
This is the shape of an indistinguishability experiment with a setup phase (sampling `par`)
whose real and ideal distributions coincide, so its guessing advantage is `0`. -/
lemma prEvent_true_bitGuess_eq_half {Par X : Type} (setup : ProbComp Par)
    (dist : Par → Bool → ProbComp X) (adversary : Par → X → ProbComp Bool)
    (h : ∀ par, dist par true =ᵈ dist par false) :
    Pr{let y ← (do
      let b ← $ᵗ Bool
      let par ← setup
      let x ← dist par b
      let b' ← adversary par x
      return b == b')}[y = true] = 1 / 2 := by
  have hf : 𝒟[do let par ← setup; let x ← dist par true; adversary par x] =
      𝒟[do let par ← setup; let x ← dist par false; adversary par x] :=
    (EvalDistEq.bind_right setup fun par => (h par).bind_left _).evalDist_eq
  have := ProbComp.evalDist_decide_eq_uniformBool_half
    (fun b => do let par ← setup; let x ← dist par b; adversary par x) hf
  rw [prEvent_eq_evalDist_singleton]
  simpa [bind_assoc, Bool.beq_eq_decide_eq] using this

end ToVCVio
