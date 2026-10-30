/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Uniform choice of an index in `{1, …, q}`

Hybrid arguments over `q` steps often build one reduction that first picks a step uniformly at
random and then runs the reduction for that step. `epochChoice q` is this random choice. For
`q > 0`, the probability of an event of such a reduction is the average over `i ∈ {1, …, q}` of
its probability for step `i` (`toReal_prEvent_epochChoice_bind`).
-/

@[expose] public section

namespace ToVCVio

/-- Draws an index uniformly from `{1, …, q}` when `q > 0`, and returns `1` when `q = 0`. -/
def epochChoice (q : ℕ) : ProbComp ℕ :=
  if hq : q = 0 then pure 1
  else
    letI : NeZero q := ⟨hq⟩
    (fun i : Fin q => i.val + 1) <$> ($ᵗ (Fin q) : ProbComp (Fin q))

/-- For `q ≠ 0`, the probability of an event after `e ← epochChoice q; X e` is the average of its
probabilities for `X 1, …, X q`. -/
theorem toReal_prEvent_epochChoice_bind {α : Type} (q : ℕ) (hq : q ≠ 0) (X : ℕ → ProbComp α)
    (p : α → Prop) :
    (Pr{let x ← epochChoice q >>= X}[p x]).toReal =
      (q : ℝ)⁻¹ * ∑ i : Fin q, (Pr{let x ← X (i.val + 1)}[p x]).toReal := by
  let : NeZero q := ⟨hq⟩
  simp only [epochChoice, hq, ↓reduceDIte, bind_map_left, (prEvent_bind_eq_sum_fintype _),
    SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fin, ← Finset.mul_sum]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_sum (fun _ _ => prEvent_ne_top _)]

end ToVCVio
