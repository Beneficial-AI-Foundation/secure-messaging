/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.Constructions.SampleableType

/-!
# Almost-XOR-universal hash families

The definition of an `ε`-almost-XOR-universal (AXU) keyed hash family, the lower bound
`1/|T| ≤ ε`, and a counting criterion for AXU.
-/

open OracleComp OracleSpec ENNReal

namespace ToVCVio

/-- A keyed hash family `hash : K → D → T` is `ε`-almost-XOR-universal (AXU) if, for any fixed
pair of distinct inputs, no particular XOR difference between their hashes occurs with
probability greater than `ε`:

`∀ x ≠ y, ∀ Δ ∈ T, Pr[k ←$ K : hash k x ⊕ hash k y = Δ] ≤ ε`.

Here `x, y ∈ D`, the key `k` is sampled uniformly from `K`, and the same key is used for both
hashes. The value `Δ` is fixed independently of `k`. -/
def IsAlmostXorUniversal {K D T : Type} [SampleableType K] [XorOp T]
    (hash : K → D → T) (ε : ℝ≥0∞) : Prop :=
  ∀ x y : D, x ≠ y → ∀ Δ : T,
    Pr[= Δ | (fun k => hash k x ^^^ hash k y) <$> ($ᵗ K)] ≤ ε

/-- Lower bound on an AXU parameter. If `hash` is `ε`-AXU, its domain `D` contains two distinct
inputs `x ≠ y`, and its output type `T` is finite, then `1/|T| ≤ ε`.

Proof: for a uniform key `k`, the probabilities of the possible values of `hash k x ⊕ hash k y`
sum to `1`, and each is at most `ε` by AXU, so

`1 = ∑ Δ ∈ T, Pr[k ←$ K : hash k x ⊕ hash k y = Δ] ≤ |T| · ε`.

Dividing by `|T|` gives the result. -/
theorem IsAlmostXorUniversal.card_inv_le {K D T : Type} [SampleableType K]
    [XorOp T] [Fintype T] {hash : K → D → T} {ε : ℝ≥0∞}
    (h : IsAlmostXorUniversal hash ε) {x y : D} (hxy : x ≠ y) :
    (Fintype.card T : ℝ≥0∞)⁻¹ ≤ ε := by
  -- The offset probabilities at the fixed pair `(x, y)` sum to `1`.
  have hsum : ∑ Δ : T, Pr[= Δ | (fun k => hash k x ^^^ hash k y) <$> ($ᵗ K)] = 1 :=
    sum_probOutput_eq_one (by simp)
  -- Each summand is at most `ε`, hence `1 ≤ card T * ε`.
  have hone_le : (1 : ℝ≥0∞) ≤ (Fintype.card T : ℝ≥0∞) * ε :=
    calc (1 : ℝ≥0∞)
        = ∑ Δ : T, Pr[= Δ | (fun k => hash k x ^^^ hash k y) <$> ($ᵗ K)] := hsum.symm
      _ ≤ ∑ _Δ : T, ε := Finset.sum_le_sum fun Δ _ => h x y hxy Δ
      _ = (Fintype.card T : ℝ≥0∞) * ε := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- `card T ≠ 0`, else the previous step reads `1 ≤ 0`.
  have hcard : (Fintype.card T : ℝ≥0∞) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hone_le
    exact one_ne_zero (le_antisymm hone_le zero_le)
  -- Cancel `card T` in `ℝ≥0∞` (a natural cast, so never `⊤`).
  calc (Fintype.card T : ℝ≥0∞)⁻¹
      = (Fintype.card T : ℝ≥0∞)⁻¹ * 1 := (mul_one _).symm
    _ ≤ (Fintype.card T : ℝ≥0∞)⁻¹ * ((Fintype.card T : ℝ≥0∞) * ε) :=
        mul_le_mul_right hone_le _
    _ = ε := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hcard (ENNReal.natCast_ne_top _), one_mul]

/-- Counting form of AXU. If for all distinct `x, y : D` and every offset `Δ` at most `d` keys
`k` satisfy `hash k x ⊕ hash k y = Δ`, then `hash` is `d/|K|`-AXU. -/
theorem isAlmostXorUniversal_of_card_le {K D T : Type} [SampleableType K] [Fintype K]
    [XorOp T] [DecidableEq T] {hash : K → D → T} {d : ℕ}
    (h : ∀ x y : D, x ≠ y → ∀ Δ : T,
      (Finset.univ.filter (fun k : K => hash k x ^^^ hash k y = Δ)).card ≤ d) :
    IsAlmostXorUniversal hash ((d : ℝ≥0∞) / Fintype.card K) := by
  intro x y hxy Δ
  rw [← probEvent_eq_eq_probOutput, probEvent_map, Function.comp_def, probEvent_uniformSample]
  exact ENNReal.div_le_div_right (by exact_mod_cast h x y hxy Δ) _

end ToVCVio
