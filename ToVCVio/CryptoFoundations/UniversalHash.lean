/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.Constructions.SampleableType

/-!
# Almost-XOR-universal hash families

A keyed hash family `hash : K → D → T` is `ε`-almost-XOR-universal (AXU) when, for any two
distinct inputs, the XOR of their hashes under a uniformly random key equals any fixed offset
`Δ` with probability at most `ε`. This is the property of the hash inside a Wegman-Carter
authenticator (`WegmanCarter.lean`).

The offset `Δ = 0` is admitted on purpose. The forgery bound applies the predicate at the offset
`tag ^^^ challengeTag`, which is `0` exactly when a forgery reuses the challenge tag on a
different message; a predicate excluding `Δ = 0` would leave that forgery uncovered.
-/

open OracleComp OracleSpec ENNReal

namespace ToVCVio

/-- `hash` is `ε`-almost-XOR-universal: for distinct inputs `x ≠ y` and any offset `Δ`,
`hash k x ^^^ hash k y = Δ` with probability at most `ε` over a uniform key `k`. The offset
`Δ = 0` is not excluded; the module header says why. -/
def IsAlmostXorUniversal {K D T : Type} [SampleableType K] [XorOp T]
    (hash : K → D → T) (ε : ℝ≥0∞) : Prop :=
  ∀ x y : D, x ≠ y → ∀ Δ : T,
    Pr[= Δ | (fun k => hash k x ^^^ hash k y) <$> ($ᵗ K)] ≤ ε

/-- An AXU bound is at least `1 / |T|` once the domain has two distinct points: at a fixed
pair the offset probabilities sum to `1` and each is at most `ε`. This discharges the `hfloor`
hypothesis of `probEvent_wcInst_forge_le` for every hash whose domain has two points. -/
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

/-- Counting form of AXU: if at most `d` keys send any fixed distinct pair to any fixed
offset, the family is `d / |K|`-AXU. A consumer proves a `Finset.card` bound and never touches
probabilities. -/
theorem isAlmostXorUniversal_of_card_le {K D T : Type} [SampleableType K] [Fintype K]
    [XorOp T] [DecidableEq T] {hash : K → D → T} {d : ℕ}
    (h : ∀ x y : D, x ≠ y → ∀ Δ : T,
      (Finset.univ.filter (fun k : K => hash k x ^^^ hash k y = Δ)).card ≤ d) :
    IsAlmostXorUniversal hash ((d : ℝ≥0∞) / Fintype.card K) := by
  intro x y hxy Δ
  rw [← probEvent_eq_eq_probOutput, probEvent_map, Function.comp_def, probEvent_uniformSample]
  exact ENNReal.div_le_div_right (by exact_mod_cast h x y hxy Δ) _

end ToVCVio
