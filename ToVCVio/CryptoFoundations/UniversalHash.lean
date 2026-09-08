/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.Constructions.SampleableType

/-!
# Almost-XOR-universal hash families

Generic almost-XOR-universal (AXU) predicate for keyed hash families, stated via
`probOutput` over `ProbComp`: a family `hash : K → D → T` is `ε`-AXU when for every
pair of distinct domain points the XOR of their hashes under a uniformly random key
hits any fixed offset `Δ` with probability at most `ε`.

The offset `Δ = 0` is deliberately admitted (no `Δ ≠ 0` side condition): the zero
offset is exactly what charges same-tag forgeries on distinct messages, so excluding
it would silently weaken any MAC/AEAD authenticity bound built on the predicate.

## Main Definitions

- `IsAlmostXorUniversal hash ε` — the `ε`-AXU predicate.
- `IsAlmostXorUniversal.card_inv_le` — the generic floor: any `ε` witnessing the
  predicate at a domain with two distinct points satisfies `(Fintype.card T)⁻¹ ≤ ε`.
-/

open OracleComp OracleSpec ENNReal

/-- A keyed hash family `hash : K → D → T` is `ε`-almost-XOR-universal when, for
every pair of distinct domain points `x ≠ y` and every offset `Δ` (including
`Δ = 0`), the probability over a uniformly random key that the two hashes XOR to
`Δ` is at most `ε`. -/
def IsAlmostXorUniversal {K D T : Type} [SampleableType K] [DecidableEq T] [XorOp T]
    (hash : K → D → T) (ε : ℝ≥0∞) : Prop :=
  ∀ x y : D, x ≠ y → ∀ Δ : T,
    Pr[= Δ | (fun k => hash k x ^^^ hash k y) <$> ($ᵗ K)] ≤ ε

/-- Sanity check: the predicate elaborates at the GHASH-style instantiation, with
`BitVec 128` keys and tags (instances resolve; type-check only). -/
example (hash : BitVec 128 → BitVec 128 → BitVec 128) : Prop :=
  IsAlmostXorUniversal hash (2 ^ (128 : ℕ) : ℝ≥0∞)⁻¹

/-- Sanity check: the predicate elaborates at a `Prod` domain, as used by GCM where
the domain is (supported AAD) × (bit-vector ciphertext) (type-check only). -/
example (hash : BitVec 128 → List (BitVec 8) × BitVec 256 → BitVec 128) : Prop :=
  IsAlmostXorUniversal hash (2 ^ (128 : ℕ) : ℝ≥0∞)⁻¹

/-- Generic floor on the AXU bound: if `hash` is `ε`-almost-XOR-universal and the
domain has two distinct points, then `ε` is at least `(Fintype.card T)⁻¹`. At any
fixed pair `x ≠ y` the offset probabilities sum to `1` (the mapped uniform sample
never fails), and each is at most `ε`, so `1 ≤ card T * ε`.

This is what lets an authenticity bound built on the predicate be `q · ε` alone,
with no separate `(card T)⁻¹` guessing term. -/
theorem IsAlmostXorUniversal.card_inv_le {K D T : Type} [SampleableType K]
    [DecidableEq T] [XorOp T] [Fintype T] {hash : K → D → T} {ε : ℝ≥0∞}
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
