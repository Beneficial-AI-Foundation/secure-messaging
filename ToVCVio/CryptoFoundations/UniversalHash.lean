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
