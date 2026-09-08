/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromGCM.Security.Encoding
import ToVCVio.CryptoFoundations.UniversalHash

/-!
# GCM — GHASH AXU statement over the encoding domain

Instantiation of the generic almost-XOR-universal predicate for `GCM.ghash` over
the GHASH encoding domain `SupportedAAD × BitVec L` (Phase 1 criteria 5–6,
GCM-specific half).

The domain is deliberately the *encoding* domain, never raw block lists: raw-list
AXU is false (`ghash h [0, X] = ghash h [X]`, since a leading zero block
contributes nothing), while `gcmEncode` is injective on the AEAD domain
(`gcmEncode_injective`), so the statement below is well-posed.

## Main Definitions

- `GhashIsAXU L ε` — the named instantiation Phase 4 hypothesizes and Phase 7b
  proves: `ghash ∘ gcmEncode` is `ε`-AXU on `SupportedAAD × BitVec L`.
- `aadZero`, `aadEight` — two explicit distinct inhabitants of `SupportedAAD`,
  distinct in the AAD length so the pair separates at every `L`, including `L = 0`.
- `ghashAXU_eps_lower` — the floor `2⁻¹²⁸ ≤ ε` for any witnessing `ε`.
-/

open OracleComp OracleSpec ENNReal

namespace GCM

/-- `ghash` composed with the GHASH encoding is `ε`-almost-XOR-universal on the
AEAD domain `SupportedAAD × BitVec L`.

This is the named statement Phase 4's authenticity brick hypothesizes and
Phase 7b discharges (via the root bound on the difference polynomial, degree
`≤ maxBlocks L` by `gcmEncode_length_le`, nonzero by `gcmEncode_tail_distinct`).
Nothing in Phase 1 proves it — this file only fixes its exact shape and derives
the generic `2⁻¹²⁸` floor below it. -/
def GhashIsAXU (L : ℕ) (ε : ℝ≥0∞) : Prop :=
  IsAlmostXorUniversal
    (fun (H : BitVec 128) (p : SupportedAAD × BitVec L) => ghash H (gcmEncode p.1 p.2)) ε

/-- Sanity check (criterion 5): the instantiation elaborates at a generic
ciphertext length `L` — all instance obligations (`SampleableType (BitVec 128)`,
`DecidableEq (BitVec 128)`, `XorOp (BitVec 128)`) resolve by import. -/
example (L : ℕ) (ε : ℝ≥0∞) : Prop := GhashIsAXU L ε

/-- Sanity check (criterion 5): the instantiation elaborates at `L = 0`, where
`BitVec 0` is a `Unique` type and only the AAD component can separate domain
points. -/
example (ε : ℝ≥0∞) : Prop := GhashIsAXU 0 ε

/-- Sanity check: `GhashIsAXU` unfolds to the generic predicate at the intended
hash family, verbatim. -/
example (L : ℕ) (ε : ℝ≥0∞) :
    GhashIsAXU L ε =
      IsAlmostXorUniversal
        (fun (H : BitVec 128) (p : SupportedAAD × BitVec L) =>
          ghash H (gcmEncode p.1 p.2)) ε :=
  rfl

/-! ## Witnessed pair

Two explicit distinct inhabitants of the AXU domain, distinct in the AAD
component: at `L = 0` the ciphertext component lives in the `Unique` type
`BitVec 0`, so only the AAD can separate a pair. -/

/-- The empty AAD (`lenA = 0`). -/
def aadZero : SupportedAAD := ⟨⟨0, 0⟩, by norm_num, by norm_num⟩

/-- A one-byte zero AAD (`lenA = 8`). -/
def aadEight : SupportedAAD := ⟨⟨8, 0⟩, by norm_num, by norm_num⟩

/-- The witnesses are distinct: their AAD bit-lengths differ (`0 ≠ 8`), so no
`HEq` reasoning on the payloads is needed. -/
theorem aadZero_ne_aadEight : aadZero ≠ aadEight := by
  intro h
  have h' : (0 : ℕ) = 8 := congrArg (fun a : SupportedAAD => a.1.1) h
  omega

/-- The witnessed domain pair is distinct at every `L`, including `L = 0`: the
first components differ. -/
theorem witness_pair_ne (L : ℕ) :
    ((aadZero, 0) : SupportedAAD × BitVec L) ≠ (aadEight, 0) :=
  fun h => aadZero_ne_aadEight (congrArg Prod.fst h)

/-! ## The `2⁻¹²⁸` floor (criterion 6) -/

/-- Floor in `Fintype.card` normal form: any `ε` witnessing `GhashIsAXU L ε`
satisfies `(Fintype.card (BitVec 128))⁻¹ ≤ ε`, by the generic
`IsAlmostXorUniversal.card_inv_le` at the witnessed pair. -/
theorem ghashAXU_card_inv_le {L : ℕ} {ε : ℝ≥0∞} (h : GhashIsAXU L ε) :
    (Fintype.card (BitVec 128) : ℝ≥0∞)⁻¹ ≤ ε :=
  IsAlmostXorUniversal.card_inv_le h (witness_pair_ne L)

/-- **The `2⁻¹²⁸` floor** (Phase 1 criterion 6): any `ε` witnessing
`GhashIsAXU L ε` satisfies `2⁻¹²⁸ ≤ ε`.

This floor is why Phase 4's authenticity term is `q_d · ε` with no separate
`2⁻¹²⁸` guessing term: a blind pre-challenge tag guess succeeds with probability
exactly `2⁻¹²⁸ ≤ ε`, so it is already charged to the AXU bound. -/
theorem ghashAXU_eps_lower {L : ℕ} {ε : ℝ≥0∞} (h : GhashIsAXU L ε) :
    ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹ ≤ ε := by
  have hcard : (Fintype.card (BitVec 128) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (128 : ℕ) := by
    rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]
    push_cast
    norm_num
  rw [← hcard]
  exact ghashAXU_card_inv_le h

end GCM
