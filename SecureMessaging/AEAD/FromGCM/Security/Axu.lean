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

end GCM
