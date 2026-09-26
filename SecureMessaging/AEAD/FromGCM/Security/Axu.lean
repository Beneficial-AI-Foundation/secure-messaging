/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromGCM.Security.Encoding
import ToVCVio.CryptoFoundations.UniversalHash
import ToVCVio.OracleComp.Constructions.BitVec

/-!
# GHASH: almost-XOR-universality statement

`GhashIsAXU L ε` says that `ghash ∘ gcmEncode` is `ε`-almost-XOR-universal (AXU) on
`SupportedAAD × BitVec L`: for distinct inputs and any target `Δ`, a uniform key `H` gives
`ghash H (…) ⊕ ghash H (…) = Δ` with probability at most `ε`. The authenticity hop
(`AuthHop.lean`) assumes it; `GhashAXU.lean` proves it from the irreducibility of `nistPoly`,
which `NistIrreducible.lean` supplies.

AXU is stated for `ghash ∘ gcmEncode`, not for `ghash` on raw block lists, where it is false: a
leading zero block is a zero leading coefficient, so `ghash h [0, X] = ghash h [X]` for every
key, and these are distinct inputs with identical hashes. The length block appended by
`gcmEncode` separates such pairs.
-/

open OracleComp OracleSpec ENNReal ToVCVio

namespace GCM

/-- `ghash` composed with the GHASH encoding is `ε`-almost-XOR-universal on the AEAD domain
`SupportedAAD × BitVec L`. -/
def GhashIsAXU (L : ℕ) (ε : ℝ≥0∞) : Prop :=
  IsAlmostXorUniversal
    (fun (H : BitVec 128) (p : SupportedAAD × BitVec L) => ghash H (gcmEncode p.1 p.2)) ε

/-! ## Witnessed pair

Two distinct inhabitants of the AXU domain, differing in the AAD length so that they are
distinct at every `L`, including `L = 0` where `BitVec 0` is a singleton. -/

/-- The empty AAD (`lenA = 0`). -/
def aadZero : SupportedAAD := ⟨⟨0, 0⟩, by norm_num, by norm_num⟩

/-- A one-byte zero AAD (`lenA = 8`). -/
def aadEight : SupportedAAD := ⟨⟨8, 0⟩, by norm_num, by norm_num⟩

theorem aadZero_ne_aadEight : aadZero ≠ aadEight := by
  intro h
  have h' : (0 : ℕ) = 8 := congrArg (fun a : SupportedAAD => a.1.1) h
  omega

theorem witness_pair_ne (L : ℕ) :
    ((aadZero, 0) : SupportedAAD × BitVec L) ≠ (aadEight, 0) :=
  fun h => aadZero_ne_aadEight (congrArg Prod.fst h)

/-! ## The `2⁻¹²⁸` floor -/

theorem ghashAXU_card_inv_le {L : ℕ} {ε : ℝ≥0∞} (h : GhashIsAXU L ε) :
    (Fintype.card (BitVec 128) : ℝ≥0∞)⁻¹ ≤ ε :=
  IsAlmostXorUniversal.card_inv_le h (witness_pair_ne L)

/-- Every AXU bound `ε` of GHASH satisfies `2⁻¹²⁸ ≤ ε`. -/
theorem ghashAXU_eps_lower {L : ℕ} {ε : ℝ≥0∞} (h : GhashIsAXU L ε) :
    ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹ ≤ ε := by
  rw [← ToVCVio.natCast_card_bitVec 128]
  exact ghashAXU_card_inv_le h

end GCM
