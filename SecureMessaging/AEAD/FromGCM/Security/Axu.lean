/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromGCM.Security.Encoding
import ToVCVio.CryptoFoundations.UniversalHash

/-!
# GHASH — almost-XOR-universality statement

`GhashIsAXU L ε` says that `ghash ∘ gcmEncode` is `ε`-almost-XOR-universal (AXU) on
`SupportedAAD × BitVec L`: for distinct inputs and any target `Δ`, a uniform key `H` gives
`ghash H (…) ⊕ ghash H (…) = Δ` with probability at most `ε`. The authenticity hop
(`AuthHop.lean`) assumes it and `GhashAXU.lean` proves it.

The domain is the encoded one, never raw block lists: on raw lists AXU is false, since a
leading zero block contributes nothing (`ghash h [0, X] = ghash h [X]`).
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

/-- The AXU bound of GHASH is at least the blind-tag-guess probability `2⁻¹²⁸`.

The authenticity hop bounds forgery by a union bound over the at most `q_d` decryption
queries. A query after the challenge succeeds only through a GHASH collision, with probability
at most `ε`. A query before the challenge has seen no tag and succeeds only by guessing one,
with probability exactly `2⁻¹²⁸`. Summing these caps would give the two-term
`q_post · ε + q_pre · 2⁻¹²⁸`; because `2⁻¹²⁸ ≤ ε`, every query can be charged `ε` and the sum is
`q_d · ε`. `probEvent_wcInst_forge_le` takes this inequality as its `hfloor` hypothesis. -/
theorem ghashAXU_eps_lower {L : ℕ} {ε : ℝ≥0∞} (h : GhashIsAXU L ε) :
    ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹ ≤ ε := by
  have hcard : (Fintype.card (BitVec 128) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (128 : ℕ) := by
    rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]
    push_cast
    norm_num
  rw [← hcard]
  exact ghashAXU_card_inv_le h

end GCM
