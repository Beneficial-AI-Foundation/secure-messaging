/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.GCM.Components
import SecureMessaging.PRP.Defs

/-!
# GCM authenticated encryption (NIST SP 800-38D §7)

Assembles the §6 components (`Components`) into GCM encryption (`gcmEncrypt`,
§7.1 Algorithm 4) and decryption (`gcmDecrypt`, §7.2 Algorithm 5).
`gcmOneTimeAEAD` (`Construction`) packages these as an `AEADScheme`.

## Scope

The IV is 96 bits only (`J₀ = IV ‖ 0³¹ ‖ 1`, NIST §5.2.1.1's recommended length, the
one HPKE/RFC 9180 fixes); the GHASH-derived `J₀` path for other IV lengths is out of
scope. Message and AAD lengths stay generic, with `ValidMsgLength`/`ValidAADLength`
capturing NIST's §5.2.1.1 supported range.

## References

- [NIST_GCM] Dworkin. *NIST SP 800-38D*, 2007. https://csrc.nist.gov/pubs/sp/800/38/d/final
-/

/-! ## Supported input lengths (NIST SP 800-38D §5.2.1.1) -/

/-- Supported plaintext/ciphertext bit-length (NIST SP 800-38D §5.2.1.1):
`≤ 2^39 - 256` and a multiple of 8 (byte-aligned). -/
-- ANCHOR: ValidMsgLength
@[reducible] def ValidMsgLength (lenC : ℕ) : Prop := lenC ≤ 2 ^ 39 - 256 ∧ 8 ∣ lenC
-- ANCHOR_END: ValidMsgLength

/-- Supported AAD bit-length (NIST SP 800-38D §5.2.1.1): `≤ 2^64 - 1` and a multiple
of 8 (byte-aligned). -/
-- ANCHOR: ValidAADLength
@[reducible] def ValidAADLength (lenA : ℕ) : Prop := lenA ≤ 2 ^ 64 - 1 ∧ 8 ∣ lenA
-- ANCHOR_END: ValidAADLength

/-- Variable-length byte-string AAD of supported length (`ValidAADLength`);
`gcmOneTimeAEAD`'s associated-data type. -/
-- ANCHOR: SupportedAAD
abbrev SupportedAAD := { x : (a : ℕ) × BitVec a // ValidAADLength x.1 }
-- ANCHOR_END: SupportedAAD

/-! ## The GCM algorithms (NIST SP 800-38D §7) -/

/-- `CIPH K` (NIST SP 800-38D §5.1): the 128-bit block cipher GCM is built over. Only
the forward direction `ciph.perm k = CIPH_K` is used. -/
abbrev CIPH (K : Type) := BlockCipher K (BitVec 128)

/-- GCM authenticated encryption `GCM-AE_K(IV, P, A)` (NIST SP 800-38D §7.1,
Algorithm 4): AAD `ad : BitVec lenA`, plaintext `m : BitVec lenP`, ciphertext
`BitVec lenP` (GCTR preserves length), 96-bit `iv`, forward cipher `ciph.perm k = CIPH_K`.
Length-generic like NIST Algorithm 4 (no length check; the `[len(A)]₆₄ ‖ [len(C)]₆₄`
block wraps mod 2⁶⁴ outside `ValidMsgLength`/`ValidAADLength`).
- (1) `H = E_K(0)`; (2) `J₀ = IV ‖ 0³¹ ‖ 1`; (3) `C = GCTR_K(inc₃₂(J₀), P)`;
- (4–5) `S = GHASH_H(A ‖ 0^v ‖ C ‖ 0^u ‖ [len(A)]₆₄ ‖ [len(C)]₆₄)` (padding via `padBlocks`);
- (6) `T = GCTR_K(J₀, S)` (one block, so `MSB₁₂₈` is the identity); (7) output `(C, T)`. -/
def gcmEncrypt {K : Type} (ciph : CIPH K) (k : K)
    (iv : BitVec 96) {lenA lenP : ℕ} (ad : BitVec lenA) (m : BitVec lenP) :
    BitVec lenP × BitVec 128 :=
  let h := ciph.perm k 0
  let j₀ := iv ++ (0 : BitVec 31) ++ (1 : BitVec 1)
  let c := gctr ciph.perm k (inc32 j₀) m
  -- trailing GHASH block `[len(A)]₆₄ ‖ [len(C)]₆₄` (NIST SP 800-38D §7.1 step 5)
  let s := ghash h (padBlocks ad ++ padBlocks c ++ [BitVec.ofNat 64 lenA ++ BitVec.ofNat 64 lenP])
  -- (6) `T = GCTR_K(J₀, S)` (NIST SP 800-38D §7.1 step 6); one block, so no truncation
  let t := gctr ciph.perm k j₀ s
  (c, t)

/-- GCM authenticated decryption `GCM-AD_K(IV, C, A, T)` (NIST SP 800-38D §7.2,
Algorithm 5); `none` is NIST's `FAIL`, `some P` the recovered plaintext.
- (1) FAIL if lengths are unsupported (`ValidMsgLength lenP ∧ ValidAADLength lenA`;
  the IV/tag widths are fixed by the `BitVec 96`/`BitVec 128` types);
- (2) `H = E_K(0)`; (3) `J₀ = IV ‖ 0³¹ ‖ 1`; (4) `P = GCTR_K(inc₃₂(J₀), C)`;
- (5–6) `S` as in `gcmEncrypt`; (7) `T' = GCTR_K(J₀, S)`;
- (8) return `P` if `T = T'`, else FAIL. -/
def gcmDecrypt {K : Type} (ciph : CIPH K) (k : K)
    (iv : BitVec 96) {lenA lenP : ℕ} (ad : BitVec lenA) (ct : BitVec lenP × BitVec 128) :
    Option (BitVec lenP) :=
  -- (1) FAIL immediately on unsupported input lengths, before any GHASH work
  if ValidMsgLength lenP ∧ ValidAADLength lenA then
    let (c, t) := ct
    let h := ciph.perm k 0                          -- (2)
    let j₀ := iv ++ (0 : BitVec 31) ++ (1 : BitVec 1) -- (3)
    let p := gctr ciph.perm k (inc32 j₀) c          -- (4)
    -- (5–6) `S = GHASH_H(A ‖ 0^v ‖ C ‖ 0^u ‖ [len(A)]₆₄ ‖ [len(C)]₆₄)`
    let s := ghash h (padBlocks ad ++ padBlocks c ++ [BitVec.ofNat 64 lenA ++ BitVec.ofNat 64 lenP])
    -- (7–8) recompute `T'` and return `P` on a match, else FAIL
    if t = gctr ciph.perm k j₀ s then some p else none
  else none
