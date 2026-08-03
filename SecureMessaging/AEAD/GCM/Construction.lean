/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.GCM.Gcm
import SecureMessaging.AEAD.Defs
import SecureMessaging.PRP.Defs

/-!
# GCM authenticated encryption (NIST SP 800-38D §7)

Assembles `gfmul`/`ghash`/`gctr`/`inc₃₂` into GCM encryption (`gcmEncrypt`,
§7.1 Algorithm 4) and decryption (`gcmDecrypt`, §7.2 Algorithm 5), packaged as
the one-time-key `AEADScheme` `gcmOneTimeAEAD`.

## References

- [NIST_GCM] Dworkin. *NIST SP 800-38D*, 2007 — the normative algorithm.
  https://csrc.nist.gov/pubs/sp/800/38/d/final
- [ACD19] Alwen, Coretti, Dodis. *The Double Ratchet: Security Notions, Proofs,
  and Modularization for the Signal Protocol.* EUROCRYPT 2019,
  https://eprint.iacr.org/2018/1037.pdf — the `AEADScheme` interface
  (`SecureMessaging.AEAD.Defs`) that `gcmOneTimeAEAD` targets.
- [RFC9180] Barnes, Bhargavan, Lipp, Wood. *Hybrid Public Key Encryption*,
  RFC 9180, 2022 — HPKE, libsignal's only production plain-GCM caller, whose
  per-message nonce the nonce-explicit `gcmEncrypt`/`gcmDecrypt` model.
  https://www.rfc-editor.org/rfc/rfc9180

## Where the cipher is committed

The algorithms take NIST's block cipher directly as `ciph : CIPH K`, using only the
forward direction `ciph.perm`. The scheme `gcmOneTimeAEAD` supplies the key
generation on top, taking a full `PRPScheme` (block cipher + `keygen`); see its
docstring.

## Scope

A specialization of NIST's general GCM. Inputs are arbitrary-length bit strings,
with the partial final block, GHASH zero-padding, and true `len(A) ‖ len(C)` field
all modelled — a reader sees NIST Algorithms 3/4/5 directly. Narrowings:

- **96-bit IV**: `J₀ = IV ‖ 0³¹ ‖ 1` directly — NIST §5.2.1.1's recommended length
  and the one HPKE (RFC 9180) fixes. Other IV lengths (GHASH-derived `J₀`, §7.1)
  are out of scope; that path is also the regime whose bound Iwata–Ohashi–Minematsu
  (CRYPTO 2012) had to repair, so 96 bits stays in the clean one.
- **Single-use key** (`gcmOneTimeAEAD`): each key encrypts one message, so a fixed
  IV is sufficient — the `(key, IV)` pair is never reused (NIST §8).
- **Supported-length, byte-aligned, fixed-length domain** (`gcmOneTimeAEAD`): NIST requires
  byte-aligned lengths within the §5.2.1.1 maxima (`ValidMsgLength`/`ValidAADLength`),
  and the message length is fixed to one `L` for the IND-CCA game's samplable
  ciphertext. The algorithm layer itself stays length-generic.
-/

open OracleSpec OracleComp

/-! ## The length constraint on the input -/

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

/-- `CIPH K` (NIST SP 800-38D §5.1): the block cipher GCM is built over, named after
NIST's own notation for it. -/
abbrev CIPH (K : Type) := BlockCipher K (BitVec 128)

/-- GCM authenticated encryption `GCM-AE_K(IV, P, A)` (NIST SP 800-38D §7.1,
Algorithm 4), on arbitrary-length bit strings: AAD `ad : BitVec lenA`, plaintext
`m : BitVec lenP`, ciphertext `c : BitVec lenP` (GCTR preserves length). The cipher is
`ciph : CIPH K`, evaluated forward `ciph.perm k = CIPH_K`; `iv` is the 96-bit IV.

Raw algorithm layer: like NIST Algorithm 4 it does not check lengths (a precondition
`ValidMsgLength lenP ∧ ValidAADLength lenA`; outside it the `[len(A)]₆₄ ‖ [len(C)]₆₄`
block wraps mod 2⁶⁴). `gcmOneTimeAEAD` only ever applies it on its supported domain.

Following NIST's steps:
- (1) `H = E_K(0)`;
- (2) `J₀ = IV ‖ 0³¹ ‖ 1`;
- (3) `C = GCTR_K(inc₃₂(J₀), P)`;
- (4–5) `S = GHASH_H(A ‖ 0^v ‖ C ‖ 0^u ‖ [len(A)]₆₄ ‖ [len(C)]₆₄)` (padding via
  `padBlocks`, length block appended last);
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
Algorithm 5). `none` is NIST's `FAIL`; `some P` is the recovered plaintext.

Following NIST's steps:
- (1) FAIL if the input lengths are unsupported (`ValidMsgLength lenP ∧
  ValidAADLength lenA`; the `IV`/tag lengths are fixed by the `BitVec 96`/`BitVec 128`
  types, so only these two remain to check);
- (2) `H = E_K(0)`;
- (3) `J₀ = IV ‖ 0³¹ ‖ 1`;
- (4) `P = GCTR_K(inc₃₂(J₀), C)`;
- (5–6) `S = GHASH_H(A ‖ 0^v ‖ C ‖ 0^u ‖ [len(A)]₆₄ ‖ [len(C)]₆₄)`;
- (7) `T' = GCTR_K(J₀, S)` (one block, so `MSB₁₂₈` is the identity), as in `gcmEncrypt`;
- (8) if `T = T'` return `P`, else FAIL. -/
def gcmDecrypt {K : Type} (ciph : CIPH K) (k : K)
    (iv : BitVec 96) {lenA lenP : ℕ} (ad : BitVec lenA) (ct : BitVec lenP × BitVec 128) :
    Option (BitVec lenP) :=
  -- (1) FAIL immediately on unsupported input lengths, before any GHASH work
  if ValidMsgLength lenP ∧ ValidAADLength lenA then
    let (c, t) := ct
    let h := ciph.perm k 0                          -- (2)
    let j₀ := iv ++ (0 : BitVec 31) ++ (1 : BitVec 1) -- (3)
    let p := gctr ciph.perm k (inc32 j₀) c          -- (4)
    let s := ghash h (padBlocks ad ++ padBlocks c ++ [BitVec.ofNat 64 lenA ++ BitVec.ofNat 64 lenP]) -- (5–6)
    -- (7–8) recompute `T'` and return `P` on a match, else FAIL
    if t = gctr ciph.perm k j₀ s then some p else none
  else none

/-- **One-time-key GCM as an `AEADScheme`** (ACD19 interface). This is a one-time-key
specialization of 96-bit-IV GCM for the ACD19 AEAD abstraction. It fixes the IV to
`0` because the security experiment permits only one encryption per freshly generated
block-cipher key; it is not a multi-invocation GCM interface (for that, call the
nonce-explicit `gcmEncrypt`/`gcmDecrypt` directly).

The scheme layer: `prp : PRPScheme K (BitVec 128)` supplies the block cipher plus
key generation; the mode consumes only `prp.toBlockCipher : CIPH K`. The PRP→PRF
switch (`prp.toPRFScheme`) belongs to the security reduction, not the mode.

The AEAD key is the block-cipher key `K` itself — no IV is bundled in. Fixing the IV
is sound precisely because keygen draws a fresh key per encryption, so the `(key, IV)`
pair is never reused (the GCM uniqueness requirement, NIST §8). The ciphertext stays
`(C, T)`, matching ACD19's fixed ciphertext space. The domain is NIST-supported by
construction — AAD is `SupportedAAD`, the message length carries `_hL : ValidMsgLength
L` — with the message fixed to `BitVec L` so the ciphertext `BitVec L × BitVec 128` is
`SampleableType` for the IND-CCA game. Hence `gcmOneTimeAEAD_correct` is the
*unconditional* `AEADScheme.Correct`.

`_hL` is carried to document/require length-support at construction but is not used
in the body (correctness supplies its own hypothesis), hence `nolint`. -/
@[nolint unusedArguments]
-- ANCHOR: gcmOneTimeAEAD
def gcmOneTimeAEAD {K : Type} (prp : PRPScheme K (BitVec 128)) (L : ℕ)
    (_hL : ValidMsgLength L) :
    AEADScheme ProbComp (BitVec L) SupportedAAD
      K (BitVec L × BitVec 128) where
  keygen := prp.keygen
  encrypt := fun k ad m => gcmEncrypt prp.toBlockCipher k (0 : BitVec 96) ad.1.2 m
  decrypt := fun k ad c => gcmDecrypt prp.toBlockCipher k (0 : BitVec 96) ad.1.2 c
-- ANCHOR_END: gcmOneTimeAEAD

/-- `gcmOneTimeAEAD` satisfies the unconditional ACD19 `AEADScheme.Correct` (given the
message length is supported, `hL`): every domain AAD is supported, so `gcmDecrypt`'s
length guard passes; the recomputed tag matches by construction; and
`gctr_involution` recovers the plaintext. -/
-- ANCHOR: gcmOneTimeAEAD_correct
theorem gcmOneTimeAEAD_correct {K : Type} (prp : PRPScheme K (BitVec 128)) {L : ℕ}
    (hL : ValidMsgLength L) :
    (gcmOneTimeAEAD prp L hL).Correct
-- ANCHOR_END: gcmOneTimeAEAD_correct
    := by
  rintro k ⟨⟨av, ad⟩, hav⟩ m
  have hv : ValidMsgLength L ∧ ValidAADLength av := ⟨hL, hav⟩
  simp only [gcmOneTimeAEAD, gcmEncrypt, gcmDecrypt]
  rw [if_pos hv]
  simp only [if_true, gctr_involution]
