/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.GCM.Gcm
import SecureMessaging.AEAD.GCM.TestVectors
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
- [MV_GCM] McGrew, Viega. *The Galois/Counter Mode of Operation (GCM)*, 2005 —
  the original GCM proposal; source of the "Test Case 3/4" validation vectors
  (App. B), which are not part of SP 800-38D. https://csrc.nist.gov/csrc/media/projects/block-cipher-techniques/documents/bcm/proposed-modes/gcm/gcm-revised-spec.pdf
- [ACD19] Alwen, Coretti, Dodis. *The Double Ratchet: Security Notions, Proofs,
  and Modularization for the Signal Protocol.* EUROCRYPT 2019,
  https://eprint.iacr.org/2018/1037.pdf — the `AEADScheme` interface
  (`SecureMessaging.AEAD.Defs`) that `gcmOneTimeAEAD` targets.
- [RFC9180] Barnes, Bhargavan, Lipp, Wood. *Hybrid Public Key Encryption*,
  RFC 9180, 2022 — HPKE, libsignal's only production plain-GCM caller, whose
  per-message nonce the nonce-explicit `gcmEncrypt`/`gcmDecrypt` model.
  https://www.rfc-editor.org/rfc/rfc9180

## Where the cipher is committed

The algorithms keep the cipher abstract — NIST's keyed family
`ciph = CIPH : K → BitVec 128 → BitVec 128`, evaluated `ciph k = CIPH_K = E_K`
(§5.1) — so `gcmEncrypt`/`gcmDecrypt` are cipher-agnostic. The scheme
`gcmOneTimeAEAD` commits it to a `PRPScheme` on 128-bit blocks (NIST §5.1: an
approved block cipher,
128-bit block, key ≥ 128 bits — a permutation, not an arbitrary PRF); see its
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
  byte-aligned lengths within the §5.2.1.1 maxima (`ValidLengths`), and the message
  length is fixed to one `L` for the IND-CCA game's samplable ciphertext. The
  algorithm layer itself stays length-generic.
-/

open OracleSpec OracleComp

/-! ## The length constraint on the input -/

/-- Supported plaintext/ciphertext length (NIST SP 800-38D §5.2.1.1): bounded
(`≤ 2^39 − 256`) and **byte-aligned** (`8 ∣ ·`). -/
@[reducible] def ValidMsgLength (lenC : ℕ) : Prop := lenC ≤ 2 ^ 39 - 256 ∧ 8 ∣ lenC

/-- Supported AAD length (NIST SP 800-38D §5.2.1.1): bounded (`≤ 2^64 − 1`) and
**byte-aligned** (`8 ∣ ·`). -/
@[reducible] def ValidAADLength (lenA : ℕ) : Prop := lenA ≤ 2 ^ 64 - 1 ∧ 8 ∣ lenA

/-- The GCM supported-length constraint (NIST SP 800-38D §5.2.1.1): plaintext and
AAD bit-lengths bounded and byte-aligned. NIST: "Although GCM is defined on bit
strings, the bit lengths of the plaintext, the AAD, and the IV shall all be
multiples of 8, so that these values are byte strings." (`len(C) = len(P)`, GCTR
preserving length.) `gcmDecrypt` enforces it (Algorithm 5 step 1) and it is baked
into `gcmOneTimeAEAD`'s domain. `@[reducible]` for `Decidable` in the guard. -/
@[reducible] def ValidLengths (lenA lenC : ℕ) : Prop :=
  ValidMsgLength lenC ∧ ValidAADLength lenA

/-- The supported-AAD domain: variable-length byte-string AAD whose length is
NIST-supported. This is `gcmOneTimeAEAD`'s associated-data type. -/
abbrev SupportedAAD := { x : (a : ℕ) × BitVec a // ValidAADLength x.1 }

/-! ## The GCM algorithms (NIST SP 800-38D §7) -/

/-- GCM authenticated encryption `GCM-AE_K(IV, P, A)` (NIST SP 800-38D §7.1,
Algorithm 4), on arbitrary-length bit strings: AAD `ad : BitVec a`, plaintext
`m : BitVec p`, ciphertext `c : BitVec p` (GCTR preserves length). The cipher is the
forward family `ciph k = CIPH_K` (module header); `iv` is the 96-bit IV.

Raw algorithm layer: like NIST Algorithm 4 it does not check lengths (a precondition
`ValidLengths a p`; outside it the `[len(A)]₆₄ ‖ [len(C)]₆₄` block wraps mod 2⁶⁴).
`gcmOneTimeAEAD` only ever applies it on its supported domain.

Following NIST's steps:
- (1) `H = E_K(0)`;
- (2) `J₀ = IV ‖ 0³¹ ‖ 1`;
- (3) `C = GCTR_K(inc₃₂(J₀), P)`;
- (4–5) `S = GHASH_H(A ‖ 0^v ‖ C ‖ 0^u ‖ [len(A)]₆₄ ‖ [len(C)]₆₄)` (padding via
  `padBlocks`, length block appended last);
- (6) `T = E_K(J₀) ⊕ S`; (7) output `(C, T)`. -/
def gcmEncrypt {K : Type} (ciph : K → BitVec 128 → BitVec 128) (k : K)
    (iv : BitVec 96) {a p : ℕ} (ad : BitVec a) (m : BitVec p) :
    BitVec p × BitVec 128 :=
  let h := ciph k 0
  let j₀ := iv ++ (0 : BitVec 31) ++ (1 : BitVec 1)
  let c := gctr ciph k (inc32 j₀) m
  -- trailing GHASH block `[len(A)]₆₄ ‖ [len(C)]₆₄` (NIST SP 800-38D §7.1 step 5)
  let s := ghash h (padBlocks ad ++ padBlocks c ++ [BitVec.ofNat 64 a ++ BitVec.ofNat 64 p])
  let t := ciph k j₀ ^^^ s
  (c, t)

/-- GCM authenticated decryption `GCM-AD_K(IV, C, A, T)` (NIST SP 800-38D §7.2,
Algorithm 5): `FAIL` (return `none`) if the input lengths are unsupported (step 1,
`ValidLengths a p`; `IV`/tag lengths are fixed by the `BitVec 96`/`BitVec 128`
types), else recompute the tag as in `gcmEncrypt` and, on a match, return
`GCTR_K(inc₃₂(J₀), C) = P`. Encryption has no such check — Algorithm 4 assumes it as
a precondition; only Algorithm 5 validates lengths. -/
def gcmDecrypt {K : Type} (ciph : K → BitVec 128 → BitVec 128) (k : K)
    (iv : BitVec 96) {a p : ℕ} (ad : BitVec a) (ct : BitVec p × BitVec 128) :
    Option (BitVec p) :=
  -- Algorithm 5 step 1: FAIL immediately on unsupported input lengths, before any
  -- GHASH work.
  if ValidLengths a p then
    let (c, t) := ct
    let h := ciph k 0
    let j₀ := iv ++ (0 : BitVec 31) ++ (1 : BitVec 1)
    -- trailing GHASH block `[len(A)]₆₄ ‖ [len(C)]₆₄` (NIST SP 800-38D §7.1 step 5)
    let s := ghash h (padBlocks ad ++ padBlocks c ++ [BitVec.ofNat 64 a ++ BitVec.ofNat 64 p])
    if t = ciph k j₀ ^^^ s then some (gctr ciph k (inc32 j₀) c) else none
  else none

/-- `CIPH K` (NIST SP 800-38D §5.1): the block cipher GCM is built over — a PRP on
128-bit blocks keyed by `K`, of which GCM uses only the forward direction. Shorter
and closer to the standard's name than `PRPScheme K (BitVec 128)`. -/
abbrev CIPH (K : Type) := PRPScheme K (BitVec 128)

/-- **One-time-key GCM as an `AEADScheme`** (ACD19 interface). This is a one-time-key
specialization of 96-bit-IV GCM for the ACD19 AEAD abstraction. It fixes the IV to
`0` because the security experiment permits only one encryption per freshly generated
block-cipher key; it is not a multi-invocation GCM interface (for that, call the
nonce-explicit `gcmEncrypt`/`gcmDecrypt` directly).

The scheme layer: the cipher is a `CIPH K` (PRP on 128-bit blocks), used forward only
(`ciph = prp.perm`; `prp.invPerm` is unused, as CTR runs forward both ways). The
PRP→PRF switch (`prp.toPRFScheme`) belongs to the security reduction, not the mode.

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
def gcmOneTimeAEAD {K : Type} (prp : CIPH K) (L : ℕ)
    (_hL : ValidMsgLength L) :
    AEADScheme ProbComp (BitVec L) SupportedAAD
      K (BitVec L × BitVec 128) where
  keygen := prp.keygen
  encrypt := fun k ad m => gcmEncrypt prp.perm k (0 : BitVec 96) ad.1.2 m
  decrypt := fun k ad c => gcmDecrypt prp.perm k (0 : BitVec 96) ad.1.2 c
-- ANCHOR_END: gcmOneTimeAEAD

/-- `gcmOneTimeAEAD` satisfies the unconditional ACD19 `AEADScheme.Correct` (given the
message length is supported, `hL`): every domain AAD is supported, so `gcmDecrypt`'s
length guard passes; the recomputed tag matches by construction; and
`gctr_involution` recovers the plaintext. -/
-- ANCHOR: gcmOneTimeAEAD_correct
theorem gcmOneTimeAEAD_correct {K : Type} (prp : CIPH K) {L : ℕ}
    (hL : ValidMsgLength L) :
    (gcmOneTimeAEAD prp L hL).Correct
-- ANCHOR_END: gcmOneTimeAEAD_correct
    := by
  rintro k ⟨⟨av, ad⟩, hav⟩ m
  have hv : ValidLengths av L := ⟨hL, hav⟩
  simp only [gcmOneTimeAEAD, gcmEncrypt, gcmDecrypt]
  rw [if_pos hv]
  simp only [if_true, gctr_involution]

/-! ## GCM validation vectors (McGrew–Viega, not in SP 800-38D)

Test Case 3 (four full blocks, empty AAD) covers the block-aligned path; Test
Case 4 (60-byte plaintext, 20-byte AAD) covers the **partial final block**,
**partial AAD block**, and the **true bit-length** field. Both share the Test
Case 3 key/IV, so the tabulated cipher `tc3Cipher` (see
`SecureMessaging.AEAD.GCM.TestVectors`) already covers every counter block and the
hash subkey both vectors query. `native_decide` is used because kernel `decide`
cannot reduce the wide `BitVec` literals (their `2^n` modulus exceeds the
exponentiation threshold); the resulting `Lean.ofReduceBool` axiom is confined to
these anonymous `example`s and does not enter `gcmOneTimeAEAD`/`gcmOneTimeAEAD_correct`. -/

section KnownAnswerTests
set_option linter.style.longLine false
set_option linter.style.nativeDecide false

/-- Test Case 3 plaintext (four blocks, 512 bits). -/
private def tc3Plain : BitVec 512 :=
  0xd9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255

/-- Test Case 3 ciphertext (512 bits) and full tag. -/
private def tc3Ct : BitVec 512 :=
  0x42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091473f5985
private def tc3Tag : BitVec 128 := 0x4d5c2af327cd64a62cf35abd2ba6fab4

/-- `gcmEncrypt` reproduces the Test Case 3 ciphertext and tag (empty AAD). -/
example :
    gcmEncrypt tc3Cipher () 0xcafebabefacedbaddecaf888 (0 : BitVec 0) tc3Plain
      = (tc3Ct, tc3Tag) := by native_decide

/-- `gcmDecrypt` inverts `gcmEncrypt` on Test Case 3. -/
example :
    gcmDecrypt tc3Cipher () 0xcafebabefacedbaddecaf888 (0 : BitVec 0) (tc3Ct, tc3Tag)
      = some tc3Plain := by native_decide

/-- `gcmDecrypt` rejects a tampered tag. -/
example :
    gcmDecrypt tc3Cipher () 0xcafebabefacedbaddecaf888 (0 : BitVec 0) (tc3Ct, 0)
      = none := by native_decide

/-- Test Case 4 AAD (20 bytes = 160 bits): a full block plus a partial block. -/
private def tc4Aad : BitVec 160 := 0xfeedfacedeadbeeffeedfacedeadbeefabaddad2

/-- Test Case 4 plaintext (60 bytes = 480 bits): three full blocks plus a
12-byte partial final block. -/
private def tc4Plain : BitVec 480 :=
  0xd9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39

/-- Test Case 4 ciphertext (480 bits) and full tag. -/
private def tc4Ct : BitVec 480 :=
  0x42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091
private def tc4Tag : BitVec 128 := 0x5bc94fbc3221a5db94fae95ae7121a47

/-- `gcmEncrypt` reproduces Test Case 4: exercises the partial final block (GCTR
keystream truncation), the partial AAD block (`0^v`/`0^u` padding), and the true
`len(A) ‖ len(C)` field, all against the authoritative vector. -/
example :
    gcmEncrypt tc3Cipher () 0xcafebabefacedbaddecaf888 tc4Aad tc4Plain
      = (tc4Ct, tc4Tag) := by native_decide

/-- `gcmDecrypt` inverts `gcmEncrypt` on Test Case 4 (partial blocks, non-empty AAD). -/
example :
    gcmDecrypt tc3Cipher () 0xcafebabefacedbaddecaf888 tc4Aad (tc4Ct, tc4Tag)
      = some tc4Plain := by native_decide

/-- AAD is authenticated: decrypting Test Case 4 under a different AAD is rejected
(GHASH, hence the tag, binds the AAD). -/
example :
    gcmDecrypt tc3Cipher () 0xcafebabefacedbaddecaf888
      (0xfeedfacedeadbeeffeedfacedeadbeef00000000 : BitVec 160) (tc4Ct, tc4Tag)
      = none := by native_decide

end KnownAnswerTests
