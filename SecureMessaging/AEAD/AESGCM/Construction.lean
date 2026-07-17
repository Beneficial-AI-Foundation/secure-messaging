/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.AESGCM.GCtr
import SecureMessaging.AEAD.AESGCM.GHash
import SecureMessaging.AEAD.Defs
import SecureMessaging.AES.Defs

/-!
# AES-GCM authenticated encryption (NIST SP 800-38D §7)

Assembles `gfmul`/`ghash`/`gctr`/`inc32` into GCM encryption (`gcmEncrypt`,
§7.1 Algorithm 4) and decryption (`gcmDecrypt`, §7.2 Algorithm 5), packaged as
the `AEADScheme` `aesGcmAEAD`.

## References

- [NIST_GCM] Dworkin. *NIST SP 800-38D*, 2007 — the normative algorithm.
  https://csrc.nist.gov/pubs/sp/800/38/d/final
- [ACD19] Alwen, Coretti, Dodis. *The Double Ratchet: Security Notions, Proofs,
  and Modularization for the Signal Protocol.* EUROCRYPT 2019,
  https://eprint.iacr.org/2018/1037.pdf — the `AEADScheme` interface
  (`SecureMessaging.AEAD.Defs`) that `aesGcmAEAD` targets.
- [RFC9180] Barnes, Bhargavan, Lipp, Wood. *Hybrid Public Key Encryption*,
  RFC 9180, 2022 — HPKE, libsignal's only production plain-GCM caller,
  motivating the per-key nonce. https://www.rfc-editor.org/rfc/rfc9180

## Where AES is

GCM is generic over a 128-bit block cipher that NIST SP 800-38D calls `CIPH_K`
(§5.1); AES-GCM instantiates `CIPH = AES` (FIPS 197). GCM never inspects it,
only evaluates it — so AES appears in the algorithms *only* as the abstract
argument `E : BitVec 128 → BitVec 128` (`E = CIPH_K = E_K`) of
`gcmEncrypt`/`gcmDecrypt`, and at the scheme level as `cipher : AES K` in
`aesGcmAEAD` (the `AES` interface, a PRP on 128-bit blocks; `E = cipher.perm k`).
GCM uses only the forward `perm`; its security rests on the PRF view
(`cipher.toPRFScheme`) via the PRP/PRF switching lemma. AES's FIPS-197 rounds
(and their internal GF(2^8) arithmetic, distinct from GHASH's GF(2^128)) are a
separate primitive, out of scope here.

## Modeling choices

- Block cipher kept abstract via the `AES` interface (a PRP on `BitVec 128`);
  AES-256 is the production target (the McGrew–Viega Test Case 3 KATs below use
  AES-128). Only the forward permutation `perm` is used (CTR never inverts).
- 96-bit-IV, block-aligned, full-tag path: GHASH input
  `A ‖ C ‖ (len(A) ‖ len(C))` with no partial-block padding, fixed message
  length `n` (AD stays variable-length), tag `T = E_K(J₀) ⊕ S` untruncated.
- AEAD key `K × BitVec 96`: `keygen` samples a fresh nonce per key, a fresh
  random nonce analogous to HPKE's `base_nonce` (which HPKE instead *derives*
  deterministically per context); `gcmEncrypt`/`gcmDecrypt` keep the nonce
  explicit. This is a *single-use-key* adaptation to the ACD19 interface:
  reusing a sampled `(k, nonce)` across encryptions repeats the IV and breaks
  GCM security (NIST §8), so it is not a general multi-message API.
-/

open OracleSpec OracleComp

variable {K : Type} {n : ℕ}

/-- The GCM length block `len(A) ‖ len(C)` (NIST SP 800-38D §7.1): the 64-bit
bit-lengths of the AAD and ciphertext concatenated, i.e. `128 · #blocks` each
when block-aligned. -/
def lenBlock (adBlocks cBlocks : ℕ) : BitVec 128 :=
  BitVec.ofNat 64 (adBlocks * 128) ++ BitVec.ofNat 64 (cBlocks * 128)

/-- GCM authenticated encryption `GCM-AE_K(IV, P, A)` (NIST SP 800-38D §7.1,
Algorithm 4), 96-bit-IV / block-aligned specialization (so the `0^v`/`0^u`
padding of NIST steps 4–5 vanishes), keyed block cipher `E = CIPH_K = E_K`
(NIST §5.1). Following NIST's step numbering:
- (1) `H = E_K(0)`;
- (2) `J₀ = IV ‖ 0^31 ‖ 1`;
- (3) `C = GCTR_K(inc₃₂(J₀), P)`;
- (5) `S = GHASH_H(A ‖ C ‖ (len(A) ‖ len(C)))` (step 4's padding is empty here);
- (6) `T = E_K(J₀) ⊕ S` (NIST's `MSB_t(GCTR_K(J₀, S))` for the full tag `t = 128`);
- (7) output `(C, T)`. -/
def gcmEncrypt (E : BitVec 128 → BitVec 128) (nonce : BitVec 96)
    (ad : List (BitVec 128)) (m : Vector (BitVec 128) n) :
    Vector (BitVec 128) n × BitVec 128 :=
  let h := E 0
  let iv0 := j0 nonce
  let c := gctr E (inc32 iv0) m
  let s := ghash h (ad ++ c.toList ++ [lenBlock ad.length n])
  let t := E iv0 ^^^ s
  (c, t)

/-- GCM authenticated decryption `GCM-AD_K(IV, C, A, T)` (NIST SP 800-38D §7.2,
Algorithm 5): recompute the tag from `C, A` (same full-tag form as `gcmEncrypt`);
on a match return `GCTR_K(inc₃₂(J₀), C) = P`, else `none` (NIST's `FAIL`). -/
def gcmDecrypt (E : BitVec 128 → BitVec 128) (nonce : BitVec 96)
    (ad : List (BitVec 128)) (ct : Vector (BitVec 128) n × BitVec 128) :
    Option (Vector (BitVec 128) n) :=
  let (c, t) := ct
  let h := E 0
  let iv0 := j0 nonce
  let s := ghash h (ad ++ c.toList ++ [lenBlock ad.length n])
  if t = E iv0 ^^^ s then some (gctr E (inc32 iv0) c) else none

/-- **AES-GCM as an `AEADScheme`**: the NIST SP 800-38D §7 algorithms adapted to
the ACD19 `AEADScheme` interface, where the IV is absorbed into the key rather
than passed per call (see the module's *Modeling choices*). The block cipher is
carried as an `AES` interface (a PRP on 128-bit blocks, so `keygen` has a key
distribution and GCM uses the forward `perm`); the AEAD key `K × BitVec 96`
bundles the cipher key with a fresh per-key nonce. Message space
`Vector (BitVec 128) n`; ciphertext `Vector (BitVec 128) n × BitVec 128` with the
full 128-bit tag. -/
-- ANCHOR: aesGcmAEAD
def aesGcmAEAD (cipher : AES K) :
    AEADScheme ProbComp (Vector (BitVec 128) n) (List (BitVec 128))
      (K × BitVec 96) (Vector (BitVec 128) n × BitVec 128) where
  keygen := do
    let k ← cipher.keygen
    let nonce ← $ᵗ (BitVec 96)
    return (k, nonce)
  encrypt := fun (k, nonce) ad m => gcmEncrypt (cipher.perm k) nonce ad m
  decrypt := fun (k, nonce) ad c => gcmDecrypt (cipher.perm k) nonce ad c
-- ANCHOR_END: aesGcmAEAD

/-! ## GCM validation vector (McGrew–Viega Test Case 3, not in SP 800-38D:
block-aligned, empty AAD) -/

/-- Test scaffolding: GCM Test Case 3 keyed cipher `E_K` over the inputs GCM
queries (`0` for the hash subkey `H`, the pre-counter block `J₀` for the tag
mask, and the `inc₃₂` counter chain from `J₀`). Not part of the spec. -/
private def tc3Cipher (cb : BitVec 128) : BitVec 128 :=
  if cb = 0xcafebabefacedbaddecaf88800000001 then 0x3247184b3c4f69a44dbcd22887bbb418
  else if cb = 0xcafebabefacedbaddecaf88800000002 then 0x9bb22ce7d9f372c1ee2b28722b25f206
  else if cb = 0xcafebabefacedbaddecaf88800000003 then 0x650d887c3936533a1b8d4e1ea39d2b5c
  else if cb = 0xcafebabefacedbaddecaf88800000004 then 0x3de91827c10e9a4f5240647ee5221f20
  else if cb = 0xcafebabefacedbaddecaf88800000005 then 0xaac9e6ccc0074ac0873b9ba85d908bd0
  else if cb = 0 then 0xb83b533708bf535d0aa6e52980d53b78
  else 0

/-- Test Case 3 plaintext (four blocks). -/
private def tc3Plain : Vector (BitVec 128) 4 :=
  #v[ 0xd9313225f88406e5a55909c5aff5269a,
      0x86a7a9531534f7da2e4c303d8a318a72,
      0x1c3c0c95956809532fcf0e2449a6b525,
      0xb16aedf5aa0de657ba637b391aafd255 ]

/-- Test Case 3 ciphertext and full tag `(C, T)`. -/
private def tc3Ciphertext : Vector (BitVec 128) 4 × BitVec 128 :=
  ( #v[ 0x42831ec2217774244b7221b784d0d49c,
        0xe3aa212f2c02a4e035c17e2329aca12e,
        0x21d514b25466931c7d8f6a5aac84aa05,
        0x1ba30b396a0aac973d58e091473f5985 ],
    0x4d5c2af327cd64a62cf35abd2ba6fab4 )

/-- `gcmEncrypt` reproduces the Test Case 3 ciphertext and tag. -/
example :
    gcmEncrypt tc3Cipher 0xcafebabefacedbaddecaf888 [] tc3Plain = tc3Ciphertext := by
  decide

/-- `gcmDecrypt` inverts `gcmEncrypt`. -/
example :
    gcmDecrypt tc3Cipher 0xcafebabefacedbaddecaf888 [] tc3Ciphertext = some tc3Plain := by
  decide

/-- `gcmDecrypt` rejects a tampered tag. -/
example :
    gcmDecrypt tc3Cipher 0xcafebabefacedbaddecaf888 []
      (tc3Ciphertext.1, 0x00000000000000000000000000000000) = none := by decide
