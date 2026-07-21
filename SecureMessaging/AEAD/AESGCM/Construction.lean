/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.AESGCM.GCtr
import SecureMessaging.AEAD.AESGCM.GHash
import SecureMessaging.AEAD.AESGCM.TestVectors
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
- [MV_GCM] McGrew, Viega. *The Galois/Counter Mode of Operation (GCM)*, 2005 —
  the original GCM proposal; source of the "Test Case 3" validation vector
  (App. B), which is not part of SP 800-38D. https://csrc.nist.gov/csrc/media/projects/block-cipher-techniques/documents/bcm/proposed-modes/gcm/gcm-revised-spec.pdf
- [ACD19] Alwen, Coretti, Dodis. *The Double Ratchet: Security Notions, Proofs,
  and Modularization for the Signal Protocol.* EUROCRYPT 2019,
  https://eprint.iacr.org/2018/1037.pdf — the `AEADScheme` interface
  (`SecureMessaging.AEAD.Defs`) that `aesGcmAEAD` targets.
- [RFC9180] Barnes, Bhargavan, Lipp, Wood. *Hybrid Public Key Encryption*,
  RFC 9180, 2022 — HPKE, libsignal's only production plain-GCM caller,
  motivating the per-key nonce. https://www.rfc-editor.org/rfc/rfc9180

## Where AES is

GCM is generic over a 128-bit block cipher that NIST SP 800-38D calls `CIPH_K`
(§5.1), and it never inspects that cipher, only evaluates it. So the algorithms
`gcmEncrypt`/`gcmDecrypt` abstract the cipher away entirely: it enters only as a
plain function `E : BitVec 128 → BitVec 128` (`E = CIPH_K = E_K`), and `AES` is
never mentioned at this layer.

AES appears one layer up, in the scheme `aesGcmAEAD`, which is what makes this
*AES*-GCM (`CIPH = AES`, FIPS 197). There we commit to the cipher as
`cipher : AES K` (the `AES` interface, a PRP on 128-bit blocks) and instantiate
the algorithms with `E = cipher.perm k`.

AES bottoms out as an opaque primitive: its FIPS-197 internals are out of scope,
assumed to be a PRP, on which GCM's security rests via the PRP/PRF switching lemma
(the PRF view `cipher.toPRFScheme`). Everything above the cipher: GCTR, GHASH,
the tag, is defined here.

## Scope

This is a specialization of NIST's general GCM. The essential narrowing is the
mode of use: NIST GCM is multi-message (one key, a fresh IV per call), whereas
here each key encrypts a single message. It also fixes the common configuration:
a 96-bit IV, whole-block plaintext and AAD, a fixed message length, and an
untruncated 128-bit tag. These choices are documented where they take effect, on
`gcmEncrypt` (the algorithm layer) and `aesGcmAEAD` (the scheme layer) below.
-/

open OracleSpec OracleComp

variable {K : Type} {n : ℕ}

/-- The GCM length block `len(A) ‖ len(C)` (NIST SP 800-38D §7.1): the 64-bit
bit-lengths of the AAD and ciphertext concatenated, i.e. `128 · #blocks` each
when block-aligned.

This length field is GCM's binding of the `A`/`C` boundary, the defense against
an adversary shifting bits between the AAD and the ciphertext.

**Block-aligned assumption.** The `* 128` hardcodes the whole-block
model: it takes *block counts* and multiplies, rather than taking true bit
lengths. This is correct only because the message and AAD are whole 128-bit
blocks (see the module *Scope*). If the domain is ever widened to allow a partial
final block, this must be generalized to the real bit-lengths of `A`/`C` **and**
the GHASH input must zero-pad the partial blocks (NIST §7.1 steps 4–5); changing
one without the other silently computes the tag over a wrong length. -/
def lenBlock (adBlocks cBlocks : ℕ) : BitVec 128 :=
  BitVec.ofNat 64 (adBlocks * 128) ++ BitVec.ofNat 64 (cBlocks * 128)

/-- GCM authenticated encryption `GCM-AE_K(IV, P, A)` (NIST SP 800-38D §7.1,
Algorithm 4).

This is the **algorithm layer**: cipher-agnostic, exactly as NIST §5.1 defines
GCM over any 128-bit block cipher. The cipher enters only as the already-keyed
forward map `E = CIPH_K = E_K : BitVec 128 → BitVec 128`; `AES` is never
mentioned here (that commitment happens in `aesGcmAEAD`).

Specialized to the common configuration (see the module *Scope*):
- **96-bit IV** (the `nonce`): `J₀ = IV ‖ 0^31 ‖ 1` directly. Other IV lengths,
  which NIST converts to a 128-bit `J₀` via a GHASH over the IV, are out of scope.
- **Block-aligned plaintext and AAD**: the message `m` and the AAD `ad`
  (*additional authenticated data*, authenticated but not encrypted) are whole
  128-bit blocks, so NIST's `0^v`/`0^u` padding of `A` and `C` (steps 4–5)
  vanishes and the GHASH input is exactly `A ‖ C ‖ (len(A) ‖ len(C))`.
- **Fixed message length** `n` (the AAD stays variable-length) and an
  **untruncated 128-bit tag**.

Following NIST's step numbering:
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
than passed per call.

This is the **scheme layer**, and the *only* place AES is committed to: the
cipher-agnostic `gcmEncrypt`/`gcmDecrypt` are instantiated by supplying the `AES`
interface (a PRP on 128-bit blocks, so `keygen` carries a key distribution),
plugged in as `E = cipher.perm k`. The abstract argument `E` of the algorithm
layer thus becomes concrete here, and the security game lives at this level (via
`cipher.toPRFScheme`), not inside the algorithms. Although a PRP is invertible,
only the forward `perm` is used, never `invPerm`, because both encryption and
decryption run through CTR mode, which only evaluates the cipher forward.

The AEAD key `K × BitVec 96` bundles the cipher key with a fresh per-key nonce
that `keygen` samples (analogous to HPKE's `base_nonce`, which HPKE instead
*derives* deterministically per context). This is the **single-use-key**
specialization (see the module *Scope*): reusing a sampled `(k, nonce)` across
encryptions repeats the IV and breaks GCM security (NIST §8), so this is not a
general multi-message API. Message space `Vector (BitVec 128) n`; ciphertext
`Vector (BitVec 128) n × BitVec 128` with the full 128-bit tag. -/
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
block-aligned, empty AAD). The keyed cipher `tc3Cipher` is shared with the
`GCtr` test suite (see `SecureMessaging.AEAD.AESGCM.TestVectors`). -/

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

/-! ## Edge-case / robustness checks (block-aligned AAD, empty message,
ciphertext tampering)

Test Case 3 exercises only a 4-block message with **empty** AAD, so these fill the
gaps in that coverage. They are self-contained — they reuse the Test Case 3 cipher
table and assert round-trip / rejection properties, rather than external vectors
(a genuinely independent AAD KAT is out of reach here: the table cipher is defined
only on Test Case 3's counter blocks, and standard vectors with block-aligned AAD
that also publish `H = E_K(0)` do not exist). -/

/-- Non-empty (block-aligned) AAD round-trips: exercises the `ad`-concatenation
and the `len(A)` field of the length block, both left at zero by Test Case 3. -/
example :
    gcmDecrypt tc3Cipher 0xcafebabefacedbaddecaf888
      [0xfeedfacedeadbeeffeedfacedeadbeef, 0x00112233445566778899aabbccddeeff]
      (gcmEncrypt tc3Cipher 0xcafebabefacedbaddecaf888
        [0xfeedfacedeadbeeffeedfacedeadbeef, 0x00112233445566778899aabbccddeeff]
        tc3Plain)
      = some tc3Plain := by decide

/-- AAD is authenticated: decrypting under AAD different from the one used to
encrypt is rejected (GHASH, hence the tag, binds the AAD). This is the strong
check — it fails if the AAD were dropped from the tag. -/
example :
    gcmDecrypt tc3Cipher 0xcafebabefacedbaddecaf888
      [0xfeedfacedeadbeeffeedfacedeadbeef, 0x00000000000000000000000000000000]
      (gcmEncrypt tc3Cipher 0xcafebabefacedbaddecaf888
        [0xfeedfacedeadbeeffeedfacedeadbeef, 0x00112233445566778899aabbccddeeff]
        tc3Plain)
      = none := by decide

/-- Empty message (`n = 0`): the ciphertext is empty and the tag is the pure tag
mask `E_K(J₀)`, since GHASH of the single all-zero length block is `0`. -/
example :
    gcmEncrypt tc3Cipher 0xcafebabefacedbaddecaf888 [] (#v[] : Vector (BitVec 128) 0)
      = ((#v[] : Vector (BitVec 128) 0), 0x3247184b3c4f69a44dbcd22887bbb418) := by decide

/-- Empty-message round-trip. -/
example :
    gcmDecrypt tc3Cipher 0xcafebabefacedbaddecaf888 []
      (gcmEncrypt tc3Cipher 0xcafebabefacedbaddecaf888 [] (#v[] : Vector (BitVec 128) 0))
      = some (#v[] : Vector (BitVec 128) 0) := by decide

/-- Ciphertext integrity: flipping one bit of the first ciphertext block makes the
recomputed tag mismatch, so decryption returns `none` (complements the
tampered-*tag* check above, which leaves `C` intact). -/
example :
    gcmDecrypt tc3Cipher 0xcafebabefacedbaddecaf888 []
      ( #v[ 0x42831ec2217774244b7221b784d0d49d,
            0xe3aa212f2c02a4e035c17e2329aca12e,
            0x21d514b25466931c7d8f6a5aac84aa05,
            0x1ba30b396a0aac973d58e091473f5985 ],
        0x4d5c2af327cd64a62cf35abd2ba6fab4 )
      = none := by decide
