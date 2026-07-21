/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import Mathlib.Data.BitVec

/-!
# GCTR, `inc₃₂`, and the pre-counter block `J₀` (NIST SP 800-38D §6.2, §6.5, §7.1)

The counter side of GCM: the counter increment `inc₃₂` (§6.2), CTR mode `gctr`
(§6.5), and the pre-counter block `J₀` (§7.1).

`gctr` is CTR mode over the block cipher `E_K` (§6.5, Algorithm 3):
`Yᵢ = Xᵢ ⊕ E_K(CBᵢ)`, `CB₁ = ICB`, `CBᵢ₊₁ = inc₃₂(CBᵢ)`. Because each block is
XORed with a keystream that depends only on `ICB`, `gctr E icb` is an involution:
applying it twice with the same `ICB` recovers the input.

We model the message as a fixed-length `Vector (BitVec 128) n` of *whole* blocks,
so block `i` (0-indexed, i.e. NIST's block `i+1`) uses `inc₃₂ⁱ(ICB)` and the NIST
partial-final-block case (§6.5: the last block XORed with the *truncated*
keystream `MSBₗₑₙ(E_K(CBₙ))`) cannot arise.
This whole-block restriction is a formalization artifact imposed at the AEAD layer: the
security game samples a random ciphertext, so the ciphertext type must be
uniformly samplable, hence fixed-length (see `Construction`). It is therefore
*narrower* than libsignal's plain-GCM usage (`rust/crypto/src/aes_gcm.rs`), which
does encrypt arbitrary-length, non-block-aligned messages; the libsignal-faithful
specializations here are instead the one-time key + fresh 96-bit nonce, the 128-bit
tag, and AES-256. Can be extended later on if we find that the restriction is a
problem.

`J₀` is the *pre-counter block* (§7.1); GCM runs `gctr` on the *initial counter
block* `ICB = inc₃₂(J₀)`, while `E_K(J₀)` itself is the tag mask.

## References

- [NIST_GCM] Dworkin. *NIST SP 800-38D*, 2007 — the normative GCM algorithm.
  https://csrc.nist.gov/pubs/sp/800/38/d/final
- [MV_GCM] McGrew, Viega. *The Galois/Counter Mode of Operation (GCM)*, 2005 —
  the original GCM proposal; source of the "Test Case 3" validation vector
  (App. B), which is not part of SP 800-38D. https://csrc.nist.gov/csrc/media/projects/block-cipher-techniques/documents/bcm/proposed-modes/gcm/gcm-revised-spec.pdf
-/

/-- The `inc₃₂` increment (NIST SP 800-38D §6.2): low 32-bit counter field
`+1 mod 2^32`, high 96 bits fixed. -/
def inc32 (x : BitVec 128) : BitVec 128 :=
  x.extractLsb' 32 96 ++ (x.extractLsb' 0 32 + 1)

/-- The pre-counter block `J₀ = IV ‖ 0^31 ‖ 1` (96-bit-IV path, NIST SP 800-38D
§7.1). `E_K(J₀)` is the tag mask; the initial counter block for `gctr` is
`inc₃₂(J₀)`. -/
def j0 (nonce : BitVec 96) : BitVec 128 := nonce ++ (0 : BitVec 31) ++ (1 : BitVec 1)

/-- GCTR over a fixed-length block vector (NIST SP 800-38D §6.5, Algorithm 3):
block `i` XORed with `E_K(inc₃₂ⁱ(ICB))`. An involution for fixed `E` and `ICB`:
`gctr E icb (gctr E icb x) = x`. -/
def gctr {n : ℕ} (E : BitVec 128 → BitVec 128) (icb : BitVec 128)
    (blocks : Vector (BitVec 128) n) : Vector (BitVec 128) n :=
  blocks.mapFinIdx (fun i x _ => x ^^^ E (Nat.iterate inc32 i icb))

/-! ## GCM validation vector (McGrew–Viega Test Case 3, not in SP 800-38D;
`IV = cafebabefacedbaddecaf888`) -/

/-- `inc₃₂(J₀)` is the first plaintext counter block (McGrew–Viega counter `Y₁`,
distinct from the GHASH iterate `Y₁`). -/
example :
    inc32 0xcafebabefacedbaddecaf88800000001 = 0xcafebabefacedbaddecaf88800000002 := by
  decide

/-- `inc₃₂` wraps `mod 2^32` without touching the high 96 bits. -/
example :
    inc32 0xcafebabefacedbaddecaf888ffffffff = 0xcafebabefacedbaddecaf88800000000 := by
  decide

/-- Test scaffolding: the `E_K(CBᵢ)` keystream outputs of GCM Test Case 3 keyed
by counter block `CBᵢ`, so `gctr` can be checked against the vector without AES. -/
private def tc3Cipher (cb : BitVec 128) : BitVec 128 :=
  if cb = 0xcafebabefacedbaddecaf88800000001 then 0x3247184b3c4f69a44dbcd22887bbb418
  else if cb = 0xcafebabefacedbaddecaf88800000002 then 0x9bb22ce7d9f372c1ee2b28722b25f206
  else if cb = 0xcafebabefacedbaddecaf88800000003 then 0x650d887c3936533a1b8d4e1ea39d2b5c
  else if cb = 0xcafebabefacedbaddecaf88800000004 then 0x3de91827c10e9a4f5240647ee5221f20
  else if cb = 0xcafebabefacedbaddecaf88800000005 then 0xaac9e6ccc0074ac0873b9ba85d908bd0
  else if cb = 0 then 0xb83b533708bf535d0aa6e52980d53b78
  else 0

/-- `gctr` maps the Test Case 3 plaintext to its ciphertext. -/
example :
    gctr tc3Cipher (inc32 (j0 0xcafebabefacedbaddecaf888))
      #v[ 0xd9313225f88406e5a55909c5aff5269a,
          0x86a7a9531534f7da2e4c303d8a318a72,
          0x1c3c0c95956809532fcf0e2449a6b525,
          0xb16aedf5aa0de657ba637b391aafd255 ]
      = #v[ 0x42831ec2217774244b7221b784d0d49c,
            0xe3aa212f2c02a4e035c17e2329aca12e,
            0x21d514b25466931c7d8f6a5aac84aa05,
            0x1ba30b396a0aac973d58e091473f5985 ] := by decide

/-- `gctr E icb` is an involution (self-inverse for fixed `E` and `ICB`). -/
example :
    gctr tc3Cipher (inc32 (j0 0xcafebabefacedbaddecaf888))
      (gctr tc3Cipher (inc32 (j0 0xcafebabefacedbaddecaf888))
        #v[ 0xd9313225f88406e5a55909c5aff5269a,
            0x86a7a9531534f7da2e4c303d8a318a72,
            0x1c3c0c95956809532fcf0e2449a6b525,
            0xb16aedf5aa0de657ba637b391aafd255 ])
      = #v[ 0xd9313225f88406e5a55909c5aff5269a,
            0x86a7a9531534f7da2e4c303d8a318a72,
            0x1c3c0c95956809532fcf0e2449a6b525,
            0xb16aedf5aa0de657ba637b391aafd255 ] := by decide
