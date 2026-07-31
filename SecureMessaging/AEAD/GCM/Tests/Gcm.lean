/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.GCM.Gcm
import SecureMessaging.AEAD.GCM.Tests.TestVectors

/-!
# GCM building-block known-answer tests (not part of the spec)

Known-answer checks for `gfmul`, `ghash`, `inc₃₂`, and `gctr` against the
McGrew–Viega *Test Case 3* vector. Not part of the spec; see `Gcm` for the
algorithms and `TestVectors` for the shared `tc3Cipher` cipher table.

## References

- [MV_GCM] McGrew, Viega. *The Galois/Counter Mode of Operation (GCM)*, 2005 —
  the original GCM proposal; source of the "Test Case 3" validation vector
  (App. B), which is not part of SP 800-38D. https://csrc.nist.rip/groups/ST/toolkit/BCM/documents/proposedmodes/gcm/gcm-spec.pdf
-/

/-! ### `gfmul` (McGrew–Viega GCM spec, Test Case 3 — not in SP 800-38D) -/

/-- `Y₁ = C₁ • H`, the first GHASH iterate (since `Y₀ = 0`). -/
example :
    gfmul 0x42831ec2217774244b7221b784d0d49c 0xb83b533708bf535d0aa6e52980d53b78
      = 0x59ed3f2bb1a0aaa07c9f56c6a504647b := by decide

/-- Commutativity spot-check: swapping the operands of `gfmul` gives the same
Test Case 3 value (`•` is commutative in general; this checks one pair). -/
example :
    gfmul 0xb83b533708bf535d0aa6e52980d53b78 0x42831ec2217774244b7221b784d0d49c
      = 0x59ed3f2bb1a0aaa07c9f56c6a504647b := by decide

/-! ### `ghash` (McGrew–Viega Test Case 3, not in SP 800-38D):
`H`, ciphertext blocks `C₁ … C₄`, length block `0^64 ‖ [0x200]₆₄`. -/

/-- Intermediate `Y₁ = C₁ • H`. -/
example : ghash 0xb83b533708bf535d0aa6e52980d53b78 [0x42831ec2217774244b7221b784d0d49c]
    = 0x59ed3f2bb1a0aaa07c9f56c6a504647b := by decide

/-- Intermediate `Y₄` (fold over `C₁ … C₄`, no length block). -/
example :
    ghash 0xb83b533708bf535d0aa6e52980d53b78
      [ 0x42831ec2217774244b7221b784d0d49c,
        0xe3aa212f2c02a4e035c17e2329aca12e,
        0x21d514b25466931c7d8f6a5aac84aa05,
        0x1ba30b396a0aac973d58e091473f5985 ]
      = 0x4796cf49464704b5dd91f159bb1b7f95 := by decide

/-- `GHASH_H` on Test Case 3 (empty AAD): input `C ‖ (len(A) ‖ len(C))`. -/
example :
    ghash 0xb83b533708bf535d0aa6e52980d53b78
      [ 0x42831ec2217774244b7221b784d0d49c,
        0xe3aa212f2c02a4e035c17e2329aca12e,
        0x21d514b25466931c7d8f6a5aac84aa05,
        0x1ba30b396a0aac973d58e091473f5985,
        0x00000000000000000000000000000200 ]
      = 0x7f1b32b81b820d02614f8895ac1d4eac := by decide

/-! ### `inc₃₂` and `gctr` (McGrew–Viega Test Case 3, not in SP 800-38D;
`IV = cafebabefacedbaddecaf888`). The counter blocks below start from the
pre-counter block `J₀ = 0xcafebabefacedbaddecaf888_00000001` (i.e. `IV ‖ 0^31 ‖ 1`,
assembled in `Construction`); `inc₃₂(J₀)` is the initial counter block `ICB`. -/

/-- `inc₃₂(J₀)` is the first plaintext counter block (McGrew–Viega counter `Y₁`,
distinct from the GHASH iterate `Y₁`). -/
example :
    inc32 0xcafebabefacedbaddecaf88800000001 = 0xcafebabefacedbaddecaf88800000002 := by
  decide

/-- `inc₃₂` wraps `mod 2^32` without touching the high 96 bits. -/
example :
    inc32 0xcafebabefacedbaddecaf888ffffffff = 0xcafebabefacedbaddecaf88800000000 := by
  decide

-- `gctr` maps the four-block (512-bit) Test Case 3 plaintext to its ciphertext
-- (from `ICB = inc₃₂(J₀)`), exercising the counter-keystream path end to end.
-- `native_decide` because kernel `decide` cannot reduce a `BitVec 512` literal
-- (the `2^512` modulus exceeds the exponentiation threshold).
set_option linter.style.longLine false in
set_option linter.style.nativeDecide false in
example :
    gctr tc3Cipher () (inc32 0xcafebabefacedbaddecaf88800000001)
      (0xd9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255 : BitVec 512)
      = 0x42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091473f5985 := by
  native_decide
