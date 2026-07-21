/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.AESGCM.GaloisField

/-!
# GHASH (NIST SP 800-38D §6.4)

The keyed hash `GHASH_H` for GCM integrity: given `H = E_K(0)` and blocks
`X₁ … Xₘ`, fold `Y₀ = 0`, `Yᵢ = (Yᵢ₋₁ ⊕ Xᵢ) • H`, return `Yₘ`.

The input is a `List (BitVec 128)` of whole blocks (this spec is block-aligned,
so no partial-final-block padding); the caller (`Construction`) assembles
`A ‖ C ‖ (len(A) ‖ len(C))`.

## References

- [NIST_GCM] Dworkin. *NIST SP 800-38D*, 2007 — the normative GCM algorithm.
  https://csrc.nist.gov/pubs/sp/800/38/d/final
- [MV_GCM] McGrew, Viega. *The Galois/Counter Mode of Operation (GCM)*, 2005 —
  the original GCM proposal; source of the "Test Case 3" validation vector
  (App. B), which is not part of SP 800-38D. https://csrc.nist.gov/csrc/media/projects/block-cipher-techniques/documents/bcm/proposed-modes/gcm/gcm-revised-spec.pdf
-/

/-- `GHASH_H(X₁ ‖ … ‖ Xₘ)` (NIST SP 800-38D §6.4, Algorithm 2): fold
`Y ↦ (Y ⊕ Xᵢ) • H` from `Y = 0`. -/
def ghash (h : BitVec 128) (blocks : List (BitVec 128)) : BitVec 128 :=
  blocks.foldl (fun y x => gfmul (y ^^^ x) h) 0

/-! ## GCM validation vectors (McGrew–Viega Test Case 3, not in SP 800-38D):
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
