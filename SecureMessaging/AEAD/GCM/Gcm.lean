/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import Mathlib.Data.BitVec
import SecureMessaging.AEAD.GCM.TestVectors

/-!
# GCM building blocks: GF(2^128) multiplication, GHASH, GCTR (NIST SP 800-38D §6)

The cipher-agnostic §6 components that `Construction` assembles into GCM:

- **`gfmul`** — GF(2^128) block multiplication `X • Y` (§6.3, Algorithm 1);
- **`ghash`** — the keyed hash `GHASH_H` (§6.4, Algorithm 2), a `gfmul` fold;
- **`inc₃₂` / `gctr`** — the counter increment (§6.2) and CTR mode (§6.5,
  Algorithm 3).

The §7 *assembly* — the pre-counter block `J₀` (§7.1), `gcmEncrypt`/`gcmDecrypt`,
and the AEAD scheme — lives in `Construction`. GCM runs `gctr` on the initial
counter block `ICB = inc₃₂(J₀)`, and `E_K(J₀)` is the tag mask; both `J₀` and the
tag mask are defined there, next to the algorithm that uses them.

## References

- [NIST_GCM] Dworkin. *NIST SP 800-38D*, 2007 — the normative GCM algorithm.
  https://csrc.nist.gov/pubs/sp/800/38/d/final
- [MV_GCM] McGrew, Viega. *The Galois/Counter Mode of Operation (GCM)*, 2005 —
  the original GCM proposal; source of the "Test Case 3" validation vector
  (App. B), which is not part of SP 800-38D. https://csrc.nist.gov/csrc/media/projects/block-cipher-techniques/documents/bcm/proposed-modes/gcm/gcm-revised-spec.pdf

## Bit ordering

NIST indexes a block `S = S₀ … S₁₂₇` leftmost-first, so `S₀` is the most
significant bit (as in the hex encoding). The map to `BitVec 128`: `Sᵢ` is
`S.getMsbD i`, `LSB₁(S)` is `S.getLsbD 0`, the right shift `S ≫ 1` is `S >>> 1`,
and `R = 11100001 ‖ 0^120 = 0xE1 <<< 120`.
-/

/-! ## GF(2^128) multiplication (NIST SP 800-38D §6.3) -/

/-- The GCM reduction constant `R = 11100001 ‖ 0^120 = 0xE1 <<< 120`
(NIST SP 800-38D §6.3), XORed in by `gfmul` after each right shift. -/
def gcmReductionConst : BitVec 128 := (0xE1 : BitVec 128) <<< 120

/-- GF(2^128) block multiplication `X • Y` (NIST SP 800-38D §6.3, Algorithm 1).

With `Z₀ = 0`, `V₀ = Y`, for `i = 0 … 127`: `Zᵢ₊₁ = Zᵢ ⊕ Vᵢ` if `Xᵢ = 1` else
`Zᵢ`; `Vᵢ₊₁ = (Vᵢ ≫ 1) ⊕ R` if `LSB₁(Vᵢ) = 1` else `Vᵢ ≫ 1`. Returns `Z₁₂₈`.

The `⊕ R` step reduces the `x^128` overflow from `Vᵢ ≫ 1` via
`x^128 ≡ x^7 + x^2 + x + 1` in `GF(2^128)` (modulus `x^128 + x^7 + x^2 + x + 1`). -/
def gfmul (x y : BitVec 128) : BitVec 128 :=
  (List.range 128 |>.foldl
    (fun (p : BitVec 128 × BitVec 128) (i : ℕ) =>
      let z := if x.getMsbD i then p.1 ^^^ p.2 else p.1
      let v := if p.2.getLsbD 0 then (p.2 >>> 1) ^^^ gcmReductionConst else p.2 >>> 1
      (z, v))
    ((0 : BitVec 128), y)).1

/-! ### GCM validation vectors (McGrew–Viega GCM spec, Test Case 3 — not in
SP 800-38D) -/

/-- `Y₁ = C₁ • H`, the first GHASH iterate (since `Y₀ = 0`). -/
example :
    gfmul 0x42831ec2217774244b7221b784d0d49c 0xb83b533708bf535d0aa6e52980d53b78
      = 0x59ed3f2bb1a0aaa07c9f56c6a504647b := by decide

/-- Commutativity spot-check: swapping the operands of `gfmul` gives the same
Test Case 3 value (`•` is commutative in general; this checks one pair). -/
example :
    gfmul 0xb83b533708bf535d0aa6e52980d53b78 0x42831ec2217774244b7221b784d0d49c
      = 0x59ed3f2bb1a0aaa07c9f56c6a504647b := by decide

/-! ## GHASH (NIST SP 800-38D §6.4)

The keyed hash `GHASH_H`: from `H = E_K(0)` and blocks `X₁ … Xₘ`, fold `Y₀ = 0`,
`Yᵢ = (Yᵢ₋₁ ⊕ Xᵢ) • H`, return `Yₘ`. It consumes *whole* blocks; NIST's zero-padding
of the final partial `A`/`C` blocks (§7.1 steps 4–5) is the caller's job
(`Construction`, via `padBlocks`).
-/

/-- `GHASH_H(X₁ ‖ … ‖ Xₘ)` (NIST SP 800-38D §6.4, Algorithm 2): fold
`Y ↦ (Y ⊕ Xᵢ) • H` from `Y = 0`. -/
def ghash (h : BitVec 128) (blocks : List (BitVec 128)) : BitVec 128 :=
  blocks.foldl (fun y x => gfmul (y ^^^ x) h) 0

/-! ### GCM validation vectors (McGrew–Viega Test Case 3, not in SP 800-38D):
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

/-! ## Bit-string blocking for GHASH (NIST SP 800-38D §5.2, §7.1)

NIST's inputs are arbitrary-length *bit strings*; an `n`-bit string `X` is modelled as
`BitVec n` (so the width `n` is `len(X)`), bits indexed most-significant-first via
`getMsbD`, so reads past the end return `false`; this supplies, for free, the zero-padding
NIST appends to a final partial block.

`paddedBlock`/`padBlocks` reblock these bit strings, per §7.1 steps 4–5, into the
whole 128-bit blocks that GHASH consumes, zero-padding the final partial block.
-/

/-- The `i`-th padded 128-bit block of the bit string `x` (0-indexed, most-significant
block first), with bits past `len(x)` read as `0` — NIST's right zero-padding of
the final partial block. Bit `t` of block `i` is bit `128·i + t` of `x`. -/
def paddedBlock {n : ℕ} (x : BitVec n) (i : ℕ) : BitVec 128 :=
  (BitVec.ofBoolListBE ((List.range 128).map fun t => x.getMsbD (128 * i + t))).cast (by simp)

/-- `x` split into `⌈len(x)/128⌉` blocks with the final partial block zero-padded
(NIST SP 800-38D §7.1 steps 4–5, `A ‖ 0^v` and `C ‖ 0^u`). GHASH folds over these. -/
def padBlocks {n : ℕ} (x : BitVec n) : List (BitVec 128) :=
  (List.range ((n + 127) / 128)).map (paddedBlock x)

/-! ## `inc₃₂` and GCTR (NIST SP 800-38D §6.2, §6.5) -/

/-- The `inc₃₂` increment (NIST SP 800-38D §6.2): low 32-bit counter field
`+1 mod 2^32`, high 96 bits fixed. -/
def inc32 (x : BitVec 128) : BitVec 128 :=
  x.extractLsb' 32 96 ++ (x.extractLsb' 0 32 + 1)

/-- The GCTR keystream truncated to `p` bits: `MSB_p(blocks[0] ‖ blocks[1] ‖ …)`,
where `blocks[i] = CIPH_K(CBᵢ)` and bit `j` is bit `j % 128` of `blocks[j / 128]`
(NIST SP 800-38D §6.5). -/
private def keystream (blocks : List (BitVec 128)) (p : ℕ) : BitVec p :=
  (BitVec.ofBoolListBE
    ((List.range p).map fun j => (blocks.getD (j / 128) 0).getMsbD (j % 128))).cast (by simp)

/-- The counter chain `[ICB, inc₃₂(ICB), …, inc₃₂ⁿ⁻¹(ICB)]` (`n` blocks), generated
**incrementally** — each block is one `inc₃₂` step from the previous, not recomputed
from `ICB` (NIST SP 800-38D §6.5, `CBᵢ₊₁ = inc₃₂(CBᵢ)`). -/
def counterChain (icb : BitVec 128) : ℕ → List (BitVec 128)
  | 0 => []
  | n + 1 => icb :: counterChain (inc32 icb) n

/-- GCTR over an arbitrary-length bit string (NIST SP 800-38D §6.5, Algorithm 3,
`GCTR_K`): `Y = X ⊕ MSB_{len(X)}(CIPH_K(CB₁) ‖ CIPH_K(CB₂) ‖ …)`, counter chain
`CBᵢ = inc₃₂ⁱ⁻¹(ICB)` (built incrementally by `counterChain`, one cipher call per
block). The keyed cipher is `ciph k = CIPH_K`; GCM supplies `ICB = inc₃₂(J₀)`. Since
the keystream is independent of `X`, `gctr` is an involution (`gctr_involution`). -/
def gctr {K : Type} (ciph : K → BitVec 128 → BitVec 128) (k : K) (icb : BitVec 128)
    {p : ℕ} (x : BitVec p) : BitVec p :=
  x ^^^ keystream ((counterChain icb ((p + 127) / 128)).map (ciph k)) p

/-- `gctr ciph k icb` is an involution: it XORs a keystream independent of the
input, so `(x ⊕ ks) ⊕ ks = x` — the basis of GCM decryption. -/
theorem gctr_involution {K : Type} (ciph : K → BitVec 128 → BitVec 128) (k : K)
    (icb : BitVec 128) {p : ℕ} (x : BitVec p) :
    gctr ciph k icb (gctr ciph k icb x) = x := by
  simp only [gctr, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-! ### GCM validation vector (McGrew–Viega Test Case 3, not in SP 800-38D;
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
