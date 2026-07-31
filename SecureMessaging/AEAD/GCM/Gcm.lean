/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import Mathlib.Data.BitVec

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
