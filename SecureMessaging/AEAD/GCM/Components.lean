/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import Mathlib.Data.BitVec

/-!
# GCM building blocks (NIST SP 800-38D §6)

The cipher-agnostic §6 components that `Specification` assembles into GCM:

- `gfmul`: GF(2^128) multiplication `X • Y` (§6.3, Algorithm 1);
- `ghash`: the keyed hash `GHASH_H` (§6.4, Algorithm 2);
- `padBlocks`: reblock a bit string for GHASH (§5.2, §7.1);
- `inc₃₂` / `gctr`: counter increment (§6.2) and CTR mode (§6.5, Algorithm 3).

## References

- [NIST_GCM] Dworkin. *NIST SP 800-38D*, 2007. https://csrc.nist.gov/pubs/sp/800/38/d/final

## Bit ordering

NIST indexes a block `S = S₀ … S₁₂₇` most-significant-first, so `Sᵢ = S.getMsbD i`,
`LSB₁(S) = S.getLsbD 0`, `S ≫ 1 = S >>> 1`, and `R = 0xE1 <<< 120`.
-/

/-! ## GF(2^128) multiplication (NIST SP 800-38D §6.3) -/

/-- The GCM reduction constant `R = 0xE1 <<< 120` (NIST SP 800-38D §6.3), XORed in
by `gfmul` after each right shift. -/
def gcmReductionConst : BitVec 128 := (0xE1 : BitVec 128) <<< 120

/-- GF(2^128) block multiplication `X • Y` (NIST SP 800-38D §6.3, Algorithm 1).
`Z₀ = 0`, `V₀ = Y`; for `i = 0 … 127`: `Zᵢ₊₁ = Zᵢ ⊕ Vᵢ` if `Xᵢ` else `Zᵢ`,
`Vᵢ₊₁ = (Vᵢ ≫ 1) ⊕ R` if `LSB₁(Vᵢ)` else `Vᵢ ≫ 1`; returns `Z₁₂₈`. The `⊕ R`
reduces mod `x^128 + x^7 + x^2 + x + 1`. -/
def gfmul (x y : BitVec 128) : BitVec 128 :=
  (List.range 128 |>.foldl
    (fun (p : BitVec 128 × BitVec 128) (i : ℕ) =>
      let z := if x.getMsbD i then p.1 ^^^ p.2 else p.1
      let v := if p.2.getLsbD 0 then (p.2 >>> 1) ^^^ gcmReductionConst else p.2 >>> 1
      (z, v))
    ((0 : BitVec 128), y)).1

/-! ## GHASH (NIST SP 800-38D §6.4) -/

/-- `GHASH_H(X₁ ‖ … ‖ Xₘ)` (NIST SP 800-38D §6.4, Algorithm 2): fold
`Y ↦ (Y ⊕ Xᵢ) • H` from `Y = 0` over whole blocks (the caller zero-pads any final
partial block via `padBlocks`). -/
def ghash (h : BitVec 128) (blocks : List (BitVec 128)) : BitVec 128 :=
  blocks.foldl (fun y x => gfmul (y ^^^ x) h) 0

/-! ## Bit-string blocking for GHASH (NIST SP 800-38D §5.2, §7.1)

An `n`-bit string is modelled as `BitVec n`, bits indexed most-significant-first via
`getMsbD` (reads past the end return `false`), which supplies NIST's zero-padding of
a final partial block for free.
-/

/-- The `i`-th 128-bit block of `x` (0-indexed, most-significant block first), bits
past `len(x)` read as `0`, giving NIST's right zero-padding of the final partial block. -/
def paddedBlock {n : ℕ} (x : BitVec n) (i : ℕ) : BitVec 128 :=
  (BitVec.ofBoolListBE ((List.range 128).map fun t => x.getMsbD (128 * i + t))).cast (by simp)

/-- `x` split into `⌈len(x)/128⌉` blocks, final partial block zero-padded
(NIST SP 800-38D §7.1 steps 4–5, `A ‖ 0^v` and `C ‖ 0^u`). -/
def padBlocks {n : ℕ} (x : BitVec n) : List (BitVec 128) :=
  (List.range ((n + 127) / 128)).map (paddedBlock x)

/-! ## `inc₃₂` and GCTR (NIST SP 800-38D §6.2, §6.5) -/

/-- `inc₃₂` (NIST SP 800-38D §6.2): low 32-bit counter field `+1 mod 2^32`, high 96
bits fixed. -/
def inc32 (x : BitVec 128) : BitVec 128 :=
  x.extractLsb' 32 96 ++ (x.extractLsb' 0 32 + 1)

/-- The GCTR keystream truncated to `p` bits: `MSB_p(blocks[0] ‖ blocks[1] ‖ …)`,
bit `j` is bit `j % 128` of `blocks[j / 128]` (NIST SP 800-38D §6.5). -/
private def keystream (blocks : List (BitVec 128)) (p : ℕ) : BitVec p :=
  (BitVec.ofBoolListBE
    ((List.range p).map fun j => (blocks.getD (j / 128) 0).getMsbD (j % 128))).cast (by simp)

/-- The counter chain `[ICB, inc₃₂(ICB), …, inc₃₂ⁿ⁻¹(ICB)]` (`n` blocks), built
incrementally, one `inc₃₂` step per block (NIST SP 800-38D §6.5, `CBᵢ₊₁ = inc₃₂(CBᵢ)`). -/
def counterChain (icb : BitVec 128) : ℕ → List (BitVec 128)
  | 0 => []
  | n + 1 => icb :: counterChain (inc32 icb) n

/-- GCTR (NIST SP 800-38D §6.5, Algorithm 3, `GCTR_K`):
`Y = X ⊕ MSB_{len(X)}(CIPH_K(CB₁) ‖ CIPH_K(CB₂) ‖ …)`, counter chain
`CBᵢ = inc₃₂ⁱ⁻¹(ICB)` (`counterChain`, one cipher call per block). GCM supplies
`ICB = inc₃₂(J₀)`. The keystream is independent of `X`, so `gctr` is an involution
(`gctr_involution`). -/
def gctr {K : Type} (ciph : K → BitVec 128 → BitVec 128) (k : K) (icb : BitVec 128)
    {p : ℕ} (x : BitVec p) : BitVec p :=
  x ^^^ keystream ((counterChain icb ((p + 127) / 128)).map (ciph k)) p

/-- `gctr ciph k icb` is an involution (`(x ⊕ ks) ⊕ ks = x`). -/
theorem gctr_involution {K : Type} (ciph : K → BitVec 128 → BitVec 128) (k : K)
    (icb : BitVec 128) {p : ℕ} (x : BitVec p) :
    gctr ciph k icb (gctr ciph k icb x) = x := by
  simp only [gctr, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
