/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import Mathlib.Data.BitVec

/-!
# GF(2^128) multiplication (NIST SP 800-38D §6.3)

The concrete GCM field arithmetic: `gfmul`, NIST's block multiplication `X • Y`
(§6.3, Algorithm 1). NIST's `•` is spelled `gfmul` here; no Lean `•` notation is
introduced. The counter primitives `inc₃₂` (§6.2) and `j0` (§7.1) live with the
CTR mode they serve, in `GCtr.lean`; this module is field arithmetic only.

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

/-! ## GCM validation vectors (McGrew–Viega GCM spec, Test Case 3 — not in
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
