/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import ToVCVio.LatticeCrypto.FrodoKEM.Encoding

/-!
# FrodoKEM matrix packing

`Frodo.Pack` and `Frodo.Unpack`, Algorithms 11 and 12 of `[CiC25]`, with the
octet conversion of Section 7.2 of `[ABD+25]`. References are as in
`Encoding.lean`.

The two documents draw the boundary differently. Algorithm 11 takes a matrix to
a bit string of length `r * c * D`, leaving the octets to the caller; `[ABD+25]`
gives the same layout as step 1 of Section 7.4 and then, in step 2, outputs its
octet encoding, so its `Pack` is `bitsToBytesPack` after this one. `Pack` and
`Unpack` here are Algorithms 11 and 12, on bit strings, and a caller composes
them with the Section 7.2 conversion below.

The layout is common to both, Algorithm 11 and step 1 of Section 7.4: each
entry of an `r`-by-`c` matrix is written as its `D` binary digits, most
significant first, and the entries are laid out row by row, each row left to
right, so that the entry in row `i` and column `j` takes positions
`(i * c + j) * D` onwards of the bit string, for `0 ≤ i < r` and `0 ≤ j < c`.
Section 7.2 then writes bit `8 * a + t` of a bit string as digit `7 - t` of
octet `a`, for `0 ≤ t < 8`.

Sections 7.1 and 7.3 of `Encoding.lean` read the least significant bit first
instead, so both conversions here are stated separately from theirs, as their
own sections of the specification state them. Only the proofs are shared:
Section 7.4's layout is `Encoding.lean`'s Section 7.3 layout at a different
codec and width, so the `…With` definitions and lemmas there serve both, and
the `…_eq` lemmas below identify each definition here with one.

## Main definitions

* `byteToBitsPack`, `bitsToBytePack` and their vector forms `bytesToBitsPack`,
  `bitsToBytesPack`: the Section 7.2 octet conversion;
* `entryToBits`, `bitsToEntry`: one entry as `D` bits;
* `Pack`, `Unpack`, with `Pack_eq` and `Unpack_eq` identifying them with
  `Encoding.lean`'s shared matrix layer.

## Main results

* `bitsToBytesPack_bytesToBitsPack` and `bytesToBitsPack_bitsToBytesPack`;
* `getElem_bytesToBitsPack` and `getElem_Pack`: the position formulas this
  header states in prose, as theorems;
* `Unpack_Pack` and `Pack_Unpack`. Both take a `Params.WellFormed`, for its
  `q_eq`, since `entryToBits` retains only `D` bits.

The Section 7.2 octet order and the Section 7.4 bit order and layout, which the
round trips cannot fix, are fixed by the `example`s beside their definitions.
-/
namespace FrodoKEM

/-- The `D` bits of one entry, most significant first: line 5 of Algorithm 11,
and step 1.1.2 of Section 7.4, put binary digit `D - 1 - l` of the entry at
position `l`. -/
def entryToBits (p : Params) (x : ZMod p.q) : Vector Bool p.D :=
  Vector.ofFn fun l => x.val.testBit (p.D - 1 - l.val)

/-- The convention on a fixed entry: with `D = 15`, the entry `5` reads as
twelve zeros and then `[1, 0, 1]`, most significant first. -/
example : (entryToBits ParameterSet.FrodoKEM640.params 5).toList =
    [false, false, false, false, false, false, false, false, false, false, false,
     false, true, false, true] := by decide

/-- The entry with the given `D` bits, most significant first. -/
def bitsToEntry (p : Params) (v : Vector Bool p.D) : ZMod p.q :=
  ((Nat.ofBits fun l : Fin p.D => v[p.D - 1 - l.val]'(by omega) : ℕ) : ZMod p.q)

/-- `Frodo.Pack` (Algorithm 11 of `[CiC25]`, step 1 of Section 7.4 of
`[ABD+25]`): concatenate the `D`-bit entries, row by row, each most significant
bit first. Section 7.4 goes on to encode the result as octets; that step is
`bitsToBytesPack`. -/
def Pack (p : Params) {r c : ℕ} (M : FrodoMatrix p r c) : Vector Bool (r * c * p.D) :=
  (Vector.ofFn fun idx : Fin (r * c) =>
    entryToBits p (M idx.divNat idx.modNat)).flatten

/-- `Frodo.Unpack` (Algorithm 12), the inverse of `Pack`: read the `D`-bit
blocks back as entries, row by row. Section 7.4's `Unpack` decodes its octets
first; that step is `bytesToBitsPack`. -/
def Unpack (p : Params) {r c : ℕ} (b : Vector Bool (r * c * p.D)) : FrodoMatrix p r c :=
  Matrix.of fun i j => bitsToEntry p (Vector.ofFn fun l =>
    b[(i.val * c + j.val) * p.D + l.val]'(bitIndex_lt i.isLt j.isLt l.isLt))

/-- The Section 7.4 layout on a fixed matrix: with `D = 15`, the bit string
that has only bits `14` and `28` set unpacks to the row `[1, 2]`. This fixes
both orders the round trips leave open, the bits within an entry and the
entries along a row; `Unpack` is used rather than `Pack` because
`Vector.flatten` does not reduce. -/
example : Unpack ParameterSet.FrodoKEM640.params
    (Vector.ofFn fun i : Fin (1 * 2 * 15) => decide (i.val = 14 ∨ i.val = 28)) =
      Matrix.of ![![(1 : ZMod 32768), 2]] := by decide

/-- `Pack` is the shared layer at the Section 7.4 layout. -/
theorem Pack_eq (p : Params) {r c : ℕ} (M : FrodoMatrix p r c) :
    Pack p M = matrixToBitsWith (entryToBits p) M := rfl

/-- `Unpack` is the shared layer at the Section 7.4 layout. -/
theorem Unpack_eq (p : Params) {r c : ℕ} (b : Vector Bool (r * c * p.D)) :
    Unpack p b = bitsToMatrixWith (bitsToEntry p) b := rfl

/-- The bits of entry `(i, j)` sit at positions `(i * c + j) * D` onwards. -/
theorem getElem_Pack (p : Params) {r c : ℕ} (M : FrodoMatrix p r c) {i j l : ℕ}
    (hi : i < r) (hj : j < c) (hl : l < p.D) :
    (Pack p M)[(i * c + j) * p.D + l]'(bitIndex_lt hi hj hl) =
      (entryToBits p (M ⟨i, hi⟩ ⟨j, hj⟩))[l] := by
  rw [Pack_eq]
  exact getElem_matrixToBitsWith (entryToBits p) M hi hj hl

/-- An entry is recovered from its `D` bits. `q = 2 ^ D` is needed here and in
`entryToBits_bitsToEntry`: `entryToBits` keeps only `D` bits, so no larger
modulus is recoverable. -/
theorem bitsToEntry_entryToBits (p : Params) (hw : p.WellFormed) (x : ZMod p.q) :
    bitsToEntry p (entryToBits p x) = x := by
  haveI : NeZero p.q := ⟨by rw [hw.q_eq]; positivity⟩
  rw [bitsToEntry]
  simp only [entryToBits, Vector.getElem_ofFn,
    show ∀ l : Fin p.D, p.D - 1 - (p.D - 1 - l.val) = l.val from fun l => by omega,
    Nat.ofBits_testBit, ← hw.q_eq, ZMod.natCast_mod, ZMod.natCast_zmod_val]

/-- The `D` bits of an entry are recovered from it. -/
theorem entryToBits_bitsToEntry (p : Params) (hw : p.WellFormed) (v : Vector Bool p.D) :
    entryToBits p (bitsToEntry p v) = v := by
  haveI : NeZero p.q := ⟨by rw [hw.q_eq]; positivity⟩
  apply Vector.ext
  intro l hl
  rw [entryToBits, Vector.getElem_ofFn, bitsToEntry, ZMod.val_natCast, hw.q_eq,
    Nat.mod_eq_of_lt (Nat.ofBits_lt_two_pow _), Nat.testBit_ofBits]
  simp only [show p.D - 1 - l < p.D by omega, dif_pos]
  congr 1
  omega

/-- `Frodo.Unpack` inverts `Frodo.Pack`. -/
theorem Unpack_Pack (p : Params) (hw : p.WellFormed) {r c : ℕ} (M : FrodoMatrix p r c) :
    Unpack p (Pack p M) = M := by
  rw [Unpack_eq, Pack_eq]
  exact bitsToMatrixWith_matrixToBitsWith (bitsToEntry_entryToBits p hw) M

/-- `Frodo.Pack` inverts `Frodo.Unpack`. -/
theorem Pack_Unpack (p : Params) (hw : p.WellFormed) {r c : ℕ}
    (b : Vector Bool (r * c * p.D)) : Pack p (Unpack p b) = b := by
  rw [Pack_eq, Unpack_eq]
  exact matrixToBitsWith_bitsToMatrixWith (entryToBits_bitsToEntry p hw) b

end FrodoKEM
