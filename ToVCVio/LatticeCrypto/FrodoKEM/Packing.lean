/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import ToVCVio.LatticeCrypto.FrodoKEM.Bits
import ToVCVio.LatticeCrypto.FrodoKEM.Parameters

/-!
# FrodoKEM matrix packing

`Frodo.Pack` and `Frodo.Unpack`, Algorithms 11 and 12 of `[CiC25]`, which are
the loop of Section 6.4 of `[LBES26]`. References are as in `Parameters.lean`.

Both documents give the same layout: each entry of an `r`-by-`c` matrix is
written as its `D` binary digits, most significant first, and the entries are
laid out row by row from row `0`, each row left to right, so that the entry in
row `i` and column `j` takes positions `(i * c + j) * D` onwards, for
`0 ≤ i < r` and `0 ≤ j < c`. Notice that the bit ordering within an entry is the
reverse of `Encoding.lean`'s, where a chunk is read least significant bit first.

The two documents stop in different places. Algorithms 11 and 12 stop at the
bit string. Section 6.4 goes one step further, packing it eight bits to a byte,
most significant bit first, and unpacking them back. The byte encoding the
packing functions use is Section 6.2.
This file is the algorithms, so the byte step is not here.

## Main definitions

Writing `D` and `q` for `p.D` and `p.q`, and reading the most significant bit
of an entry first throughout:

* `entryToBits : ZMod q → Vector Bool D`, the `D` binary digits of one entry,
  most significant first;
* `bitsToEntry : Vector Bool D → ZMod q`, reading those digits back;
* `Pack : FrodoMatrix p r c → Vector Bool (r * c * D)`, applying `entryToBits`
  to every entry and concatenating the results;
* `Unpack : Vector Bool (r * c * D) → FrodoMatrix p r c`, cutting the bit
  string every `D` bits and applying `bitsToEntry` to each piece.

`Pack` is `matrixToBitsWith` of `Bits.lean` and `Unpack` is `bitsToMatrixWith`,
at `D` bits per entry, which `Encoding.lean` uses at `B` bits instead.

## Main results

* `getElem_Pack`: bit `l` of entry `(i, j)` sits at position
  `(i * c + j) * D + l`, as a theorem.

The Section 6.4 bit order and layout are fixed by the `example`s beside their
definitions.
-/
namespace FrodoKEM

/-- The `D` bits of one entry, most significant first: line 5 of Algorithm 11,
and `b[(i * n2 + j)D + k] = c[D-1-k]` of Section 6.4, put binary digit
`D - 1 - l` of the entry at position `l`. -/
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

/-- `Frodo.Pack` (Algorithm 11 of `[CiC25]`, the loop of Section 6.4 of
`[LBES26]`): concatenate the `D`-bit entries, row by row from row `0` and each
row left to right, most significant bit of an entry first. Section 6.4 returns
the byte array this encodes to, which Algorithm 11 does not. -/
def Pack (p : Params) {r c : ℕ} (M : FrodoMatrix p r c) : Vector Bool (r * c * p.D) :=
  matrixToBitsWith (entryToBits p) M

/-- `Frodo.Unpack` (Algorithm 12), the inverse of `Pack`: read the `D`-bit
pieces back as entries, row by row from row `0` and each row left to right.
Section 6.4's `Unpack` decodes octets to that bit string first, which
Algorithm 12 does not. -/
def Unpack (p : Params) (r c : ℕ) (b : Vector Bool (r * c * p.D)) : FrodoMatrix p r c :=
  bitsToMatrixWith (bitsToEntry p) r c b

/-- The Section 6.4 layout on a fixed matrix: with `D = 15`, the bit string
that has only bits `14`, `28`, `43`, `44` and `57` set unpacks to
`![![1, 2], ![3, 4]]`. This fixes all three orders: the bits within an entry,
the entries along a row, and the rows themselves;
`Unpack` is used rather than `Pack` because `Pack` does not reduce: the
`Vector.flatten` inside `matrixToBitsWith` blocks it. -/
example : Unpack ParameterSet.FrodoKEM640.params 2 2
    (Vector.ofFn fun i : Fin (2 * 2 * 15) =>
      decide (i.val = 14 ∨ i.val = 28 ∨ i.val = 43 ∨ i.val = 44 ∨ i.val = 57)) =
      Matrix.of ![![(1 : ZMod 32768), 2], ![3, 4]] := by decide

/-- The bits of entry `(i, j)` sit at positions `(i * c + j) * D` onwards. -/
theorem getElem_Pack (p : Params) {r c : ℕ} (M : FrodoMatrix p r c) {i j l : ℕ}
    (hi : i < r) (hj : j < c) (hl : l < p.D) :
    (Pack p M)[(i * c + j) * p.D + l]'(bitIndex_lt hi hj hl) =
      (entryToBits p (M ⟨i, hi⟩ ⟨j, hj⟩))[l] :=
  getElem_matrixToBitsWith (entryToBits p) M hi hj hl

end FrodoKEM
