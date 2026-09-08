/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import ToVCVio.LatticeCrypto.FrodoKEM.Encoding

/-!
# FrodoKEM matrix packing

`Frodo.Pack` and `Frodo.Unpack`, Algorithms 11 and 12 of `[CiC25]`, which are
the loop of Section 6.4 of `[LBES26]`. References are as in `Parameters.lean`.

Both documents give the same layout: each entry of an `r`-by-`c` matrix is
written as its `D` binary digits, most significant first, and the entries are
laid out row by row from row `0`, each row left to right, so that the entry in
row `i` and
column `j` takes positions `(i * c + j) * D` onwards of the bit string, for
`0 ≤ i < r` and `0 ≤ j < c`. Notice that the bit ordering within an entry is the
reverse of `Encoding.lean`'s, where a chunk is read least significant bit first.

The two documents stop in different places. Algorithm 11 returns that bit
string; Section 6.4's `Pack` goes on to return the byte array it encodes to,
by Section 6.2, and its `Unpack` decodes those bytes before reading the entries
back. `Pack` and `Unpack` here are the algorithms, so that byte conversion is
not part of this file.

## Main definitions

* `entryToBits`, `bitsToEntry`: one entry as `D` bits;
* `Pack`, `Unpack`, which are `matrixToBitsWith` and `bitsToMatrixWith` of
  `Bits.lean` at `entryToBits` and `bitsToEntry`.

## Main results

* `getElem_Pack`: the position formula this header states in prose, as a
  theorem;
* `Unpack_Pack` and `Pack_Unpack`. Both take a `Params.WellFormed`, for its
  `q_eq`, since `entryToBits` retains only `D` bits.

The Section 6.4 bit order and layout, which the round trips cannot fix, are
fixed by the `example`s beside their definitions.
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
Section 6.4's
`Unpack` decodes octets to that bit string first, which Algorithm 12 does
not. -/
def Unpack (p : Params) (r c : ℕ) (b : Vector Bool (r * c * p.D)) : FrodoMatrix p r c :=
  bitsToMatrixWith (bitsToEntry p) r c b

/-- The Section 6.4 layout on a fixed matrix: with `D = 15`, the bit string
that has only bits `14`, `28`, `43`, `44` and `57` set unpacks to
`![![1, 2], ![3, 4]]`. This fixes all three orders the round trips leave open,
the bits within an entry, the entries along a row, and the rows themselves;
`Unpack` is used rather than `Pack` because `Vector.flatten` does not reduce. -/
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
    Unpack p r c (Pack p M) = M :=
  bitsToMatrixWith_matrixToBitsWith (bitsToEntry_entryToBits p hw) M

/-- `Frodo.Pack` inverts `Frodo.Unpack`. -/
theorem Pack_Unpack (p : Params) (hw : p.WellFormed) (r c : ℕ)
    (b : Vector Bool (r * c * p.D)) : Pack p (Unpack p r c b) = b :=
  matrixToBitsWith_bitsToMatrixWith (entryToBits_bitsToEntry p hw) r c b

end FrodoKEM
