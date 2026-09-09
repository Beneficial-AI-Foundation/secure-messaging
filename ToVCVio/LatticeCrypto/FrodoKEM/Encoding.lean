/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import ToVCVio.LatticeCrypto.FrodoKEM.Bits
import ToVCVio.LatticeCrypto.FrodoKEM.Parameters
import LatticeCrypto.Ring.Norms

/-!
# FrodoKEM message encoding

`Frodo.Encode` and `Frodo.Decode`.

References are as in `Parameters.lean`. The maps on bit strings are named
in Section 3.3 and given in Appendix B of `[CiC25]`. `[LBES26]` gives the
same maps as pseudocode in Section 6.3, with the chunking layout written out.

## Main definitions

Encoding places `B` bits in each entry of an `mbar`-by-`nbar` matrix over
`ZMod q`. Writing `B`, `D` and `q` for `p.B`, `p.D` and `p.q`, and reading the
least significant bit first throughout, the scalar maps are

* `ec : ZMod (2 ^ B) → ZMod q`, `k ↦ k * q / 2 ^ B` — written `k * 2 ^ (D - B)`,
  which agrees under `q = 2 ^ D`;
* `dc : ZMod q → ZMod (2 ^ B)`, `c ↦ ⌊c * 2 ^ B / q⌉ mod 2 ^ B`;

they are applied to every entry of a matrix by

* `EncodeChunks : ChunkMatrix p → FrodoMatrix p mbar nbar`, applying `ec` to
  every entry. The message is already cut into `mbar * nbar` chunks that belong
  to `ZMod (2 ^ B)`, which is what a `ChunkMatrix p` holds. Each chunk becomes
  one entry of the matrix;
* `DecodeChunks : FrodoMatrix p mbar nbar → ChunkMatrix p`, applying `dc` to
  every entry;

the message is cut into those chunks by

* `chunkToBits : ZMod (2 ^ B) → Vector Bool B`, the `B` binary digits of one
  chunk, least significant first;
* `bitsToChunk : Vector Bool B → ZMod (2 ^ B)`, reading those digits back;
* `bitsToChunkMatrix : Vector Bool (mbar * nbar * B) → ChunkMatrix p`, cutting
  the message every `B` bits and applying `bitsToChunk` to each piece, giving
  the `mbar * nbar` chunks. Section 6.3 sends bit `(i * nbar + j) * B + t` of the
  message to bit `t` of the entry in row `i` and column `j`, for
  `0 ≤ i < mbar`, `0 ≤ j < nbar` and `0 ≤ t < B`, so the matrix fills row by
  row from row `0`, each row left to right;
* `chunkMatrixToBits : ChunkMatrix p → Vector Bool (mbar * nbar * B)`, applying
  `chunkToBits` to every entry and concatenating the results in that same
  order.

`bitsToChunkMatrix` is `bitsToMatrixWith` of `Bits.lean` and
`chunkMatrixToBits` is `matrixToBitsWith`, at `B` bits per entry, which
`Packing.lean` uses at `D` bits instead.

The specification's `Frodo.Encode` and `Frodo.Decode` are

* `Encode : Vector Bool (mbar * nbar * B) → FrodoMatrix p mbar nbar`, cutting
  the bit vector into chunks with `bitsToChunkMatrix` and then applying `EncodeChunks`.
  The bit vector is the message, `ell_eq` fixing `mbar * nbar * B` to be its
  length `ℓ`;
* `Decode : FrodoMatrix p mbar nbar → Vector Bool (mbar * nbar * B)`, applying
  `DecodeChunks` and then laying the chunks back out with `chunkMatrixToBits`.

## Main results

* `getElem_chunkMatrixToBits`: bit `t` of entry `(i, j)` sits at position
  `(i * nbar + j) * B + t`, as a theorem. The bit order and layout it fixes are
  pinned by the `example`s beside the definitions.
-/

namespace FrodoKEM

open LatticeCrypto

/-- `Frodo.Encode`'s scalar map (Appendix B): `k ↦ k * 2 ^ (D - B)`, multiplying
by the spacing `q / 2 ^ B`. -/
def ec (p : Params) (k : ZMod (2 ^ p.B)) : ZMod p.q :=
  (k.val * 2 ^ (p.D - p.B) : ℕ)

/-- `Frodo.Decode`'s scalar map (Appendix B): `c ↦ ⌊c * 2 ^ B / q⌉ mod 2 ^ B`,
dividing by that spacing and rounding to the nearest integer. -/
def dc (p : Params) (c : ZMod p.q) : ZMod (2 ^ p.B) :=
  ((c.val * 2 ^ p.B + p.q / 2) / p.q % 2 ^ p.B : ℕ)

/-! ## The matrix maps

`Frodo.Encode` and `Frodo.Decode` apply the scalar maps entrywise to an
`mbar`-by-`nbar` matrix. The maps here are that entrywise step alone, on input
already chunked; composing them with the bit-string layer gives the published
functions. -/

/-- A matrix of `B`-bit chunks, one per entry: the chunked form of a message of
`ℓ = B * mbar * nbar` bits. -/
abbrev ChunkMatrix (p : Params) := Matrix (Fin mbar) (Fin nbar) (ZMod (2 ^ p.B))

/-- The entrywise step of `Frodo.Encode` (Appendix B), on input already chunked
into `B`-bit values: apply `ec` to every entry. -/
def EncodeChunks (p : Params) (M : ChunkMatrix p) : FrodoMatrix p mbar nbar :=
  M.map (ec p)

/-- The entrywise step of `Frodo.Decode` (Appendix B), returning the chunked
form: apply `dc` to every entry. -/
def DecodeChunks (p : Params) (C : FrodoMatrix p mbar nbar) : ChunkMatrix p :=
  C.map (dc p)

/-! ## Chunking

Section 6.3 of `[LBES26]`: the input is cut every `B` bits, and each piece,
read from its least significant bit, becomes one matrix entry; entries are
filled row by row from row `0`, each row left to right, so bits `0` to `B - 1`
of the input fill entry `(0, 0)`.

The bit strings here have length `mbar * nbar * B`, `B` bits per entry, which
`Params.WellFormed.ell_eq` identifies with the message length `ℓ`. -/

/-- The `B` bits of one chunk, least significant first. -/
def chunkToBits (p : Params) (k : ZMod (2 ^ p.B)) : Vector Bool p.B :=
  Vector.ofFn fun t => k.val.testBit t

/-- The chunk with the given `B` bits, least significant first. `Nat.ofBits`
is that reading, and `[LBES26]` uses the same convention. -/
def bitsToChunk (p : Params) (v : Vector Bool p.B) : ZMod (2 ^ p.B) :=
  ((Nat.ofBits fun t => v[t] : ℕ) : ZMod (2 ^ p.B))

/-- The chunk convention on a fixed value: with `B = 2`, the chunk `1` reads as
the bits `[1, 0]`, least significant first. -/
example : (chunkToBits ParameterSet.FrodoKEM640.params 1).toList = [true, false] := by
  decide

/-- Cut a bit string into the `mbar * nbar` values of `B` bits that
`EncodeChunks` consumes, entry `(i, j)` taking the piece at position
`i * nbar + j`. -/
def bitsToChunkMatrix (p : Params) (b : Vector Bool (mbar * nbar * p.B)) : ChunkMatrix p :=
  bitsToMatrixWith (bitsToChunk p) mbar nbar b

/-- The inverse of `bitsToChunkMatrix`: the bits of each entry, row by row from
row `0`, each row left to right. -/
def chunkMatrixToBits (p : Params) (M : ChunkMatrix p) : Vector Bool (mbar * nbar * p.B) :=
  matrixToBitsWith (chunkToBits p) M

/-- The chunking convention on a fixed matrix: with `B = 2`, the bit string
that has only bits `0` and `3` set puts `1` in entry `(0, 0)` and `2` in entry
`(0, 1)`. This fixes both orders that the round trips leave open, the bits
within a chunk and the entries along a row; `bitsToChunkMatrix` is used rather
than `chunkMatrixToBits` because the latter does not reduce: the
`Vector.flatten` inside `matrixToBitsWith` blocks it. -/
example : bitsToChunkMatrix ParameterSet.FrodoKEM640.params
    (Vector.ofFn fun i : Fin (mbar * nbar * 2) => decide (i.val = 0 ∨ i.val = 3))
      ⟨0, by decide⟩ ⟨1, by decide⟩ = 2 := by decide

/-- The row order, which the example above leaves open: bit `16` is the first
bit of entry `(1, 0)`, so it puts `1` in the second row and not in the last. -/
example : bitsToChunkMatrix ParameterSet.FrodoKEM640.params
    (Vector.ofFn fun i : Fin (mbar * nbar * 2) => decide (i.val = 16))
      ⟨1, by decide⟩ ⟨0, by decide⟩ = 1 := by decide

/-- Bit `t` of entry `(i, j)` sits at position `(i * nbar + j) * B + t`, the
layout of Section 6.3 of `[LBES26]`. -/
theorem getElem_chunkMatrixToBits (p : Params) (M : ChunkMatrix p) {i j t : ℕ}
    (hi : i < mbar) (hj : j < nbar) (ht : t < p.B) :
    (chunkMatrixToBits p M)[(i * nbar + j) * p.B + t]'(bitIndex_lt hi hj ht) =
      (chunkToBits p (M ⟨i, hi⟩ ⟨j, hj⟩))[t] :=
  getElem_matrixToBitsWith (chunkToBits p) M hi hj ht

/-! ## The published maps -/

/-- `Frodo.Encode` (Appendix B of `[CiC25]`, Section 6.3 of `[LBES26]`): cut
the bit string into `B`-bit chunks, then apply `ec` entrywise. -/
def Encode (p : Params) (b : Vector Bool (mbar * nbar * p.B)) :
    FrodoMatrix p mbar nbar :=
  EncodeChunks p (bitsToChunkMatrix p b)

/-- `Frodo.Decode` (Appendix B of `[CiC25]`, Section 6.3 of `[LBES26]`): apply
`dc` entrywise, then concatenate the chunks. -/
def Decode (p : Params) (C : FrodoMatrix p mbar nbar) :
    Vector Bool (mbar * nbar * p.B) :=
  chunkMatrixToBits p (DecodeChunks p C)

end FrodoKEM
