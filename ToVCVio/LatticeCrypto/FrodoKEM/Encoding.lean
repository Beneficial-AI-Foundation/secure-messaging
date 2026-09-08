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

`Frodo.Encode` and `Frodo.Decode`, with the proof that decoding inverts
encoding, exactly and in the presence of noise.

References are as in `Parameters.lean`. `[CiC25]` gives the maps on bit strings
in Appendix B, named in Section 3.3, and their noise tolerance in Lemma 1 of
Section 4.1. `[LBES26]` gives the same maps as pseudocode in Section 6.3, with
the chunking layout written out, and states no correctness result, so Lemma 1
is cited from `[CiC25]` alone.

## Main definitions

Encoding places `B` bits in each entry of an `mbar`-by-`nbar` matrix over
`ZMod q`. Names follow the specification, `ec` and `dc` included. With
`p : Params` left implicit and the least significant bit read first throughout,
the scalar maps are

* `ec : ZMod (2 ^ B) → ZMod q`, `k ↦ k * q / 2 ^ B` — written `k * 2 ^ (D - B)`,
  which agrees under `q = 2 ^ D`;
* `dc : ZMod q → ZMod (2 ^ B)`, `c ↦ ⌊c * 2 ^ B / q⌉ mod 2 ^ B`;

they are applied to every entry of a matrix by

* `EncodeChunks : ChunkMatrix p → FrodoMatrix p mbar nbar`, applying `ec` to
  every entry. The message is already cut into `mbar * nbar` chunks that belong
  to `ZMod (2 ^ B)`, which is what a `ChunkMatrix p` holds. Each chunk becomes
  one entry of the matrix;
* `DecodeChunks : FrodoMatrix p mbar nbar → ChunkMatrix p`, applying `dc` to
  every entry. If an entry stays within the noise window below, then the initial
  chunk is recovered;

the message is cut into those chunks by

* `chunkToBits : ZMod (2 ^ B) → Vector Bool B`, the `B` binary digits of one
  chunk, least significant first;
* `bitsToChunk : Vector Bool B → ZMod (2 ^ B)`, reading those digits back;
* `toChunks : Vector Bool (mbar * nbar * B) → ChunkMatrix p`, cutting the
  message every `B` bits and applying `bitsToChunk` to each piece, giving the
  `mbar * nbar` chunks. Section 6.3 sends bit `(i * nbar + j) * B + t` of the
  message to bit `t` of the entry in row `i` and column `j`, for
  `0 ≤ i < mbar`, `0 ≤ j < nbar` and `0 ≤ t < B`, so the matrix fills row by
  row from row `0`, each row left to right;
* `ofChunks : ChunkMatrix p → Vector Bool (mbar * nbar * B)`, applying
  `chunkToBits` to every entry and concatenating the results in that same
  order.

These two are `bitsToMatrixWith` and `matrixToBitsWith` of `Bits.lean` at `B`
bits per entry, which `Packing.lean` uses at `D` bits instead.

The two composites, which are `Frodo.Encode` and `Frodo.Decode` of the
specification and so take those names, are

* `Encode : Vector Bool (mbar * nbar * B) → FrodoMatrix p mbar nbar`, cutting
  the bit vector into chunks with `toChunks` and then applying `EncodeChunks`.
  The bit vector is the message, `ell_eq` fixing `mbar * nbar * B` to be its
  length `ℓ`;
* `Decode : FrodoMatrix p mbar nbar → Vector Bool (mbar * nbar * B)`, applying
  `DecodeChunks` and then laying the chunks back out with `ofChunks`. If every
  entry stays within the noise window, then the initial message is recovered.

Three of the `Params.WellFormed` conditions are used:

* `q = 2 ^ D` (`q_eq`) makes `q / 2 ^ B` exact, so both maps are bit shifts;
* `B ≤ D` (`B_le_D`) gives `2 ^ B ≤ q`, so `ec` does not wrap (`ec_val`);
* `ℓ = B * mbar * nbar` (`ell_eq`) makes a message fill the matrix exactly.

The encoded values then sit at spacing `q / 2 ^ B = 2 ^ (D - B)`. If the added
noise is less than half of it, then `dc` recovers `k`; `dc_ec_add` states the
window exactly, and `Params.noiseRadius` is that half-step rounded down.

## Main results

* `dc_ec`, `DecodeChunks_EncodeChunks` and `Decode_Encode`: decoding inverts
  encoding;
* `dc_ec_add`, `DecodeChunks_EncodeChunks_add` and `Decode_Encode_add`: decoding
  inverts encoding perturbed by noise `e` with
  `-q ≤ 2 ^ (B + 1) * centeredRepr e < q`, which is Lemma 1 of Section 4.1
  cleared of its denominator;
* `ofChunks_toChunks` and `toChunks_ofChunks`: the chunking is a round trip;
* `getElem_ofChunks`: the position formula this header states in prose, as a
  theorem. The bit order and layout it fixes are pinned by the `example`s beside
  the definitions, which no round trip can determine.
-/

namespace FrodoKEM

open LatticeCrypto

namespace Params

/-- The half-step `q / 2 ^ (B + 1)`: half the spacing of the representable
values `ec k`, and the bound on the noise `dc` tolerates. The division is exact
only when `B < D`; at `B = D` it truncates to zero, and `dc_ec_add` takes that
case separately. -/
def noiseRadius (p : Params) : ℕ := p.q / 2 ^ (p.B + 1)

end Params

/-- `Frodo.Encode`'s scalar map (Appendix B): `k ↦ k * 2 ^ (D - B)`, multiplying
by the spacing `q / 2 ^ B`. -/
def ec (p : Params) (k : ZMod (2 ^ p.B)) : ZMod p.q :=
  (k.val * 2 ^ (p.D - p.B) : ℕ)

/-- `Frodo.Decode`'s scalar map (Appendix B): `c ↦ ⌊c * 2 ^ B / q⌉ mod 2 ^ B`,
dividing by that spacing and rounding to the nearest integer. -/
def dc (p : Params) (c : ZMod p.q) : ZMod (2 ^ p.B) :=
  ((c.val * 2 ^ p.B + p.q / 2) / p.q % 2 ^ p.B : ℕ)

/-- `ec` does not wrap: its value is the unreduced product `k * 2 ^ (D - B)`. -/
theorem ec_val (p : Params) (hw : p.WellFormed) (k : ZMod (2 ^ p.B)) :
    (ec p k).val = k.val * 2 ^ (p.D - p.B) := by
  apply ZMod.val_cast_of_lt
  rw [hw.q_eq, ← pow_mul_pow_sub (2:ℕ) hw.B_le_D]
  gcongr
  exact ZMod.val_lt k

/-- Decoding inverts encoding (Appendix B). -/
theorem dc_ec (p : Params) (hw : p.WellFormed) (k : ZMod (2 ^ p.B)) :
    dc p (ec p k) = k := by
  rw [dc, ec_val p hw k, hw.q_eq, mul_assoc, ← Nat.pow_add,
      Nat.sub_add_cancel hw.B_le_D, Nat.mul_comm,
      Nat.mul_add_div (Nat.two_pow_pos p.D),
      Nat.div_eq_of_lt (Nat.div_lt_self (Nat.two_pow_pos p.D) one_lt_two),
      Nat.add_zero, ZMod.natCast_mod]
  exact ZMod.natCast_zmod_val k

/-- A natural-number quotient identity for residues in `[0, r) ∪ [q - r, q)`.

If `s * n = q` and `2 * (r * n) = q`, then for `v < n` and `ev < q` in the
interval union above,

`((v * s + ev) % q * n + q / 2) / q % n = v`.

`dc_ec_add` supplies `q = 2 ^ D`, `n = 2 ^ B`, `s = 2 ^ (D - B)` and
`r = noiseRadius`. -/
private theorem dc_quotient {q n s v ev : ℕ} (r : ℕ)
    (hsn : s * n = q) (hrn : 2 * (r * n) = q)
    (hv : v < n) (hev : ev < q) (hwin : ev < r ∨ q - r ≤ ev) :
    ((v * s + ev) % q * n + q / 2) / q % n = v := by
  have hn : 0 < n := by omega
  have hr : 0 < r := by rcases Nat.eq_zero_or_pos r with rfl | h <;> omega
  have hs : s = 2 * r := Nat.eq_of_mul_eq_mul_right hn (by rw [Nat.mul_assoc]; omega)
  subst hs
  -- cancel the factor `n` from the quotient, leaving a division by the step `2 * r`
  rw [show q / 2 = r * n by omega, ← hsn, ← Nat.add_mul, Nat.mul_div_mul_right _ _ hn]
  -- the wrap past the modulus contributes a multiple of `n`
  have hshift : ∀ x : ℕ, (x % (2 * r * n) + r) / (2 * r) % n = (x + r) / (2 * r) % n := by
    intro x
    conv_rhs => rw [← Nat.div_add_mod x (2 * r * n), Nat.mul_assoc, Nat.add_assoc,
      Nat.mul_add_div (by omega : 0 < 2 * r), Nat.mul_add_mod]
  rw [hshift]
  rcases hwin with h | h
  -- noise below the half-step: the rounding term is `0`
  · rw [Nat.mul_comm v (2 * r), Nat.add_assoc, Nat.mul_add_div (by omega : 0 < 2 * r),
      Nat.div_eq_of_lt (by omega), Nat.add_zero, Nat.mod_eq_of_lt hv]
  -- noise within the half-step of `q`: the quotient is `v + n`, and `% n` drops the `n`
  · rw [show v * (2 * r) + ev + r = 2 * r * (v + n) + (ev + r - 2 * r * n) by
        have : 2 * r * (v + n) = v * (2 * r) + 2 * r * n := by ring
        omega,
      Nat.mul_add_div (by omega : 0 < 2 * r), Nat.div_eq_of_lt (by omega), Nat.add_zero,
      Nat.add_mod_right, Nat.mod_eq_of_lt hv]

/-- Decoding recovers `k` after perturbing its encoding by a signed additive
error `e` with `-q ≤ 2 ^ (B + 1) * centeredRepr e < q`. This is Lemma 1 of
Section 4.1, whose window `centeredRepr e ∈ [-q / 2 ^ (B + 1), q / 2 ^ (B + 1))`
is closed below and open above, and whose division is a rational one.

It is stated here cleared of that denominator because `q : ℕ`, so the division
would be natural. At `B = D` the rational window is `-1/2 ≤ e < 1/2`, admitting
`e = 0` alone, where `q / 2 ^ (B + 1)` in `ℕ` truncates to zero and gives the
empty `0 ≤ e < 0`, excluding the one error the lemma allows. -/
theorem dc_ec_add (p : Params) (hw : p.WellFormed) (k : ZMod (2 ^ p.B))
    (e : ZMod p.q)
    (hlo : -(p.q : ℤ) ≤ 2 ^ (p.B + 1) * centeredRepr e)
    (hhi : 2 ^ (p.B + 1) * centeredRepr e < (p.q : ℤ)) :
    dc p (ec p k + e) = k := by
  have hQ : p.q = 2 ^ p.D := hw.q_eq
  haveI : NeZero p.q := ⟨by rw [hQ]; positivity⟩
  have hq0 : (0 : ℤ) < (p.q : ℤ) := by rw [hQ]; positivity
  have hpow : (0 : ℤ) < 2 ^ (p.B + 1) := by positivity
  -- with every bit of an entry carrying message the window admits only `e = 0`
  rcases eq_or_lt_of_le hw.B_le_D with hBD | hBD
  · rw [show (2 : ℤ) ^ (p.B + 1) = 2 * (p.q : ℤ) by
        rw [hBD, pow_succ, hQ]; push_cast; ring] at hlo hhi
    have hz : centeredRepr e = 0 := by
      rcases lt_trichotomy (centeredRepr e) 0 with h | h | h
      · nlinarith
      · exact h
      · nlinarith
    have he : e = 0 := by rw [centeredRepr_intCast e, hz]; simp
    rw [he, add_zero, dc_ec p hw k]
  have hsn : 2 ^ (p.D - p.B) * 2 ^ p.B = p.q := by rw [hQ, ← pow_add]; congr 1; omega
  have hrn : 2 * (p.noiseRadius * 2 ^ p.B) = p.q := by
    rw [Params.noiseRadius, hQ, Nat.pow_div (by omega) two_pos, ← pow_add, ← pow_succ']
    congr 1; omega
  -- `q = 2 ^ (B + 1) * noiseRadius`, so cancelling the factor gives the half-step
  -- window on `e.val` that `dc_quotient` consumes
  have hwin : e.val < p.noiseRadius ∨ p.q - p.noiseRadius ≤ e.val := by
    rw [show (p.q : ℤ) = 2 ^ (p.B + 1) * p.noiseRadius by rw [← hrn]; push_cast; ring]
      at hlo hhi
    rcases le_or_gt ((e.val : ℤ)) ((p.q : ℤ) / 2) with h | h
    · rw [centeredRepr_of_le h] at hhi
      exact Or.inl (by exact_mod_cast lt_of_mul_lt_mul_left hhi hpow.le)
    · rw [centeredRepr_of_gt h] at hlo
      refine Or.inr ?_
      have := le_of_mul_le_mul_left (a := (2 : ℤ) ^ (p.B + 1))
        (by linarith : (2 : ℤ) ^ (p.B + 1) * (-(p.noiseRadius : ℤ))
              ≤ 2 ^ (p.B + 1) * ((e.val : ℤ) - (p.q : ℤ))) hpow
      omega
  rw [dc, ZMod.val_add, ec_val p hw k,
    dc_quotient p.noiseRadius hsn hrn (ZMod.val_lt k) (ZMod.val_lt e) hwin]
  exact ZMod.natCast_zmod_val k

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

/-- `DecodeChunks` inverts `EncodeChunks`. -/
theorem DecodeChunks_EncodeChunks (p : Params) (hw : p.WellFormed)
    (M : ChunkMatrix p) :
    DecodeChunks p (EncodeChunks p M) = M := by
  ext i j
  simp [DecodeChunks, EncodeChunks, dc_ec p hw]

/-- `DecodeChunks` recovers the chunks from an encoding perturbed by an error
matrix whose entries all lie in the window of `dc_ec_add`, stated entrywise. -/
theorem DecodeChunks_EncodeChunks_add (p : Params) (hw : p.WellFormed)
    (M : ChunkMatrix p)
    (E : FrodoMatrix p mbar nbar)
    (hlo : ∀ i j, -(p.q : ℤ) ≤ 2 ^ (p.B + 1) * centeredRepr (E i j))
    (hhi : ∀ i j, 2 ^ (p.B + 1) * centeredRepr (E i j) < (p.q : ℤ)) :
    DecodeChunks p (EncodeChunks p M + E) = M := by
  ext i j
  simpa [DecodeChunks, EncodeChunks] using
    dc_ec_add p hw (M i j) (E i j) (hlo i j) (hhi i j)

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

/-- A chunk is recovered from its bits. -/
@[simp]
theorem bitsToChunk_chunkToBits (p : Params) (k : ZMod (2 ^ p.B)) :
    bitsToChunk p (chunkToBits p k) = k := by
  simp only [bitsToChunk, chunkToBits, Fin.getElem_fin, Vector.getElem_ofFn,
    Nat.ofBits_testBit, ZMod.natCast_mod, ZMod.natCast_zmod_val]

/-- The bits of a chunk are recovered from it. -/
@[simp]
theorem chunkToBits_bitsToChunk (p : Params) (v : Vector Bool p.B) :
    chunkToBits p (bitsToChunk p v) = v := by
  apply Vector.ext
  intro t ht
  rw [chunkToBits, Vector.getElem_ofFn, bitsToChunk, ZMod.val_natCast,
    Nat.mod_eq_of_lt (Nat.ofBits_lt_two_pow _), Nat.testBit_ofBits]
  simp [ht]

/-- Cut a bit string into the `mbar * nbar` values of `B` bits that
`EncodeChunks` consumes, entry `(i, j)` taking the piece at position
`i * nbar + j`. -/
def toChunks (p : Params) (b : Vector Bool (mbar * nbar * p.B)) : ChunkMatrix p :=
  bitsToMatrixWith (bitsToChunk p) mbar nbar b

/-- The inverse of `toChunks`: the bits of each entry, row by row from row `0`,
each row left to right. -/
def ofChunks (p : Params) (M : ChunkMatrix p) : Vector Bool (mbar * nbar * p.B) :=
  matrixToBitsWith (chunkToBits p) M

/-- The chunking convention on a fixed matrix: with `B = 2`, the bit string
that has only bits `0` and `3` set puts `1` in entry `(0, 0)` and `2` in entry
`(0, 1)`. This fixes both orders that the round trips leave open, the bits
within a chunk and the entries along a row; `toChunks` is used rather than
`ofChunks` because `Vector.flatten` does not reduce. -/
example : toChunks ParameterSet.FrodoKEM640.params
    (Vector.ofFn fun i : Fin (mbar * nbar * 2) => decide (i.val = 0 ∨ i.val = 3))
      ⟨0, by decide⟩ ⟨1, by decide⟩ = 2 := by decide

/-- The row order, which the example above leaves open: bit `16` is the first
bit of entry `(1, 0)`, so it puts `1` in the second row and not in the last. -/
example : toChunks ParameterSet.FrodoKEM640.params
    (Vector.ofFn fun i : Fin (mbar * nbar * 2) => decide (i.val = 16))
      ⟨1, by decide⟩ ⟨0, by decide⟩ = 1 := by decide

/-- Bit `t` of entry `(i, j)` sits at position `(i * nbar + j) * B + t`, the
layout of Section 6.3. -/
theorem getElem_ofChunks (p : Params) (M : ChunkMatrix p) {i j t : ℕ}
    (hi : i < mbar) (hj : j < nbar) (ht : t < p.B) :
    (ofChunks p M)[(i * nbar + j) * p.B + t]'(bitIndex_lt hi hj ht) =
      (chunkToBits p (M ⟨i, hi⟩ ⟨j, hj⟩))[t] :=
  getElem_matrixToBitsWith (chunkToBits p) M hi hj ht

/-- The chunks are recovered from their bit string. -/
@[simp]
theorem toChunks_ofChunks (p : Params) (M : ChunkMatrix p) :
    toChunks p (ofChunks p M) = M :=
  bitsToMatrixWith_matrixToBitsWith (bitsToChunk_chunkToBits p) M

/-- A bit string is recovered from its chunks. -/
@[simp]
theorem ofChunks_toChunks (p : Params) (b : Vector Bool (mbar * nbar * p.B)) :
    ofChunks p (toChunks p b) = b :=
  matrixToBitsWith_bitsToMatrixWith (chunkToBits_bitsToChunk p) mbar nbar b

/-! ## The published maps -/

/-- `Frodo.Encode` (Appendix B of `[CiC25]`, Section 6.3 of `[LBES26]`): cut
the bit string into `B`-bit chunks, then apply `ec` entrywise. -/
def Encode (p : Params) (b : Vector Bool (mbar * nbar * p.B)) :
    FrodoMatrix p mbar nbar :=
  EncodeChunks p (toChunks p b)

/-- `Frodo.Decode` (Appendix B of `[CiC25]`, Section 6.3 of `[LBES26]`): apply
`dc` entrywise, then concatenate the chunks. -/
def Decode (p : Params) (C : FrodoMatrix p mbar nbar) :
    Vector Bool (mbar * nbar * p.B) :=
  ofChunks p (DecodeChunks p C)

/-- `Frodo.Decode` inverts `Frodo.Encode`. -/
theorem Decode_Encode (p : Params) (hw : p.WellFormed)
    (b : Vector Bool (mbar * nbar * p.B)) : Decode p (Encode p b) = b := by
  rw [Decode, Encode, DecodeChunks_EncodeChunks p hw, ofChunks_toChunks]

/-- `Frodo.Decode` recovers the bit string from an encoding perturbed by an
error matrix whose entries all lie in the window of `dc_ec_add`. -/
theorem Decode_Encode_add (p : Params) (hw : p.WellFormed)
    (b : Vector Bool (mbar * nbar * p.B)) (E : FrodoMatrix p mbar nbar)
    (hlo : ∀ i j, -(p.q : ℤ) ≤ 2 ^ (p.B + 1) * centeredRepr (E i j))
    (hhi : ∀ i j, 2 ^ (p.B + 1) * centeredRepr (E i j) < (p.q : ℤ)) :
    Decode p (Encode p b + E) = b := by
  rw [Decode, Encode, DecodeChunks_EncodeChunks_add p hw _ E hlo hhi, ofChunks_toChunks]

end FrodoKEM
