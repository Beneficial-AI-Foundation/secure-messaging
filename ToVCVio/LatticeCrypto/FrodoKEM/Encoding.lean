/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import ToVCVio.LatticeCrypto.FrodoKEM.Parameters
import LatticeCrypto.Ring.Norms

/-!
# FrodoKEM message encoding

This file specifies `Frodo.Encode` and `Frodo.Decode`, and proves that decoding
inverts encoding, exactly and in the presence of noise.

FrodoKEM has been published in several revisions. Two of the 2025 ones are
referred to here, because neither covers everything this file needs:

* `[CiC25]`, Glabush, Longa, Naehrig, Peikert, Stebila and Virdia, *FrodoKEM: A
  CCA-Secure Learning With Errors Key Encapsulation Mechanism*, IACR
  Communications in Cryptology 2:3, <https://cic.iacr.org/p/2/3/25>. It
  specifies the maps on bit strings but fixes no octet convention.
* `[ABD+25]`, Alkim, Bos, Ducas, Longa, Mironov, Naehrig, Nikolaenko, Peikert,
  Raghunathan and Stebila, *FrodoKEM Preliminary Standardization Proposal
  (submitted to ISO)*, September 2025,
  <https://frodokem.org/files/FrodoKEM_standard_proposal_20250929.pdf>. It fixes
  the octet conventions, which `[CiC25]` leaves open. Both describe the same
  version of the scheme.

`Frodo.Encode` and `Frodo.Decode` are Appendix B of `[CiC25]`, named in its
Section 3.3, and Section 7.3 of `[ABD+25]`. The octet encoding of bit strings is
Section 7.1 of `[ABD+25]`; note that `Frodo.Pack` uses a different one, so it is
specified separately in `Packing.lean`.

Encoding places `B` bits in each entry of an `mbar`-by-`nbar` matrix over
`ZMod q`. With `p : Params` left implicit, the maps are

* `ec : ZMod (2 ^ B) → ZMod q`, `k ↦ k * q / 2 ^ B`;
* `dc : ZMod q → ZMod (2 ^ B)`, `c ↦ ⌊c * 2 ^ B / q⌉ mod 2 ^ B`;
* `EncodeChunks : ChunkMatrix p → FrodoMatrix p mbar nbar`, `ec` entrywise;
* `DecodeChunks : FrodoMatrix p mbar nbar → ChunkMatrix p`, `dc` entrywise.

Two conditions of `Params.WellFormed` are used throughout:

* `q = 2 ^ D` (`q_eq`) makes `q / 2 ^ B` exact, so both maps are bit shifts;
* `B ≤ D` (`B_le_D`) gives `2 ^ B ≤ q`, so `ec` does not wrap (`ec_val`).

Two further relations follow, each proved where it is used:

* the encoded values sit at spacing `q / 2 ^ B = 2 ^ (D - B)`;
* the half-step is `Params.noiseRadius = q / 2 ^ (B + 1)`, which satisfies
  `q = 2 ^ (B + 1) * noiseRadius` exactly when `B < D`. At `B = D` the true
  half-step is one half and `noiseRadius` truncates it to zero, so `dc_ec_add`
  treats that case separately.

The remaining conditions of `WellFormed`, `D ≤ 16` and `n % 8 = 0`, play no part
here: `n` is the lattice dimension and does not enter encoding.

The maps take a message already chunked into `mbar * nbar` values of
`ZMod (2 ^ B)`, one per matrix entry, rather than as a bit string of length
`ℓ = B * mbar * nbar` (`ParameterSet.ell_eq_mul`); the bit-string layer is
specified alongside `Frodo.Pack` and `Frodo.Unpack`.

Names follow the specification where the maps do. The scalar maps and their
lemmas keep its abbreviated lowercase names, `ec` and `dc`. The matrix maps are
only the chunked half of `Frodo.Encode` and `Frodo.Decode`, so they are named
`EncodeChunks` and `DecodeChunks`; the names of the published functions are left
for the composites that include the bit-string layer.

## Main definitions

* `ec`, `dc`: the scalar maps;
* `EncodeChunks`, `DecodeChunks`: the matrix maps, `ec` and `dc` applied
  entrywise;
* `Params.noiseRadius`: the half-step `q / 2 ^ (B + 1)`.

## Main results

* `dc_ec` and `DecodeChunks_EncodeChunks`: decoding inverts encoding;
* `dc_ec_add` and `DecodeChunks_EncodeChunks_add`: decoding inverts encoding
  perturbed by
  noise `e` with `centeredRepr e ∈ [-q / 2 ^ (B + 1), q / 2 ^ (B + 1) - 1]`.
  This is Lemma 1, whose window is asymmetric: closed below and open above.
-/

namespace FrodoKEM

namespace Params

/-- The half-step `q / 2 ^ (B + 1)`: half the spacing of the representable
values `ec k`, and the bound on the noise `dc` tolerates. -/
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
error whose centered representative lies in
`[-q / 2 ^ (B + 1), q / 2 ^ (B + 1))`, stated without division as
`-q ≤ 2 ^ (B + 1) * centeredRepr e < q`. This is Lemma 1. At `B = D` the window
admits only `e = 0`. -/
theorem dc_ec_add (p : Params) (hw : p.WellFormed) (k : ZMod (2 ^ p.B))
    (e : ZMod p.q)
    (hlo : -(p.q : ℤ) ≤ 2 ^ (p.B + 1) * LatticeCrypto.centeredRepr e)
    (hhi : 2 ^ (p.B + 1) * LatticeCrypto.centeredRepr e < (p.q : ℤ)) :
    dc p (ec p k + e) = k := by
  have hQ : p.q = 2 ^ p.D := hw.q_eq
  haveI : NeZero p.q := ⟨by rw [hQ]; positivity⟩
  have hq0 : (0 : ℤ) < (p.q : ℤ) := by rw [hQ]; positivity
  have hpow : (0 : ℤ) < 2 ^ (p.B + 1) := by positivity
  -- with every bit of an entry carrying message the window admits only `e = 0`
  rcases eq_or_lt_of_le hw.B_le_D with hBD | hBD
  · rw [show (2 : ℤ) ^ (p.B + 1) = 2 * (p.q : ℤ) by
        rw [hBD, pow_succ, hQ]; push_cast; ring] at hlo hhi
    have hz : LatticeCrypto.centeredRepr e = 0 := by
      rcases lt_trichotomy (LatticeCrypto.centeredRepr e) 0 with h | h | h
      · nlinarith
      · exact h
      · nlinarith
    have he : e = 0 := by rw [LatticeCrypto.centeredRepr_intCast e, hz]; simp
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
    unfold LatticeCrypto.centeredRepr at hlo hhi
    split at hlo <;> rename_i h
    · rw [if_pos h] at hhi
      exact Or.inl (by exact_mod_cast lt_of_mul_lt_mul_left hhi hpow.le)
    · refine Or.inr ?_
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
matrix whose entries all lie in the window, stated entrywise. -/
theorem DecodeChunks_EncodeChunks_add (p : Params) (hw : p.WellFormed)
    (M : ChunkMatrix p)
    (E : FrodoMatrix p mbar nbar)
    (hlo : ∀ i j, -(p.q : ℤ) ≤ 2 ^ (p.B + 1) * LatticeCrypto.centeredRepr (E i j))
    (hhi : ∀ i j, 2 ^ (p.B + 1) * LatticeCrypto.centeredRepr (E i j) < (p.q : ℤ)) :
    DecodeChunks p (EncodeChunks p M + E) = M := by
  ext i j
  simpa [DecodeChunks, EncodeChunks] using
    dc_ec_add p hw (M i j) (E i j) (hlo i j) (hhi i j)

/-! ## Bit strings and octets

`Frodo.Encode` consumes a bit string of length `ℓ = B * mbar * nbar`; messages
are byte vectors. Section 7.1 of `[ABD+25]` fixes the conversion: bits are taken
left to right and packed from the least significant bit of each octet upwards.

`Frodo.Pack` uses the opposite order within each octet, so that conversion is
specified separately in `Packing.lean` rather than shared with this one. -/

/-- The eight bits of one octet, least significant first. -/
def byteToBits (x : Byte) : Vector Bool 8 :=
  Vector.ofFn fun j => x.toNat.testBit j

/-- The octet with the given eight bits, least significant first. -/
def bitsToByte (v : Vector Bool 8) : Byte :=
  UInt8.ofNat (∑ j : Fin 8, if v[j] then 2 ^ j.val else 0)

/-- The convention of Section 7.1 on the two domain separators of the
specification, `0x96 = 0b10010110` and `0x5F = 0b01011111`. This fixes the bit
order, which the round-trip theorems below cannot: reading and writing in the
same wrong order round-trips just as well. -/
example : (byteToBits 0x96).toList ++ (byteToBits 0x5F).toList =
    [false, true, true, false, true, false, false, true,
     true, true, true, true, true, false, true, false] := by decide

/-- An octet is recovered from its bits. -/
theorem bitsToByte_byteToBits (x : Byte) : bitsToByte (byteToBits x) = x := by
  simpa using (by decide : ∀ m < 256,
    bitsToByte (byteToBits (UInt8.ofNat m)) = UInt8.ofNat m) x.toNat x.toNat_lt

/-- Section 7.1 of `[ABD+25]`: read a byte vector as a bit string, least
significant bit of each octet first. -/
def bytesToBits {n : ℕ} (bs : Bytes n) : Vector Bool (n * 8) :=
  (bs.map byteToBits).flatten

/-- The inverse of `bytesToBits`. -/
def bitsToBytes {n : ℕ} (b : Vector Bool (n * 8)) : Bytes n :=
  Vector.ofFn fun i =>
    bitsToByte (Vector.ofFn fun j => b[i.val * 8 + j.val]'(by omega))

/-- The bits of octet `i` sit at positions `i * 8` to `i * 8 + 7`. -/
theorem getElem_bytesToBits {n : ℕ} (bs : Bytes n) {i j : ℕ} (hi : i < n) (hj : j < 8) :
    (bytesToBits bs)[i * 8 + j]'(by omega) = (byteToBits bs[i])[j] := by
  simp [bytesToBits, Vector.getElem_flatten, Nat.mod_eq_of_lt hj,
    show (i * 8 + j) / 8 = i by omega]

/-- A byte vector is recovered from its bit string. -/
theorem bitsToBytes_bytesToBits {n : ℕ} (bs : Bytes n) :
    bitsToBytes (bytesToBits bs) = bs := by
  apply Vector.ext
  intro i hi
  rw [bitsToBytes, Vector.getElem_ofFn, ← bitsToByte_byteToBits bs[i]]
  congr 1
  apply Vector.ext
  intro j hj
  simpa using getElem_bytesToBits bs hi hj

/-- The bits of an octet are recovered from it. -/
theorem byteToBits_bitsToByte (v : Vector Bool 8) : byteToBits (bitsToByte v) = v := by
  simpa using (by decide : ∀ f : Fin 8 → Bool,
    byteToBits (bitsToByte (Vector.ofFn f)) = Vector.ofFn f) fun j => v[j]

/-- A bit string is recovered from its byte vector. -/
theorem bytesToBits_bitsToBytes {n : ℕ} (b : Vector Bool (n * 8)) :
    bytesToBits (bitsToBytes b) = b := by
  apply Vector.ext
  intro k hk
  obtain ⟨i, j, hi, hj, rfl⟩ : ∃ i j, i < n ∧ j < 8 ∧ k = i * 8 + j :=
    ⟨k / 8, k % 8, by omega, by omega, by omega⟩
  rw [getElem_bytesToBits _ hi hj, bitsToBytes, Vector.getElem_ofFn, byteToBits_bitsToByte,
      Vector.getElem_ofFn]

/-! ## Chunking

Section 7.3 of `[ABD+25]`: each `B`-bit run of the input, read from its least
significant bit, becomes one matrix entry; entries are filled row by row.

The bit strings here have length `mbar * nbar * B`, one `B`-bit run per entry.
`ParameterSet.ell_eq_mul` identifies that with `ℓ` for the published parameter
sets. -/

/-- The `B` bits of one chunk, least significant first. -/
def chunkToBits (p : Params) (k : ZMod (2 ^ p.B)) : Vector Bool p.B :=
  Vector.ofFn fun t => k.val.testBit t

/-- The chunk with the given `B` bits, least significant first. `Nat.ofBits`
is that reading, and `[ABD+25]` uses the same convention. -/
def bitsToChunk (p : Params) (v : Vector Bool p.B) : ZMod (2 ^ p.B) :=
  ((Nat.ofBits fun t => v[t] : ℕ) : ZMod (2 ^ p.B))

/-- A chunk is recovered from its bits. -/
theorem bitsToChunk_chunkToBits (p : Params) (k : ZMod (2 ^ p.B)) :
    bitsToChunk p (chunkToBits p k) = k := by
  simp only [bitsToChunk, chunkToBits, Fin.getElem_fin, Vector.getElem_ofFn,
    Nat.ofBits_testBit, ZMod.natCast_mod, ZMod.natCast_zmod_val]

/-- The bits of a chunk are recovered from it. -/
theorem chunkToBits_bitsToChunk (p : Params) (v : Vector Bool p.B) :
    chunkToBits p (bitsToChunk p v) = v := by
  apply Vector.ext
  intro t ht
  rw [chunkToBits, Vector.getElem_ofFn, bitsToChunk, ZMod.val_natCast,
    Nat.mod_eq_of_lt (Nat.ofBits_lt_two_pow _), Nat.testBit_ofBits]
  simp [ht]

/-- Bit `t` of entry `(i, j)` of an `r`-by-`c` matrix sits at position
`(i * c + j) * d + t` of a bit string of length `r * c * d`, when each entry
takes `d` bits and entries are laid out row by row. Used for the chunks here and
for the packed entries of `Packing.lean`. -/
theorem bitIndex_lt {r c d i j t : ℕ} (hi : i < r) (hj : j < c) (ht : t < d) :
    (i * c + j) * d + t < r * c * d :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left ht _)
    (by rw [← Nat.succ_mul, Nat.mul_comm i c]; gcongr
        exact Nat.mul_add_lt_mul_of_lt_of_lt hi hj)

/-- Cut a bit string into the `mbar * nbar` values of `B` bits that
`EncodeChunks` consumes, entry `(i, j)` taking the run at position
`i * nbar + j`. -/
def toChunks (p : Params) (b : Vector Bool (mbar * nbar * p.B)) : ChunkMatrix p :=
  Matrix.of fun i j => bitsToChunk p (Vector.ofFn fun t =>
    b[(i.val * nbar + j.val) * p.B + t.val]'(bitIndex_lt i.isLt j.isLt t.isLt))

/-- The inverse of `toChunks`: the runs of each entry, row by row. -/
def ofChunks (p : Params) (M : ChunkMatrix p) : Vector Bool (mbar * nbar * p.B) :=
  (Vector.ofFn fun c : Fin (mbar * nbar) =>
    chunkToBits p (M c.divNat c.modNat)).flatten

theorem getElem_ofChunks (p : Params) (M : ChunkMatrix p) {i j t : ℕ}
    (hi : i < mbar) (hj : j < nbar) (ht : t < p.B) :
    (ofChunks p M)[(i * nbar + j) * p.B + t]'(bitIndex_lt hi hj ht) =
      (chunkToBits p (M ⟨i, hi⟩ ⟨j, hj⟩))[t] := by
  rw [ofChunks, Vector.getElem_flatten]
  simp only [Nat.mul_comm (i * nbar + j) p.B, Nat.mul_add_div (by omega : 0 < p.B),
    Nat.mul_add_mod, Nat.div_eq_of_lt ht, Nat.mod_eq_of_lt ht, Nat.add_zero,
    Vector.getElem_ofFn]
  congr 3 <;> simp only [Fin.divNat, Fin.modNat, Fin.mk.injEq, nbar] at hj ⊢ <;> omega

theorem toChunks_ofChunks (p : Params) (M : ChunkMatrix p) :
    toChunks p (ofChunks p M) = M := by
  ext i j
  simp only [toChunks, Matrix.of_apply]
  rw [← bitsToChunk_chunkToBits p (M i j)]
  congr 1
  apply Vector.ext
  intro t ht
  rw [Vector.getElem_ofFn]
  exact getElem_ofChunks p M i.isLt j.isLt ht

theorem ofChunks_toChunks (p : Params) (b : Vector Bool (mbar * nbar * p.B)) :
    ofChunks p (toChunks p b) = b := by
  apply Vector.ext
  intro k hk
  rcases Nat.eq_zero_or_pos p.B with hB | hB
  · simp [hB] at hk
  obtain ⟨i, j, t, hi, hj, ht, rfl⟩ :
      ∃ i j t, i < mbar ∧ j < nbar ∧ t < p.B ∧ k = (i * nbar + j) * p.B + t :=
    ⟨k / p.B / nbar, k / p.B % nbar, k % p.B,
      Nat.div_lt_of_lt_mul (Nat.div_lt_of_lt_mul (by simp only [mbar, nbar] at *; omega)),
      Nat.mod_lt _ (by simp [nbar]), Nat.mod_lt _ hB,
      by rw [Nat.div_add_mod', Nat.div_add_mod']⟩
  rw [getElem_ofChunks p _ hi hj ht]
  simp only [toChunks, Matrix.of_apply, chunkToBits_bitsToChunk, Vector.getElem_ofFn]

/-! ## The published maps -/

/-- `Frodo.Encode` (Appendix B of `[CiC25]`, Section 7.3 of `[ABD+25]`). -/
def Encode (p : Params) (b : Vector Bool (mbar * nbar * p.B)) :
    FrodoMatrix p mbar nbar :=
  EncodeChunks p (toChunks p b)

/-- `Frodo.Decode` (Appendix B of `[CiC25]`, Section 7.3 of `[ABD+25]`). -/
def Decode (p : Params) (C : FrodoMatrix p mbar nbar) :
    Vector Bool (mbar * nbar * p.B) :=
  ofChunks p (DecodeChunks p C)

/-- `Frodo.Decode` inverts `Frodo.Encode`. -/
theorem Decode_Encode (p : Params) (hw : p.WellFormed)
    (b : Vector Bool (mbar * nbar * p.B)) : Decode p (Encode p b) = b := by
  rw [Decode, Encode, DecodeChunks_EncodeChunks p hw, ofChunks_toChunks]

/-- `Frodo.Decode` recovers the message from an encoding perturbed by an error
matrix whose entries all lie in the window. -/
theorem Decode_Encode_add (p : Params) (hw : p.WellFormed)
    (b : Vector Bool (mbar * nbar * p.B)) (E : FrodoMatrix p mbar nbar)
    (hlo : ∀ i j, -(p.q : ℤ) ≤ 2 ^ (p.B + 1) * LatticeCrypto.centeredRepr (E i j))
    (hhi : ∀ i j, 2 ^ (p.B + 1) * LatticeCrypto.centeredRepr (E i j) < (p.q : ℤ)) :
    Decode p (Encode p b + E) = b := by
  rw [Decode, Encode, DecodeChunks_EncodeChunks_add p hw _ E hlo hhi, ofChunks_toChunks]

end FrodoKEM
