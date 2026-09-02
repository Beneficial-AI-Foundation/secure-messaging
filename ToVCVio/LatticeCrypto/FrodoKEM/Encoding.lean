/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import ToVCVio.LatticeCrypto.FrodoKEM.Parameters
import LatticeCrypto.Ring.Norms

/-!
# FrodoKEM message encoding

`Frodo.Encode` and `Frodo.Decode`, with the proof that decoding inverts
encoding, exactly and in the presence of noise.

Two 2025 revisions are cited, because neither covers everything this file needs:

* `[CiC25]`, Glabush, Longa, Naehrig, Peikert, Stebila and Virdia, *FrodoKEM: A
  CCA-Secure Learning With Errors Key Encapsulation Mechanism*, IACR
  Communications in Cryptology 2:3, <https://cic.iacr.org/p/2/3/25>: the maps on
  bit strings, Appendix B, named in Section 3.3;
* `[ABD+25]`, Alkim, Bos, Ducas, Longa, Mironov, Naehrig, Nikolaenko, Peikert,
  Raghunathan and Stebila, *FrodoKEM Preliminary Standardization Proposal
  (submitted to ISO)*, September 2025,
  <https://frodokem.org/files/FrodoKEM_standard_proposal_20250929.pdf>: the same
  maps in Section 7.3, and the octet convention of Section 7.1, which `[CiC25]`
  leaves open. Both describe the same version of the scheme.

Encoding places `B` bits in each entry of an `mbar`-by-`nbar` matrix over
`ZMod q`. With `p : Params` left implicit and the least significant bit read
first throughout:

* `ec : ZMod (2 ^ B) → ZMod q`, `k ↦ k * q / 2 ^ B` — written `k * 2 ^ (D - B)`,
  which agrees under `q = 2 ^ D` — and `dc` back, `c ↦ ⌊c * 2 ^ B / q⌉ mod 2 ^ B`;
* `EncodeChunks`, `DecodeChunks`: `ec` and `dc` entrywise, on a message already
  chunked into `mbar * nbar` values of `ZMod (2 ^ B)`;
* Section 7.1 writes bit `8 * a + t` of a bit string as bit `t` of octet `a`,
  for `0 ≤ t < 8`;
* Section 7.3 writes bit `(i * nbar + j) * B + t` as bit `t` of the matrix entry
  in row `i` and column `j`, for `0 ≤ i < mbar`, `0 ≤ j < nbar` and
  `0 ≤ t < B`, so that the matrix is read row by row;
* `Encode` and `Decode` compose these on bit strings of length `mbar * nbar * B`,
  and `encodeMessage`, `decodeMessage` do the same on `Message p`.

Three of the `Params.WellFormed` conditions are used:

* `q = 2 ^ D` (`q_eq`) makes `q / 2 ^ B` exact, so both maps are bit shifts;
* `B ≤ D` (`B_le_D`) gives `2 ^ B ≤ q`, so `ec` does not wrap (`ec_val`);
* `ℓ = B * mbar * nbar` (`ell_eq`) makes a message fill the matrix exactly.

The encoded values then sit at spacing `q / 2 ^ B = 2 ^ (D - B)`. If the added
noise is less than half of it, then `dc` recovers `k`; `dc_ec_add` states the
window exactly, and `Params.noiseRadius` is that half-step rounded down.

Names follow the specification: the scalar maps keep its abbreviated lowercase
`ec` and `dc`, and since `EncodeChunks` and `DecodeChunks` are only the
entrywise half of `Frodo.Encode` and `Frodo.Decode`, the published names are
left for the composites `Encode` and `Decode`.

## Main definitions

* `ec`, `dc`: the scalar maps;
* `ChunkMatrix`: an `mbar`-by-`nbar` matrix of `B`-bit chunks;
* `bytesToBitsWith`, `bitsToBytesWith`, `matrixToBitsWith`,
  `bitsToMatrixWith`: the octet and matrix layers with the convention on one
  octet, resp. one entry, left as a parameter. Both files prove their round
  trips through these; neither specification states them, and the `…_eq`
  lemmas record that each published definition is one of them;
* `EncodeChunks`, `DecodeChunks`: the matrix maps, `ec` and `dc` applied
  entrywise;
* `byteToBits`, `bitsToByte` and their vector forms `bytesToBits`,
  `bitsToBytes`: the Section 7.1 octet conversion;
* `chunkToBits`, `bitsToChunk`, `toChunks`, `ofChunks`: the Section 7.3
  chunking;
* `Encode`, `Decode`: the published maps, on bit strings;
* `encodeMessage`, `decodeMessage`: the same on `Message p`, over a
  `ValidParams` since the length cast needs `ell_eq`;
* `Params.noiseRadius`: the half-step `q / 2 ^ (B + 1)`.

## Main results

* `dc_ec`, `DecodeChunks_EncodeChunks` and `Decode_Encode`: decoding inverts
  encoding;
* `dc_ec_add`, `DecodeChunks_EncodeChunks_add` and `Decode_Encode_add`: decoding
  inverts encoding perturbed by noise `e` with
  `-q ≤ 2 ^ (B + 1) * centeredRepr e < q`. This is Lemma 1, whose window is
  asymmetric: closed below and open above;
* `decodeMessage_encodeMessage` and `decodeMessage_encodeMessage_add`: the same
  on `Message p`;
* `bitsToBytes_bytesToBits`, `bytesToBits_bitsToBytes`, `ofChunks_toChunks` and
  `toChunks_ofChunks`: the two layers are inverse;
* `getElem_bytesToBits` and `getElem_ofChunks`: the position formulas this
  header states in prose, as theorems.
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
error `e` with `-q ≤ 2 ^ (B + 1) * centeredRepr e < q`. This is Lemma 1, stated
without division so that it stays correct at `B = D`, where the window admits
only `e = 0`; for `B < D` it is the half-open interval
`centeredRepr e ∈ [-q / 2 ^ (B + 1), q / 2 ^ (B + 1))`. -/
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

/-! ## Bit strings and octets

`Frodo.Encode` consumes a bit string of length `ℓ = B * mbar * nbar`; messages
are byte vectors. Section 7.1 of `[ABD+25]` fixes the conversion: bits are taken
left to right and packed from the least significant bit of each octet upwards.

`Frodo.Pack` uses the opposite order within each octet, so that conversion is
specified separately in `Packing.lean`, each definition written as its own
section of the specification states it. Only the proofs are shared: the
`…With` definitions and lemmas below take the octet convention as a parameter,
since concatenating octets is the same work whichever convention holds on one,
and both files discharge their round trips through them. -/

/-- Read a byte vector as a bit string, `f` giving the eight bits of an octet. -/
def bytesToBitsWith {n : ℕ} (f : Byte → Vector Bool 8) (bs : Bytes n) :
    Vector Bool (n * 8) :=
  (bs.map f).flatten

/-- Read a bit string as a byte vector, `g` giving the octet with the given
eight bits. -/
def bitsToBytesWith {n : ℕ} (g : Vector Bool 8 → Byte) (b : Vector Bool (n * 8)) :
    Bytes n :=
  Vector.ofFn fun i => g (Vector.ofFn fun j => b[i.val * 8 + j.val]'(by omega))

/-- The bits of octet `i` sit at positions `i * 8` to `i * 8 + 7`. -/
theorem getElem_bytesToBitsWith {n : ℕ} (f : Byte → Vector Bool 8) (bs : Bytes n)
    {i j : ℕ} (hi : i < n) (hj : j < 8) :
    (bytesToBitsWith f bs)[i * 8 + j]'(by omega) = (f bs[i])[j] := by
  simp [bytesToBitsWith, Vector.getElem_flatten, Nat.mod_eq_of_lt hj,
    show (i * 8 + j) / 8 = i by omega]

/-- A byte vector is recovered from its bit string, whenever an octet is
recovered from its own bits. -/
theorem bitsToBytesWith_bytesToBitsWith {n : ℕ} {f : Byte → Vector Bool 8}
    {g : Vector Bool 8 → Byte} (hgf : ∀ x, g (f x) = x) (bs : Bytes n) :
    bitsToBytesWith g (bytesToBitsWith f bs) = bs := by
  apply Vector.ext
  intro i hi
  rw [bitsToBytesWith, Vector.getElem_ofFn, ← hgf bs[i]]
  congr 1
  apply Vector.ext
  intro j hj
  simpa using getElem_bytesToBitsWith f bs hi hj

/-- A bit string is recovered from its byte vector, whenever the bits of an
octet are recovered from the octet. -/
theorem bytesToBitsWith_bitsToBytesWith {n : ℕ} {f : Byte → Vector Bool 8}
    {g : Vector Bool 8 → Byte} (hfg : ∀ v, f (g v) = v) (b : Vector Bool (n * 8)) :
    bytesToBitsWith f (bitsToBytesWith g b) = b := by
  apply Vector.ext
  intro k hk
  obtain ⟨i, j, hi, hj, rfl⟩ : ∃ i j, i < n ∧ j < 8 ∧ k = i * 8 + j :=
    ⟨k / 8, k % 8, by omega, by omega, by omega⟩
  rw [getElem_bytesToBitsWith _ _ hi hj, bitsToBytesWith, Vector.getElem_ofFn, hfg,
      Vector.getElem_ofFn]

/-- The eight bits of one octet, least significant first. -/
def byteToBits (x : Byte) : Vector Bool 8 :=
  Vector.ofFn fun j => x.toNat.testBit j

/-- The octet with the given eight bits, least significant first: `Nat.ofBits`
is that reading. -/
def bitsToByte (v : Vector Bool 8) : Byte :=
  UInt8.ofNat (Nat.ofBits fun j : Fin 8 => v[j])

/-- The convention of Section 7.1 applied to the two domain separators of the
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

/-- The bits of an octet are recovered from it. -/
theorem byteToBits_bitsToByte (v : Vector Bool 8) : byteToBits (bitsToByte v) = v := by
  simpa using (by decide : ∀ f : Fin 8 → Bool,
    byteToBits (bitsToByte (Vector.ofFn f)) = Vector.ofFn f) fun j => v[j]

/-- Section 7.1 of `[ABD+25]`: read a byte vector as a bit string, least
significant bit of each octet first. -/
def bytesToBits {n : ℕ} (bs : Bytes n) : Vector Bool (n * 8) :=
  (bs.map byteToBits).flatten

/-- The inverse of `bytesToBits`. -/
def bitsToBytes {n : ℕ} (b : Vector Bool (n * 8)) : Bytes n :=
  Vector.ofFn fun i =>
    bitsToByte (Vector.ofFn fun j => b[i.val * 8 + j.val]'(by omega))

/-- `bytesToBits` is the shared layer at the Section 7.1 convention. -/
theorem bytesToBits_eq {n : ℕ} (bs : Bytes n) :
    bytesToBits bs = bytesToBitsWith byteToBits bs := rfl

/-- `bitsToBytes` is the shared layer at the Section 7.1 convention. -/
theorem bitsToBytes_eq {n : ℕ} (b : Vector Bool (n * 8)) :
    bitsToBytes b = bitsToBytesWith bitsToByte b := rfl

/-- The bits of octet `i` sit at positions `i * 8` to `i * 8 + 7`, least
significant first. -/
theorem getElem_bytesToBits {n : ℕ} (bs : Bytes n) {i j : ℕ} (hi : i < n) (hj : j < 8) :
    (bytesToBits bs)[i * 8 + j]'(by omega) = (byteToBits bs[i])[j] := by
  rw [bytesToBits_eq]
  exact getElem_bytesToBitsWith byteToBits bs hi hj

/-- A byte vector is recovered from its bit string. -/
theorem bitsToBytes_bytesToBits {n : ℕ} (bs : Bytes n) :
    bitsToBytes (bytesToBits bs) = bs := by
  rw [bitsToBytes_eq, bytesToBits_eq]
  exact bitsToBytesWith_bytesToBitsWith bitsToByte_byteToBits bs

/-- A bit string is recovered from its byte vector. -/
theorem bytesToBits_bitsToBytes {n : ℕ} (b : Vector Bool (n * 8)) :
    bytesToBits (bitsToBytes b) = b := by
  rw [bytesToBits_eq, bitsToBytes_eq]
  exact bytesToBitsWith_bitsToBytesWith byteToBits_bitsToByte b

/-! ## Chunking

Section 7.3 of `[ABD+25]`: each `B`-bit run of the input, read from its least
significant bit, becomes one matrix entry; entries are filled row by row and
each row is filled left to right, so bits `0` to `B - 1` of the input fill
entry `(0, 0)`.

The bit strings here have length `mbar * nbar * B`, one `B`-bit run per entry.
`Params.WellFormed.ell_eq` identifies that with `ℓ`, and `ellBytes_mul_eight`
turns it into the byte count of a `Message p`. -/

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
takes `d` bits and entries are laid out row by row. This is the bound the
matrix layer below indexes with, at `d = B` for the chunks and `d = D` for the
packed entries of `Packing.lean`. -/
theorem bitIndex_lt {r c d i j t : ℕ} (hi : i < r) (hj : j < c) (ht : t < d) :
    (i * c + j) * d + t < r * c * d :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left ht _)
    (by rw [← Nat.succ_mul, Nat.mul_comm i c]; gcongr
        exact Nat.mul_add_lt_mul_of_lt_of_lt hi hj)

/-! ### The shared matrix layer

Both `ofChunks` here and `Frodo.Pack` of `Packing.lean` cut a matrix into one
bit block per entry, differing only in the codec on one entry and its width.
Those are parameters below, so that the index lemma and the two round trips are
proved once; the published definitions stay as their sections state them and
bridge to these by `rfl`. -/

/-- Lay the entries of a matrix out as bit blocks of width `d`, row by row and
each row left to right, `f` giving the `d` bits of one entry. -/
def matrixToBitsWith {α : Type*} {r c d : ℕ} (f : α → Vector Bool d)
    (M : Matrix (Fin r) (Fin c) α) : Vector Bool (r * c * d) :=
  (Vector.ofFn fun idx : Fin (r * c) => f (M idx.divNat idx.modNat)).flatten

/-- Read a bit string back as a matrix, `g` giving the entry with the given
`d` bits. -/
def bitsToMatrixWith {α : Type*} {r c d : ℕ} (g : Vector Bool d → α)
    (b : Vector Bool (r * c * d)) : Matrix (Fin r) (Fin c) α :=
  Matrix.of fun i j => g (Vector.ofFn fun l =>
    b[(i.val * c + j.val) * d + l.val]'(bitIndex_lt i.isLt j.isLt l.isLt))

/-- The bits of entry `(i, j)` sit at positions `(i * c + j) * d` onwards. -/
theorem getElem_matrixToBitsWith {α : Type*} {r c d : ℕ} (f : α → Vector Bool d)
    (M : Matrix (Fin r) (Fin c) α) {i j l : ℕ} (hi : i < r) (hj : j < c) (hl : l < d) :
    (matrixToBitsWith f M)[(i * c + j) * d + l]'(bitIndex_lt hi hj hl) =
      (f (M ⟨i, hi⟩ ⟨j, hj⟩))[l] := by
  rw [matrixToBitsWith, Vector.getElem_flatten]
  simp only [Nat.mul_comm (i * c + j) d, Nat.mul_add_div (by omega : 0 < d),
    Nat.mul_add_mod, Nat.div_eq_of_lt hl, Nat.mod_eq_of_lt hl, Nat.add_zero,
    Vector.getElem_ofFn]
  congr 3 <;> simp only [Fin.divNat, Fin.modNat, Nat.mul_comm i c,
    Nat.mul_add_div (by omega : 0 < c), Nat.mul_add_mod, Nat.div_eq_of_lt hj,
    Nat.mod_eq_of_lt hj, Nat.add_zero]

/-- A matrix is recovered from its bit string, whenever an entry is recovered
from its own bits. -/
theorem bitsToMatrixWith_matrixToBitsWith {α : Type*} {r c d : ℕ}
    {f : α → Vector Bool d} {g : Vector Bool d → α} (hgf : ∀ x, g (f x) = x)
    (M : Matrix (Fin r) (Fin c) α) :
    bitsToMatrixWith g (matrixToBitsWith f M) = M := by
  ext i j
  simp only [bitsToMatrixWith, Matrix.of_apply]
  rw [← hgf (M i j)]
  congr 1
  apply Vector.ext
  intro l hl
  rw [Vector.getElem_ofFn]
  exact getElem_matrixToBitsWith f M i.isLt j.isLt hl

/-- A bit string is recovered from its matrix, whenever the bits of an entry
are recovered from the entry. -/
theorem matrixToBitsWith_bitsToMatrixWith {α : Type*} {r c d : ℕ}
    {f : α → Vector Bool d} {g : Vector Bool d → α} (hfg : ∀ v, f (g v) = v)
    (b : Vector Bool (r * c * d)) :
    matrixToBitsWith f (bitsToMatrixWith g b) = b := by
  apply Vector.ext
  intro k hk
  obtain ⟨i, j, l, hi, hj, hl, rfl⟩ :
      ∃ i j l, i < r ∧ j < c ∧ l < d ∧ k = (i * c + j) * d + l :=
    ⟨k / d / c, k / d % c, k % d,
      Nat.div_lt_of_lt_mul (Nat.div_lt_of_lt_mul
        (by rw [Nat.mul_comm d (c * r), Nat.mul_comm c r]; exact hk)),
      Nat.mod_lt _ (Nat.pos_of_ne_zero fun h => absurd hk (by simp [h])),
      Nat.mod_lt _ (Nat.pos_of_ne_zero fun h => absurd hk (by simp [h])),
      by rw [Nat.div_add_mod', Nat.div_add_mod']⟩
  rw [getElem_matrixToBitsWith _ _ hi hj hl]
  simp only [bitsToMatrixWith, Matrix.of_apply, hfg, Vector.getElem_ofFn]

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

/-- `ofChunks` is the shared layer at the Section 7.3 chunking. -/
theorem ofChunks_eq (p : Params) (M : ChunkMatrix p) :
    ofChunks p M = matrixToBitsWith (chunkToBits p) M := rfl

/-- `toChunks` is the shared layer at the Section 7.3 chunking. -/
theorem toChunks_eq (p : Params) (b : Vector Bool (mbar * nbar * p.B)) :
    toChunks p b = bitsToMatrixWith (bitsToChunk p) b := rfl

/-- Bit `t` of entry `(i, j)` sits at position `(i * nbar + j) * B + t`, the
layout of Section 7.3. -/
theorem getElem_ofChunks (p : Params) (M : ChunkMatrix p) {i j t : ℕ}
    (hi : i < mbar) (hj : j < nbar) (ht : t < p.B) :
    (ofChunks p M)[(i * nbar + j) * p.B + t]'(bitIndex_lt hi hj ht) =
      (chunkToBits p (M ⟨i, hi⟩ ⟨j, hj⟩))[t] := by
  rw [ofChunks_eq]
  exact getElem_matrixToBitsWith (chunkToBits p) M hi hj ht

/-- The chunks are recovered from their bit string. -/
theorem toChunks_ofChunks (p : Params) (M : ChunkMatrix p) :
    toChunks p (ofChunks p M) = M := by
  rw [toChunks_eq, ofChunks_eq]
  exact bitsToMatrixWith_matrixToBitsWith (bitsToChunk_chunkToBits p) M

/-- A bit string is recovered from its chunks. -/
theorem ofChunks_toChunks (p : Params) (b : Vector Bool (mbar * nbar * p.B)) :
    ofChunks p (toChunks p b) = b := by
  rw [ofChunks_eq, toChunks_eq]
  exact matrixToBitsWith_bitsToMatrixWith (chunkToBits_bitsToChunk p) b

/-! ## The published maps -/

/-- `Frodo.Encode` (Appendix B of `[CiC25]`, Section 7.3 of `[ABD+25]`): cut
the bit string into `B`-bit chunks, then apply `ec` entrywise. -/
def Encode (p : Params) (b : Vector Bool (mbar * nbar * p.B)) :
    FrodoMatrix p mbar nbar :=
  EncodeChunks p (toChunks p b)

/-- `Frodo.Decode` (Appendix B of `[CiC25]`, Section 7.3 of `[ABD+25]`): apply
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

/-! ## Messages

`Message p` is `ellBytes` bytes; `Params.WellFormed.ell_eq` makes that the same
number of bits the matrix holds. The two maps here therefore need the proof in
order to typecheck, not merely to be proved correct, so they take a
`ValidParams`: a record carrying its own well-formedness, which a caller passes
as one argument. Everything above this section stays on a bare `Params`, taking
a `WellFormed` hypothesis only where a theorem needs one. -/

/-- A message has exactly as many bits as the matrix has chunk bits. The
division in `ellBytes` is exact because `mbar = nbar = 8`. -/
theorem ellBytes_mul_eight (p : Params) (hw : p.WellFormed) :
    p.ellBytes * 8 = mbar * nbar * p.B := by
  simp only [Params.ellBytes, hw.ell_eq, mbar, nbar]; omega

/-- `Frodo.Encode` on a message: Section 7.1 then Section 7.3. The
well-formedness carried by `ValidParams` enters only through the length cast of
`ellBytes_mul_eight`. -/
def encodeMessage (p : ValidParams) (mu : Message p.toParams) :
    FrodoMatrix p.toParams mbar nbar :=
  Encode p.toParams (Vector.cast (ellBytes_mul_eight p.toParams p.wf) (bytesToBits mu))

/-- `Frodo.Decode` returning a message: Section 7.3 then Section 7.1, with the
same cast as `encodeMessage` in reverse. -/
def decodeMessage (p : ValidParams) (C : FrodoMatrix p.toParams mbar nbar) :
    Message p.toParams :=
  bitsToBytes (Vector.cast (ellBytes_mul_eight p.toParams p.wf).symm (Decode p.toParams C))

/-- `decodeMessage` inverts `encodeMessage`. -/
theorem decodeMessage_encodeMessage (p : ValidParams) (mu : Message p.toParams) :
    decodeMessage p (encodeMessage p mu) = mu := by
  rw [decodeMessage, encodeMessage, Decode_Encode p.toParams p.wf]
  simp [bitsToBytes_bytesToBits]

/-- `decodeMessage` recovers the message from an encoding perturbed by an error
matrix whose entries all lie in the window of `dc_ec_add`. -/
theorem decodeMessage_encodeMessage_add (p : ValidParams) (mu : Message p.toParams)
    (E : FrodoMatrix p.toParams mbar nbar)
    (hlo : ∀ i j, -(p.q : ℤ) ≤ 2 ^ (p.B + 1) * centeredRepr (E i j))
    (hhi : ∀ i j, 2 ^ (p.B + 1) * centeredRepr (E i j) < (p.q : ℤ)) :
    decodeMessage p (encodeMessage p mu + E) = mu := by
  rw [decodeMessage, encodeMessage, Decode_Encode_add p.toParams p.wf _ E hlo hhi]
  simp [bitsToBytes_bytesToBits]

end FrodoKEM
