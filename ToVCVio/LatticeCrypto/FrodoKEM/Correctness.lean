/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import ToVCVio.LatticeCrypto.FrodoKEM.Encoding
import ToVCVio.LatticeCrypto.FrodoKEM.Packing
import LatticeCrypto.Ring.Norms

/-!
# FrodoKEM encoding and packing correctness

The proofs about the maps that `Bits.lean`, `Encoding.lean` and `Packing.lean`
specify. References are as in `Parameters.lean`. Both documents state the exact
round trip `dc (ec k) = k`, `[CiC25]` in Appendix B and `[LBES26]` in
Section 6.3. Only `[CiC25]` bounds the noise `dc` tolerates, as Lemma 1 of
Section 4.1, so `dc_ec_add` is cited from it alone.

Two of the `Params.WellFormed` conditions are used. `q = 2 ^ D` (`q_eq`) makes
`q / 2 ^ B` exact, so `ec` and `dc` are bit shifts, and `entryToBits` loses
nothing. `B ≤ D` (`B_le_D`) gives `2 ^ B ≤ q`, so `ec` does not wrap.

The encoded values sit at spacing `q / 2 ^ B = 2 ^ (D - B)`. If the noise added
stays within half of that, `dc` recovers the chunk it was given.

## Main definitions

* `Params.noiseRadius`: the half-step `q / 2 ^ (B + 1)`, which is that half
  spacing, and so the bound on the noise `dc` tolerates.

## Main results

* `dc_ec`, `DecodeChunks_EncodeChunks` and `Decode_Encode`: decoding inverts
  encoding;
* `Unpack_Pack` and `Pack_Unpack`: unpacking inverts packing, and back;
* `dc_ec_add`, `DecodeChunks_EncodeChunks_add` and `Decode_Encode_add`: the
  same as the first, with the encoding perturbed by a noise `e` satisfying
  `-q ≤ 2 ^ (B + 1) * centeredRepr e < q`, which is Lemma 1 of Section 4.1
  cleared of its denominator;
* `bitsToMatrixWith_matrixToBitsWith` and `matrixToBitsWith_bitsToMatrixWith`:
  if `g` inverts `f` on one entry, then `bitsToMatrixWith g` inverts
  `matrixToBitsWith f` on the whole matrix. `Unpack_Pack` and `Pack_Unpack` are
  this at `D` bits per entry, `bitsToChunkMatrix_chunkMatrixToBits` and
  `chunkMatrixToBits_bitsToChunkMatrix` at `B`;
* `bitsToChunk_chunkToBits`, `chunkToBits_bitsToChunk`,
  `bitsToEntry_entryToBits` and `entryToBits_bitsToEntry`: those maps on one
  chunk and on one entry.
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

/-- A matrix is recovered from its bit string, whenever an entry is recovered
from its own bits. -/
theorem bitsToMatrixWith_matrixToBitsWith {α : Type*} {r c d : ℕ}
    {f : α → Vector Bool d} {g : Vector Bool d → α} (hgf : ∀ x, g (f x) = x)
    (M : Matrix (Fin r) (Fin c) α) :
    bitsToMatrixWith g r c (matrixToBitsWith f M) = M := by
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
theorem matrixToBitsWith_bitsToMatrixWith {α : Type*} {d : ℕ}
    {f : α → Vector Bool d} {g : Vector Bool d → α} (hfg : ∀ v, f (g v) = v)
    (r c : ℕ) (b : Vector Bool (r * c * d)) :
    matrixToBitsWith f (bitsToMatrixWith g r c b) = b := by
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

/-- The chunks are recovered from their bit string. -/
@[simp]
theorem bitsToChunkMatrix_chunkMatrixToBits (p : Params) (M : ChunkMatrix p) :
    bitsToChunkMatrix p (chunkMatrixToBits p M) = M :=
  bitsToMatrixWith_matrixToBitsWith (bitsToChunk_chunkToBits p) M

/-- A bit string is recovered from its chunks. -/
@[simp]
theorem chunkMatrixToBits_bitsToChunkMatrix (p : Params)
    (b : Vector Bool (mbar * nbar * p.B)) :
    chunkMatrixToBits p (bitsToChunkMatrix p b) = b :=
  matrixToBitsWith_bitsToMatrixWith (chunkToBits_bitsToChunk p) mbar nbar b

/-- `Frodo.Decode` inverts `Frodo.Encode`. -/
theorem Decode_Encode (p : Params) (hw : p.WellFormed)
    (b : Vector Bool (mbar * nbar * p.B)) : Decode p (Encode p b) = b := by
  rw [Decode, Encode, DecodeChunks_EncodeChunks p hw, chunkMatrixToBits_bitsToChunkMatrix]

/-- `Frodo.Decode` recovers the bit string from an encoding perturbed by an
error matrix whose entries all lie in the window of `dc_ec_add`. -/
theorem Decode_Encode_add (p : Params) (hw : p.WellFormed)
    (b : Vector Bool (mbar * nbar * p.B)) (E : FrodoMatrix p mbar nbar)
    (hlo : ∀ i j, -(p.q : ℤ) ≤ 2 ^ (p.B + 1) * centeredRepr (E i j))
    (hhi : ∀ i j, 2 ^ (p.B + 1) * centeredRepr (E i j) < (p.q : ℤ)) :
    Decode p (Encode p b + E) = b := by
  rw [Decode, Encode, DecodeChunks_EncodeChunks_add p hw _ E hlo hhi,
    chunkMatrixToBits_bitsToChunkMatrix]

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
