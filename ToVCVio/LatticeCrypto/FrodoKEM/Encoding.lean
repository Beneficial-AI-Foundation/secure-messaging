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

FrodoKEM has been published in several revisions. The one followed here, and by
`Parameters.lean`, is [Glabush, Longa, Naehrig, Peikert, Stebila and Virdia,
*FrodoKEM: A CCA-Secure Learning With Errors Key Encapsulation Mechanism*, IACR
Communications in Cryptology 2:3 (2025)](https://cic.iacr.org/p/2/3/25); every
reference below is to it.

`Frodo.Encode` and `Frodo.Decode` are defined in Appendix B, "Additional
algorithms", and named in Section 3.3, "Matrix encoding and packing".

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

/-- `Frodo.Encode`'s scalar map (Appendix B): `k ↦ k * 2 ^ (D - B)`, placing
`k` in the top `B` bits of an element of `ZMod q`. -/
def ec (p : Params) (k : ZMod (2 ^ p.B)) : ZMod p.q :=
  (k.val * 2 ^ (p.D - p.B) : ℕ)

/-- `Frodo.Decode`'s scalar map (Appendix B):
`c ↦ ⌊c * 2 ^ B / q⌉ mod 2 ^ B`, the index of the multiple of `q / 2 ^ B`
nearest to `c`. -/
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

/-- The rounding step of `dc` as natural-number arithmetic, with the parameters
abstract:

* `q` is the modulus and `n = 2 ^ B` the number of values one entry represents;
* `s = q / n` is the spacing between those values, and `r = s / 2` the half-step
  that `dc` adds before dividing;
* `v < n` is the encoded value and `ev` the noise, as a residue mod `q`.

For every `ev` in the window — below the half-step, or within it of `q` — the
quotient `dc` computes recovers `v` modulo `n`. -/
private theorem dc_quotient {q n s v ev : ℕ} (r : ℕ) (hn : 0 < n)
    (hsn : s * n = q) (hrn : 2 * (r * n) = q)
    (hv : v < n) (hev : ev < q) (hwin : ev < r ∨ q - r ≤ ev) :
    ((v * s + ev) % q * n + q / 2) / q % n = v := by
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

/-- Decoding recovers `k` from an encoding perturbed by noise below the
half-step, over a window closed below and open above. -/
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
    dc_quotient p.noiseRadius (Nat.two_pow_pos p.B) hsn hrn (ZMod.val_lt k) (ZMod.val_lt e) hwin]
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

end FrodoKEM
