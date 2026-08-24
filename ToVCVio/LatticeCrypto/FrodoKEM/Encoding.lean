/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import ToVCVio.LatticeCrypto.FrodoKEM.Parameters
import LatticeCrypto.Ring.Norms

/-!
# FrodoKEM message encoding

`Frodo.Encode` and `Frodo.Decode` of Section 2.2.2 of the FrodoKEM
specification, published at [frodokem.org](https://frodokem.org/) and as
[Glabush, Longa, Naehrig, Peikert, Stebila and Virdia,
*FrodoKEM: A CCA-Secure Learning With Errors Key Encapsulation Mechanism*,
Communications in Cryptology 2:3](https://cic.iacr.org/p/2/3/25).

Encoding places `B` bits in each entry of an `mbar`-by-`nbar` matrix over
`ZMod q`, scaled to the top of the modulus so that the low bits are free to
absorb noise. The scalar maps are

* `ec k = k * q / 2 ^ B`, which spaces the `2 ^ B` representable values evenly
  across `ZMod q`;
* `dc c = ⌊c * 2 ^ B / q⌉ mod 2 ^ B`, which rounds back to the nearest one.

Because `q = 2 ^ D` the rounding is exact bit arithmetic: `ec` is a shift by
`D - B`, and `dc` is a shift back after adding the half-step `q / 2`. The
relation `q = 2 ^ D` is supplied by `Params.WellFormed.q_eq`, and `B ≤ D` by
`Params.WellFormed.B_le_D`; both are load-bearing rather than cosmetic, since
`ec` wraps when `B > D` and `ℕ` subtraction truncates `D - B` to zero.

## Chunked input

The specification's `Frodo.Encode` consumes a bit string of length
`ℓ = B * mbar * nbar`. The maps here consume that string already chunked into
`mbar * nbar` values of `ZMod (2 ^ B)`, one per matrix entry. The bit-string
layer that produces the chunks is bit manipulation of the same kind as
`Frodo.Pack` and `Frodo.Unpack`, and is specified alongside them; composing it
with `Encode` here recovers the published map.

## Noise tolerance

`dc` recovers `k` from `ec k + e` when `e` is small, and the tolerated window
is asymmetric: `centeredRepr e ∈ [-q / 2 ^ (B + 1), q / 2 ^ (B + 1) - 1]`,
because the half-step is added before a floor division rather than a symmetric
rounding. This matches the specification, which states the same one-sided
bound.
-/

namespace FrodoKEM

namespace Params

/-- The half-step `q / 2 ^ (B + 1)` that bounds the tolerated noise: the
representable values `ec k` are `q / 2 ^ B` apart, and `dc` rounds to the
nearest one. -/
def noiseRadius (p : Params) : ℕ := p.q / 2 ^ (p.B + 1)

end Params

/-- `Frodo.Encode`'s scalar map (Section 2.2.2): place `k` in the top `B` bits
of an element of `ZMod q` by scaling it by `q / 2 ^ B = 2 ^ (D - B)`. -/
def ec (p : Params) (k : ZMod (2 ^ p.B)) : ZMod p.q :=
  (k.val * 2 ^ (p.D - p.B) : ℕ)

/-- `Frodo.Decode`'s scalar map (Section 2.2.2): round `c` to the nearest
multiple of `q / 2 ^ B` and read off which multiple it is, as
`⌊c * 2 ^ B / q⌉ mod 2 ^ B`. -/
def dc (p : Params) (c : ZMod p.q) : ZMod (2 ^ p.B) :=
  ((c.val * 2 ^ p.B + p.q / 2) / p.q % 2 ^ p.B : ℕ)

/-- `ec` does not wrap: its value is the unreduced product `k * 2 ^ (D - B)`.
This is where `B ≤ D` is needed, via `2 ^ B * 2 ^ (D - B) = 2 ^ D = q`. -/
theorem ec_val (p : Params) (hw : p.WellFormed) (k : ZMod (2 ^ p.B)) :
    (ec p k).val = k.val * 2 ^ (p.D - p.B) := by
  apply ZMod.val_cast_of_lt
  rw [hw.q_eq, ← pow_mul_pow_sub (2:ℕ) hw.B_le_D]
  gcongr
  exact ZMod.val_lt k

/-- Decoding inverts encoding (Section 2.2.2). -/
theorem dc_ec (p : Params) (hw : p.WellFormed) (k : ZMod (2 ^ p.B)) :
    dc p (ec p k) = k := by
  rw [dc, ec_val p hw k, hw.q_eq, mul_assoc, ← Nat.pow_add,
      Nat.sub_add_cancel hw.B_le_D, Nat.mul_comm,
      Nat.mul_add_div (Nat.two_pow_pos p.D),
      Nat.div_eq_of_lt (Nat.div_lt_self (Nat.two_pow_pos p.D) one_lt_two),
      Nat.add_zero, ZMod.natCast_mod]
  exact ZMod.natCast_zmod_val k

/-- The rounding step of `dc`, as a statement about natural numbers: the
quotient it computes recovers `v` modulo `K`, for any `ev` inside the tolerated
window. Stated with `Q`, `K = 2 ^ B`, `s = q / 2 ^ B` and `R` abstract so that
the arithmetic is separated from the parameter bookkeeping.

The wrap of `v * s + ev` past the modulus is never tracked, only its residue:
it contributes a multiple of `K`, which vanishes mod `K`. What remains is
`v` plus the rounding term `(ev * K + Q / 2) / Q`, and that term is `0` for
noise just above zero and exactly `K` for noise just below the modulus. -/
private theorem dc_quotient {Q K s v ev : ℕ} (R : ℕ) (hQ : 0 < Q) (hK : 0 < K)
    (hsK : s * K = Q) (hRK : R * K = Q / 2) (hhalf : Q / 2 + Q / 2 = Q)
    (hv : v < K) (hev : ev < Q) (hwin : ev < R ∨ Q - R ≤ ev) :
    ((v * s + ev) % Q * K + Q / 2) / Q % K = v := by
  have hcomm : Q * K = K * Q := Nat.mul_comm _ _
  have hRQ : R ≤ R * K := Nat.le_mul_of_pos_right _ hK
  have hQK : Q ≤ Q * K := Nat.le_mul_of_pos_right _ hK
  have hrnd : (ev * K + Q / 2) / Q = 0 ∨ (ev * K + Q / 2) / Q = K := by
    rcases hwin with h | h
    · refine Or.inl (Nat.div_eq_of_lt ?_)
      have := Nat.mul_le_mul_right K (by omega : ev + 1 ≤ R)
      rw [Nat.add_mul, Nat.one_mul, hRK] at this; omega
    · refine Or.inr (Nat.div_eq_of_lt_le ?_ ?_)
      · have := Nat.mul_le_mul_right K (by omega : Q ≤ ev + R)
        rw [Nat.add_mul, hRK] at this; omega
      · have h1 := Nat.mul_le_mul_right K (by omega : ev + 1 ≤ Q)
        have h2 : (K + 1) * Q = K * Q + Q := by ring
        rw [Nat.add_mul, Nat.one_mul] at h1; omega
  have hkey : ((v * s + ev) % Q * K + Q / 2) / Q + K * ((v * s + ev) / Q)
      = v + (ev * K + Q / 2) / Q := by
    set u := v * s + ev with hu
    have h1 : u % Q * K + Q * (K * (u / Q)) = u * K := by
      calc u % Q * K + Q * (K * (u / Q)) = (u % Q + Q * (u / Q)) * K := by ring
        _ = u * K := by rw [Nat.add_comm (u % Q), Nat.div_add_mod]
    have h2 : u * K = Q * v + ev * K := by rw [hu, Nat.add_mul, Nat.mul_assoc, hsK]; ring
    rw [← Nat.add_mul_div_left _ (K * (u / Q)) hQ,
        show u % Q * K + Q / 2 + Q * (K * (u / Q)) = Q * v + (ev * K + Q / 2) by omega,
        Nat.mul_add_div hQ]
  rw [← Nat.add_mul_mod_self_left _ K ((v * s + ev) / Q), hkey]
  rcases hrnd with h | h <;> rw [h] <;> simp [Nat.mod_eq_of_lt hv]

/-- Decoding recovers `k` from an encoding perturbed by noise below the
rounding half-step. The window is asymmetric, matching the floor division in
`dc`: the lower end is closed and the upper end open. -/
theorem dc_ec_add (p : Params) (hw : p.WellFormed) (k : ZMod (2 ^ p.B))
    (e : ZMod p.q)
    (hlo : -(p.noiseRadius : ℤ) ≤ LatticeCrypto.centeredRepr e)
    (hhi : LatticeCrypto.centeredRepr e < (p.noiseRadius : ℤ)) :
    dc p (ec p k + e) = k := by
  have hQ : p.q = 2 ^ p.D := hw.q_eq
  have hQpos : 0 < p.q := by rw [hQ]; exact Nat.two_pow_pos _
  haveI : NeZero p.q := ⟨by omega⟩
  -- with every bit of an entry carrying message there is no room for error
  rcases eq_or_lt_of_le hw.B_le_D with hBD | hBD
  · have : p.noiseRadius = 0 := by
      rw [Params.noiseRadius, hQ, hBD]
      exact Nat.div_eq_of_lt (Nat.pow_lt_pow_right one_lt_two (by omega))
    omega
  have hsK : 2 ^ (p.D - p.B) * 2 ^ p.B = p.q := by rw [hQ, ← pow_add]; congr 1; omega
  have hRK : p.noiseRadius * 2 ^ p.B = p.q / 2 := by
    rw [Params.noiseRadius, hQ, Nat.pow_div hBD (by norm_num),
        Nat.pow_div (by omega : 1 ≤ p.D) (by norm_num), ← pow_add]
    congr 1; omega
  have hhalf : p.q / 2 + p.q / 2 = p.q := by
    have : 2 ∣ p.q := by rw [hQ]; exact dvd_pow_self 2 (by omega)
    omega
  -- the window, read off `e.val` rather than its centered representative
  have hwin : e.val < p.noiseRadius ∨ p.q - p.noiseRadius ≤ e.val := by
    unfold LatticeCrypto.centeredRepr at hlo hhi
    split at hlo
    · rename_i h; exact Or.inl (by rw [if_pos h] at hhi; exact_mod_cast hhi)
    · rename_i h; exact Or.inr (by rw [if_neg h] at hhi; omega)
  rw [dc, ZMod.val_add, ec_val p hw k,
    dc_quotient p.noiseRadius hQpos (Nat.two_pow_pos p.B) hsK hRK hhalf
      (ZMod.val_lt k) (ZMod.val_lt e) hwin]
  exact ZMod.natCast_zmod_val k

/-! ## The matrix maps

`Frodo.Encode` and `Frodo.Decode` apply the scalar maps entrywise to an
`mbar`-by-`nbar` matrix. -/

/-- A matrix of `B`-bit chunks, one per entry: the chunked form of a message of
`ℓ = B * mbar * nbar` bits. -/
abbrev ChunkMatrix (p : Params) := Matrix (Fin mbar) (Fin nbar) (ZMod (2 ^ p.B))

/-- `Frodo.Encode` (Section 2.2.2), on input already chunked into `B`-bit
values: apply `ec` to every entry. -/
def Encode (p : Params) (M : ChunkMatrix p) : FrodoMatrix p mbar nbar :=
  M.map (ec p)

/-- `Frodo.Decode` (Section 2.2.2), returning the chunked form: apply `dc` to
every entry. -/
def Decode (p : Params) (C : FrodoMatrix p mbar nbar) : ChunkMatrix p :=
  C.map (dc p)

/-- `Frodo.Decode` inverts `Frodo.Encode`. -/
theorem Decode_Encode (p : Params) (hw : p.WellFormed) (M : ChunkMatrix p) :
    Decode p (Encode p M) = M := by
  ext i j
  simp [Decode, Encode, dc_ec p hw]

/-- `Frodo.Decode` recovers the message from an encoding perturbed by an error
matrix whose entries all lie in the tolerated window. The hypothesis is stated
entrywise: `LatticeCrypto.cInfNorm` is defined for polynomials rather than
matrices, and FrodoKEM has no polynomial ring. -/
theorem Decode_Encode_add (p : Params) (hw : p.WellFormed) (M : ChunkMatrix p)
    (E : FrodoMatrix p mbar nbar)
    (hlo : ∀ i j, -(p.noiseRadius : ℤ) ≤ LatticeCrypto.centeredRepr (E i j))
    (hhi : ∀ i j, LatticeCrypto.centeredRepr (E i j) < (p.noiseRadius : ℤ)) :
    Decode p (Encode p M + E) = M := by
  ext i j
  simpa [Decode, Encode] using dc_ec_add p hw (M i j) (E i j) (hlo i j) (hhi i j)

end FrodoKEM
