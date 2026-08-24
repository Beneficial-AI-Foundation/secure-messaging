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
  have hKpos : 0 < 2 ^ p.B := Nat.two_pow_pos _
  rcases eq_or_lt_of_le hw.B_le_D with hBD | hBD
  · exfalso
    have hR : p.noiseRadius = 0 := by
      rw [Params.noiseRadius, hQ, hBD]
      exact Nat.div_eq_of_lt (Nat.pow_lt_pow_right one_lt_two (by omega))
    rw [hR] at hlo hhi; omega
  have hD1 : 1 ≤ p.D := by omega
  have hsK : 2 ^ (p.D - p.B) * 2 ^ p.B = p.q := by
    rw [hQ, ← pow_add]; congr 1; omega
  have hhalf : p.q / 2 + p.q / 2 = p.q := by
    have h2 : 2 ∣ p.q := by rw [hQ]; exact dvd_pow_self 2 (by omega)
    omega
  have hRK : p.noiseRadius * 2 ^ p.B = p.q / 2 := by
    rw [Params.noiseRadius, hQ, Nat.pow_div hBD (by norm_num),
        Nat.pow_div (by omega : 1 ≤ p.D) (by norm_num), ← pow_add]
    congr 1; omega
  -- the noise window, transferred from centeredRepr to e.val
  have hE : e.val < p.noiseRadius ∨ p.q - p.noiseRadius ≤ e.val := by
    unfold LatticeCrypto.centeredRepr at hlo hhi
    split at hlo
    · rename_i h; left; rw [if_pos h] at hhi; exact_mod_cast hhi
    · rename_i h; right; rw [if_neg h] at hhi; omega
  have hevQ : e.val < p.q := ZMod.val_lt e
  -- the rounding term contributes 0 or a full K, either way nothing mod K
  have hquot : (e.val * 2 ^ p.B + p.q / 2) / p.q = 0
      ∨ (e.val * 2 ^ p.B + p.q / 2) / p.q = 2 ^ p.B := by
    have hcomm : p.q * 2 ^ p.B = 2 ^ p.B * p.q := Nat.mul_comm _ _
    have hQK : p.q ≤ p.q * 2 ^ p.B := Nat.le_mul_of_pos_right _ hKpos
    rcases hE with h | h
    · left
      apply Nat.div_eq_of_lt
      have h1 : e.val * 2 ^ p.B ≤ (p.noiseRadius - 1) * 2 ^ p.B :=
        Nat.mul_le_mul_right _ (by omega)
      have h2 : (p.noiseRadius - 1) * 2 ^ p.B = p.q / 2 - 2 ^ p.B := by
        rw [Nat.sub_mul, hRK, Nat.one_mul]
      omega
    · right
      apply Nat.div_eq_of_lt_le
      · have h1 : (p.q - p.noiseRadius) * 2 ^ p.B ≤ e.val * 2 ^ p.B :=
          Nat.mul_le_mul_right _ h
        have h2 : (p.q - p.noiseRadius) * 2 ^ p.B = p.q * 2 ^ p.B - p.q / 2 := by
          rw [Nat.sub_mul, hRK]
        omega
      · have h1 : e.val * 2 ^ p.B ≤ (p.q - 1) * 2 ^ p.B :=
          Nat.mul_le_mul_right _ (by omega)
        have h2 : (p.q - 1) * 2 ^ p.B = p.q * 2 ^ p.B - 2 ^ p.B := by
          rw [Nat.sub_mul, Nat.one_mul]
        have h3 : (2 ^ p.B + 1) * p.q = p.q * 2 ^ p.B + p.q := by
          rw [Nat.add_mul, Nat.one_mul, hcomm]
        omega
  -- the encoded value, and the mod-q wrap it may undergo
  have hval : (ec p k + e).val = (k.val * 2 ^ (p.D - p.B) + e.val) % p.q := by
    rw [ZMod.val_add, ec_val p hw k]
  set u := k.val * 2 ^ (p.D - p.B) + e.val with hu
  have hkey : (u % p.q * 2 ^ p.B + p.q / 2) / p.q + 2 ^ p.B * (u / p.q)
      = k.val + (e.val * 2 ^ p.B + p.q / 2) / p.q := by
    have hsplit : p.q * (u / p.q) + u % p.q = u := Nat.div_add_mod u p.q
    have step1 : (u % p.q * 2 ^ p.B + p.q / 2 + p.q * (2 ^ p.B * (u / p.q))) / p.q
        = (u % p.q * 2 ^ p.B + p.q / 2) / p.q + 2 ^ p.B * (u / p.q) :=
      Nat.add_mul_div_left _ _ hQpos
    have step2 : u % p.q * 2 ^ p.B + p.q / 2 + p.q * (2 ^ p.B * (u / p.q))
        = p.q * k.val + (e.val * 2 ^ p.B + p.q / 2) := by
      have hA : u % p.q * 2 ^ p.B + p.q * (2 ^ p.B * (u / p.q)) = u * 2 ^ p.B := by
        calc u % p.q * 2 ^ p.B + p.q * (2 ^ p.B * (u / p.q))
            = (u % p.q + p.q * (u / p.q)) * 2 ^ p.B := by ring
          _ = u * 2 ^ p.B := by rw [Nat.add_comm (u % p.q), hsplit]
      have hB : u * 2 ^ p.B = p.q * k.val + e.val * 2 ^ p.B := by
        rw [hu, Nat.add_mul, Nat.mul_assoc, hsK]; ring
      omega
    rw [← step1, step2, Nat.mul_add_div hQpos]
  -- conclude in ZMod (2 ^ B), where the multiple of K and the rounding term vanish
  rw [dc, hval, ZMod.natCast_mod]
  have hcast := congrArg (fun n : ℕ => (n : ZMod (2 ^ p.B))) hkey
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero] at hcast
  rcases hquot with h | h <;> rw [h] at hcast <;> simp at hcast <;>
    simpa [ZMod.natCast_zmod_val] using hcast

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
