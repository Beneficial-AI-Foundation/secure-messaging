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
  sorry

end FrodoKEM
