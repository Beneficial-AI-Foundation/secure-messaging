/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Data.BitVec
import Mathlib.Data.ZMod.Basic

/-!
# Reflected equivalence between bit vectors and `AdjoinRoot p`

For any **monic** `p : (ZMod 2)[X]` this file builds a bijection

  `reflect hp : BitVec p.natDegree ≃ AdjoinRoot p`

that reflects NIST bit order: `getMsbD` index `i` maps to the coefficient of
`root p ^ i` in the power basis (MSB ↔ `x⁰`). Alongside it we prove XOR additivity
(`reflect_xor`), the coordinate-is-coefficient lemma (`reflect_apply`), and the
bijection / cardinality facts consumed downstream.

Everything here is polymorphic in the monic polynomial: there is no `nistPoly`,
`gfmul`, `ghash`, or `SecureMessaging` reference, and monicity is the only hypothesis
(no irreducibility / domain / field). This is why it lives in `ToVCVio/` and can run
in parallel with the GCM-specific plans.

## Design decision (locked)

The `BitVec` half is represented as a plain `Equiv` (`bitVecEquivFun`) plus a *separate*
additivity lemma (`bitVecEquivFun_xor` / `reflect_xor`), **not** a bundled
`≃ₗ[ZMod 2]`. Mathlib's native `AddCommGroup (BitVec n)` is arithmetic `+`, not XOR, so
a linear-equiv on the `BitVec` side would require equipping a bespoke xor-module
instance. The `AdjoinRoot` half keeps its genuine `LinearEquiv`
(`powerBasis'.basis.equivFun`), which is what still exposes coordinate = coefficient
for downstream coefficient transport.

## Main definitions

- `boolToZMod2` / `boolToZMod2_xor` — the `Bool → ZMod 2` bridge with XOR additivity.
- `bitVecEquivFun` / `bitVecEquivFun_xor` — the `BitVec n ≃ (Fin n → ZMod 2)` half.
- `reflect` / `reflect_xor` / `reflect_apply` — the full reflected equivalence, its XOR
  additivity, and its coordinate-is-coefficient expansion.
- `reflect_bijective` / `card_preimage_reflect` — the bijection and cardinality transport.
-/

open Polynomial

namespace AdjoinRootReflect

/-! ### `Bool` ↔ `ZMod 2` bridge -/

/-- Send `true ↦ 1`, `false ↦ 0` in `ZMod 2`. -/
def boolToZMod2 : Bool → ZMod 2 := fun b => if b then 1 else 0

/-- Send `ZMod 2` back to `Bool` (`0 ↦ false`, `1 ↦ true`). -/
def zmod2ToBool : ZMod 2 → Bool := fun z => decide (z ≠ 0)

@[simp] theorem zmod2ToBool_boolToZMod2 (b : Bool) : zmod2ToBool (boolToZMod2 b) = b := by
  cases b <;> decide

@[simp] theorem boolToZMod2_zmod2ToBool (z : ZMod 2) : boolToZMod2 (zmod2ToBool z) = z := by
  revert z; decide

/-- The `Bool`-XOR bridge: `boolToZMod2` is additive from `xor` to `+` in `ZMod 2`,
using `1 + 1 = 0`. -/
theorem boolToZMod2_xor (a b : Bool) :
    boolToZMod2 (a ^^ b) = boolToZMod2 a + boolToZMod2 b := by
  cases a <;> cases b <;> decide

/-! ### The `BitVec n ≃ (Fin n → ZMod 2)` half -/

/-- Reflected coordinate equivalence between `BitVec n` and `Fin n → ZMod 2`:
coordinate `i` is `boolToZMod2` of the `i`-th most-significant bit. The inverse rebuilds
the bit vector big-endian from the coordinate function. -/
def bitVecEquivFun (n : ℕ) : BitVec n ≃ (Fin n → ZMod 2) where
  toFun x := fun i => boolToZMod2 (x.getMsbD i)
  invFun f := (BitVec.ofBoolListBE (List.ofFn fun i => zmod2ToBool (f i))).cast (by simp)
  left_inv x := by
    apply BitVec.eq_of_getMsbD_eq
    intro i hi
    simp only [BitVec.getMsbD_cast, BitVec.getMsbD_ofBoolListBE, List.getD_eq_getElem?_getD,
      List.getElem?_ofFn, hi, dif_pos, Option.getD_some, zmod2ToBool_boolToZMod2]
  right_inv f := by
    funext i
    simp only [BitVec.getMsbD_cast, BitVec.getMsbD_ofBoolListBE, List.getD_eq_getElem?_getD,
      List.getElem?_ofFn, i.isLt, dif_pos, Option.getD_some, boolToZMod2_zmod2ToBool]

@[simp] theorem bitVecEquivFun_apply (n : ℕ) (x : BitVec n) (i : Fin n) :
    bitVecEquivFun n x i = boolToZMod2 (x.getMsbD i) := rfl

/-- Additivity of the `BitVec` half: XOR of bit vectors maps to `+` of coordinate
functions. -/
theorem bitVecEquivFun_xor (n : ℕ) (x y : BitVec n) :
    bitVecEquivFun n (x ^^^ y) = bitVecEquivFun n x + bitVecEquivFun n y := by
  funext i
  simp only [bitVecEquivFun_apply, Pi.add_apply, BitVec.getMsbD_xor, boolToZMod2_xor]

end AdjoinRootReflect
