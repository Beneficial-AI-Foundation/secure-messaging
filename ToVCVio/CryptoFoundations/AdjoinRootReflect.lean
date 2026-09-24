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
# Bit vectors as elements of `AdjoinRoot p`

For monic `p : (ZMod 2)[X]` of degree `n`, write `α = root p`. `reflect hp` is the bijection

```text
φ : {0,1}ⁿ ≃ F₂[X]/(p)
φ(b₀ … bₙ₋₁) = b₀ + b₁α + ⋯ + bₙ₋₁αⁿ⁻¹
```

with `reflect_apply` giving this expansion and `reflect_xor` proving `φ(x ⊕ y) = φ(x) + φ(y)`.
Irreducibility is not required.

The leftmost bit is the constant coefficient. This is the bit order NIST fixes for GHASH, so GCM's
`BitVec 128` constants transport without a reversal.

`reflect` is a plain `Equiv` with a separate additivity lemma rather than a `≃ₗ[ZMod 2]`, because
Mathlib's `AddCommGroup (BitVec n)` is arithmetic `+`, not XOR.
-/

open Polynomial

namespace ToVCVio.AdjoinRootReflect

/-! ### `Bool` ↔ `ZMod 2` bridge -/

/-- Send `true ↦ 1`, `false ↦ 0` in `ZMod 2`. -/
def boolToZMod2 : Bool → ZMod 2 := fun b => if b then 1 else 0

@[simp] theorem boolToZMod2_true : boolToZMod2 true = 1 := rfl

@[simp] theorem boolToZMod2_false : boolToZMod2 false = 0 := rfl

/-- Send `0 ↦ false`, `1 ↦ true`, the inverse of `boolToZMod2`. -/
def zmod2ToBool : ZMod 2 → Bool := fun z => decide (z ≠ 0)

@[simp] theorem zmod2ToBool_boolToZMod2 (b : Bool) : zmod2ToBool (boolToZMod2 b) = b := by
  cases b <;> decide

@[simp] theorem boolToZMod2_zmod2ToBool (z : ZMod 2) : boolToZMod2 (zmod2ToBool z) = z := by
  revert z; decide

theorem boolToZMod2_xor (a b : Bool) :
    boolToZMod2 (a ^^ b) = boolToZMod2 a + boolToZMod2 b := by
  cases a <;> cases b <;> decide

/-! ### The `BitVec n ≃ (Fin n → ZMod 2)` half -/

/-- `BitVec n ≃ (Fin n → ZMod 2)`, coordinate `i` being the `i`-th most-significant bit. -/
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

theorem bitVecEquivFun_xor (n : ℕ) (x y : BitVec n) :
    bitVecEquivFun n (x ^^^ y) = bitVecEquivFun n x + bitVecEquivFun n y := by
  funext i
  simp only [bitVecEquivFun_apply, Pi.add_apply, BitVec.getMsbD_xor, boolToZMod2_xor]

/-! ### The reflected equivalence for a monic polynomial -/

/-- For monic `p` of degree `n` and `α = root p`, `reflect hp` is the bijection
`BitVec n ≃ AdjoinRoot p` sending the bits `(b₀, …, bₙ₋₁)` to `b₀ + b₁α + ⋯ + bₙ₋₁αⁿ⁻¹`, where
`b₀` is the most significant bit. -/
noncomputable def reflect {p : (ZMod 2)[X]} (hp : p.Monic) :
    BitVec p.natDegree ≃ AdjoinRoot p :=
  (bitVecEquivFun p.natDegree).trans
    ((AdjoinRoot.powerBasis' hp).basis.equivFun.symm.toEquiv)

theorem reflect_xor {p : (ZMod 2)[X]} (hp : p.Monic) (x y : BitVec p.natDegree) :
    reflect hp (x ^^^ y) = reflect hp x + reflect hp y := by
  -- Unfold `reflect` to the `AdjoinRoot`-side linear equiv (defeq through the
  -- `PowerBasis.dim = natDegree` gap), then use linearity.
  change (AdjoinRoot.powerBasis' hp).basis.equivFun.symm (bitVecEquivFun p.natDegree (x ^^^ y))
     = (AdjoinRoot.powerBasis' hp).basis.equivFun.symm (bitVecEquivFun p.natDegree x)
     + (AdjoinRoot.powerBasis' hp).basis.equivFun.symm (bitVecEquivFun p.natDegree y)
  rw [bitVecEquivFun_xor]
  exact map_add _ _ _

theorem reflect_apply {p : (ZMod 2)[X]} (hp : p.Monic) (x : BitVec p.natDegree) :
    reflect hp x
      = ∑ i : Fin p.natDegree, boolToZMod2 (x.getMsbD (i : ℕ)) • AdjoinRoot.root p ^ (i : ℕ) := by
  -- Expand the power basis at a coordinate function indexed by `powerBasis'.dim`, not by
  -- `p.natDegree`: the two are defeq but only the former keeps the statement type-correct
  -- at the transparency `rw` checks its motive under. `exact` crosses the gap.
  have key : ∀ c : Fin (AdjoinRoot.powerBasis' hp).dim → ZMod 2,
      (AdjoinRoot.powerBasis' hp).basis.equivFun.symm c
        = ∑ i, c i • AdjoinRoot.root p ^ (i : ℕ) := by
    intro c
    rw [Module.Basis.equivFun_symm_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [(AdjoinRoot.powerBasis' hp).basis_eq_pow i, AdjoinRoot.powerBasis'_gen]
  exact key _

end ToVCVio.AdjoinRootReflect
