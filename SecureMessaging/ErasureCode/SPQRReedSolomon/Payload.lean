/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.ErasureCode.SPQRReedSolomon.Construction
public import Mathlib.Data.FinEnum
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Byte blocks over the abstract SPQR field

Pairs are little-endian indices in the existing field enumeration. This reversible mathematical
representation does not identify that enumeration with SPQR's runtime `u16` representation.
-/

public section

namespace ErasureCode.SPQRReedSolomon

private noncomputable def bytePairEquiv : (UInt8 × UInt8) ≃ GF16 :=
  (Equiv.prodComm UInt8 UInt8).trans
    (((FinEnum.equiv : UInt8 ≃ Fin 256).prodCongr
      (FinEnum.equiv : UInt8 ≃ Fin 256)).trans
      (finProdFinEquiv.trans spqrEvaluationPoints))

/-- Group bytes `32*i + 2*j` and `32*i + 2*j + 1` into coordinate `j` of chunk `i`.
The inverse restores those same bytes in the same order. -/
noncomputable def byteBlocksEquiv (k : ℕ) :
    Vector UInt8 (32 * k) ≃ (Fin k → Chunk GF16) :=
  let vectorFn : Vector UInt8 (32 * k) ≃ (Fin (32 * k) → UInt8) :=
    { toFun := fun v i => v[i.val]
      invFun := Vector.ofFn
      left_inv := by intro v; exact Vector.ofFn_getElem
      right_inv := by intro f; funext i; simp }
  let positions : (Fin k × (Fin 16 × Fin 2)) ≃ Fin (32 * k) :=
    ((Equiv.refl (Fin k)).prodCongr finProdFinEquiv).trans
      (finProdFinEquiv.trans (finCongr (Nat.mul_comm k 32)))
  vectorFn.trans <|
    (Equiv.arrowCongr positions.symm (Equiv.refl UInt8)).trans <|
      (Equiv.curry (Fin k) (Fin 16 × Fin 2) UInt8).trans <|
        Equiv.arrowCongr (Equiv.refl (Fin k)) <|
          (Equiv.curry (Fin 16) (Fin 2) UInt8).trans <|
            Equiv.arrowCongr (Equiv.refl (Fin 16)) <|
              (finTwoArrowEquiv UInt8).trans bytePairEquiv

end ErasureCode.SPQRReedSolomon
