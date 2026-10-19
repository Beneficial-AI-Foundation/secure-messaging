/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.IncrementalKEM.FromBoundedMLKEM
import SecureMessaging.ErasureCode.SPQRReedSolomon.Payload
import SecureMessaging.ErasureCode.SPQRReedSolomon.Correctness
import SecureMessaging.ErasureCode.Payload
import SecureMessaging.SCKA.MLKEMBraid.Construction

/-!
# Bounded ML-KEM Braid parameters

The four payloads use reversible byte representations and the existing abstract SPQR code.
Their roundtrips hold for every bounded payload, without canonical-encoding restrictions.
-/

namespace MLKEMBraid.Bounded

open ErasureCode.SPQRReedSolomon

/-- Concatenate the seed and hash, in that order, and restore the unique unit tag on reading. -/
def headerBytesEquiv :
    ((MLKEM.Seed32 × MLKEM.PublicKeyHash) × Unit) ≃ MLKEM.Bytes 64 :=
  let vectorFn (n : ℕ) : Vector UInt8 n ≃ (Fin n → UInt8) :=
    { toFun := fun v i => v[i.val]
      invFun := Vector.ofFn
      left_inv := by intro v; exact Vector.ofFn_getElem
      right_inv := by intro f; funext i; simp }
  (Equiv.prodPUnit _).trans <|
    ((vectorFn 32).prodCongr (vectorFn 32)).trans <|
      (Equiv.sumArrowEquivProdArrow (Fin 32) (Fin 32) UInt8).symm.trans <|
        (Equiv.arrowCongr finSumFinEquiv (Equiv.refl UInt8)).trans (vectorFn 64).symm

/-- The two-chunk header code. -/
noncomputable def headerPayload :
    ErasureCodePayload ((MLKEM.Seed32 × MLKEM.PublicKeyHash) × Unit) (Chunk GF16) :=
  ErasureCodePayload.ofEquiv (erasureCode 2 (by decide) (by decide))
    (headerBytesEquiv.trans (byteBlocksEquiv 2))

/-- The public vector occupies twelve chunks per module rank. -/
noncomputable def publicKeyPayload (p : MLKEM.ParameterSet) :
    ErasureCodePayload (MLKEM.Bytes (384 * (MLKEM.ParameterSet.params p).k)) (Chunk GF16) :=
  ErasureCodePayload.ofEquiv
    (erasureCode (12 * (MLKEM.ParameterSet.params p).k)
      (by cases p <;> decide) (by cases p <;> decide))
    ((Equiv.cast (congrArg (Vector UInt8)
      (by omega : 384 * (MLKEM.ParameterSet.params p).k =
        32 * (12 * (MLKEM.ParameterSet.params p).k)))).trans
      (byteBlocksEquiv (12 * (MLKEM.ParameterSet.params p).k)))

/-- The first ciphertext component uses `du*k` source chunks. -/
noncomputable def ct1Payload (p : MLKEM.ParameterSet) :
    ErasureCodePayload
      (MLKEM.Bytes
        (32 * (MLKEM.ParameterSet.params p).du * (MLKEM.ParameterSet.params p).k))
      (Chunk GF16) :=
  ErasureCodePayload.ofEquiv
    (erasureCode ((MLKEM.ParameterSet.params p).du * (MLKEM.ParameterSet.params p).k)
      (by cases p <;> decide) (by cases p <;> decide))
    ((Equiv.cast (congrArg (Vector UInt8)
      (Nat.mul_assoc 32 (MLKEM.ParameterSet.params p).du (MLKEM.ParameterSet.params p).k))).trans
      (byteBlocksEquiv
        ((MLKEM.ParameterSet.params p).du * (MLKEM.ParameterSet.params p).k)))

/-- The second ciphertext component uses `dv` chunks and a unique unit tag. -/
noncomputable def ct2Payload (p : MLKEM.ParameterSet) :
    ErasureCodePayload (MLKEM.Bytes (32 * (MLKEM.ParameterSet.params p).dv) × Unit)
      (Chunk GF16) :=
  ErasureCodePayload.ofEquiv
    (erasureCode (MLKEM.ParameterSet.params p).dv
      (by cases p <;> decide) (by cases p <;> decide))
    ((Equiv.prodPUnit _).trans (byteBlocksEquiv (MLKEM.ParameterSet.params p).dv))

/-- Each of the four payload codes has the existing SPQR reconstruction guarantee. -/
theorem payloads_correct (p : MLKEM.ParameterSet) :
    headerPayload.ec.Correct ∧ (publicKeyPayload p).ec.Correct ∧
      (ct1Payload p).ec.Correct ∧ (ct2Payload p).ec.Correct := by
  exact ⟨erasureCode_correct _ _ _, erasureCode_correct _ _ _,
    erasureCode_correct _ _ _, erasureCode_correct _ _ _⟩

/-- Assemble bounded ML-KEM with finite-symbol payloads, retaining the original key samplers. -/
noncomputable def parameters (p : MLKEM.ParameterSet) (ring : MLKEM.NTTRingOps)
    (prims : MLKEM.Primitives (MLKEM.ParameterSet.params p)
      (MLKEM.Concrete.concreteEncoding (MLKEM.ParameterSet.params p)))
    {EpochKey : Type} (kdfOK : MLKEM.SharedSecret → ℕ → EpochKey) :
    MLKEMBraid.Parameters ProbComp where
  K := MLKEM.SharedSecret
  PK := MLKEM.EncapsulationKey (MLKEM.ParameterSet.params p)
    (MLKEM.Bounded.encoding (MLKEM.ParameterSet.params p))
  SK := MLKEM.DecapsulationKey (MLKEM.ParameterSet.params p)
    (MLKEM.Bounded.encoding (MLKEM.ParameterSet.params p))
  C := MLKEM.Ciphertext (MLKEM.ParameterSet.params p)
    (MLKEM.Bounded.encoding (MLKEM.ParameterSet.params p))
  kem := MLKEM.Bounded.scheme p ring prims
  inc := MLKEM.incrementalStructure ring (MLKEM.Bounded.encoding (MLKEM.ParameterSet.params p))
    (MLKEM.Bounded.primitives (MLKEM.ParameterSet.params p) prims)
  hDet := MLKEM.incrementalDeterministicDecaps ring
    (MLKEM.Bounded.encoding (MLKEM.ParameterSet.params p))
    (MLKEM.Bounded.primitives (MLKEM.ParameterSet.params p) prims)
  hEnc2 := MLKEM.incrementalDeterministicEncaps2 ring
    (MLKEM.Bounded.encoding (MLKEM.ParameterSet.params p))
    (MLKEM.Bounded.primitives (MLKEM.ParameterSet.params p) prims)
  EpochKey := EpochKey
  Mac := Unit
  Sym := Chunk GF16
  kdfOK := kdfOK
  ecpHdr := headerPayload
  ecpEk := publicKeyPayload p
  ecpCt1 := ct1Payload p
  ecpCt2 := ct2Payload p

end MLKEMBraid.Bounded
