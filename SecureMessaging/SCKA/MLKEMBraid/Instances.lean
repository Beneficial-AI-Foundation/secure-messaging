/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.IncrementalKEM.FromMLKEM
import SecureMessaging.SCKA.MLKEMBraid.Construction

/-!
# Concrete ML-KEM Braid adapter

This module supplies ML-KEM Braid's KEM parameters using incremental ML-KEM. Callers still
choose the epoch-key derivation, ratcheted authenticator, MAC and symbol types, four erasure
codes, and initial-key sampler.
-/

namespace MLKEMBraid

/-- Assemble the Braid parameters around concrete incremental ML-KEM. -/
-- ANCHOR: mlkemBraidParameters
def mlkemBraidParameters (p : MLKEM.ParameterSet) (ring : MLKEM.NTTRingOps)
    (prims : MLKEM.Primitives (MLKEM.ParameterSet.params p)
      (MLKEM.Concrete.concreteEncoding (MLKEM.ParameterSet.params p)))
    {EpochKey Mac Sym : Type} (kdfOK : MLKEM.SharedSecret → ℕ → EpochKey)
    (ecpHdr : ErasureCodePayload
      ((MLKEM.mlkemIncremental p ring prims).PKheader × Mac) Sym)
    (ecpEk : ErasureCodePayload (MLKEM.mlkemIncremental p ring prims).PKvector Sym)
    (ecpCt1 : ErasureCodePayload (MLKEM.mlkemIncremental p ring prims).C₁ Sym)
    (ecpCt2 : ErasureCodePayload
      ((MLKEM.mlkemIncremental p ring prims).C₂ × Mac) Sym) : Parameters ProbComp
-- ANCHOR_END: mlkemBraidParameters
    where
  K := MLKEM.SharedSecret
  PK := MLKEM.EncapsulationKey (MLKEM.ParameterSet.params p)
    (MLKEM.Concrete.concreteEncoding (MLKEM.ParameterSet.params p))
  SK := MLKEM.DecapsulationKey (MLKEM.ParameterSet.params p)
    (MLKEM.Concrete.concreteEncoding (MLKEM.ParameterSet.params p))
  C := MLKEM.Ciphertext (MLKEM.ParameterSet.params p)
    (MLKEM.Concrete.concreteEncoding (MLKEM.ParameterSet.params p))
  kem := MLKEM.mlkemScheme p ring prims
  inc := MLKEM.mlkemIncremental p ring prims
  hDet := MLKEM.mlkemDeterministicDecaps p ring prims
  hEnc2 := MLKEM.mlkemDeterministicEncaps2 p ring prims
  EpochKey := EpochKey
  Mac := Mac
  Sym := Sym
  kdfOK := kdfOK
  ecpHdr := ecpHdr
  ecpEk := ecpEk
  ecpCt1 := ecpCt1
  ecpCt2 := ecpCt2

/-- Instantiate the SCKA scheme with concrete incremental ML-KEM. -/
-- ANCHOR: mlkemBraidScheme
def mlkemBraidScheme (p : MLKEM.ParameterSet) (ring : MLKEM.NTTRingOps)
    (prims : MLKEM.Primitives (MLKEM.ParameterSet.params p)
      (MLKEM.Concrete.concreteEncoding (MLKEM.ParameterSet.params p)))
    {InitKey AuthState EpochKey Mac Sym : Type} [DecidableEq Sym]
    (kdfOK : MLKEM.SharedSecret → ℕ → EpochKey)
    (ecpHdr : ErasureCodePayload
      ((MLKEM.mlkemIncremental p ring prims).PKheader × Mac) Sym)
    (ecpEk : ErasureCodePayload (MLKEM.mlkemIncremental p ring prims).PKvector Sym)
    (ecpCt1 : ErasureCodePayload (MLKEM.mlkemIncremental p ring prims).C₁ Sym)
    (ecpCt2 : ErasureCodePayload
      ((MLKEM.mlkemIncremental p ring prims).C₂ × Mac) Sym)
    (auth : RatchetedAuthenticator InitKey EpochKey AuthState
      (MLKEM.mlkemIncremental p ring prims).PKheader
      ((MLKEM.mlkemIncremental p ring prims).C₁ ×
        (MLKEM.mlkemIncremental p ring prims).C₂) Mac)
    (sampleInitKey : ProbComp InitKey) :
    SCKAScheme ProbComp InitKey
      (State (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2) AuthState)
      (State (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2) AuthState)
      EpochKey (Message Sym)
      (SendRand (MLKEM.mlkemIncrementalRandLeak p ring prims).KeygenRand
        (MLKEM.mlkemIncrementalRandLeak p ring prims).Encaps1Rand)
-- ANCHOR_END: mlkemBraidScheme
    := by
  letI : DecidableEq
      (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2).Sym := by
    change DecidableEq Sym
    infer_instance
  exact scheme (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2) auth
    (MLKEM.mlkemIncrementalRandLeak p ring prims) sampleInitKey

end MLKEMBraid
