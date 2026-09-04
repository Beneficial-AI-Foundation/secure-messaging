/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.ErasureCode.SPQRReedSolomon.Construction
import SecureMessaging.SCKA.MLKEMBraid.Instances
import SecureMessaging.SCKA.SPQR.Construction

/-! # SPQR v1 instance

`v1Parameters` fixes the ML-KEM-768 witnesses of `MLKEM.mlkem768Scheme`, uses `Chunk GF16` symbols,
and supplies four SPQR Reed-Solomon codes. With 32-byte chunks, the 96-byte header and MAC payload
requires 3 chunks, the 1152-byte encapsulation-key vector requires 36, `ct₁` at 960 bytes requires
30, and the 160-byte `ct₂` and MAC payload requires 5.

`EpochKey`, `Mac`, `InitKey`, `AuthState`, `kdfOK`, the four serializer triples, `auth`, and
`sampleInitKey` remain parameters. `v1Parameters` applies `MLKEMBraid.mlkemBraidParameters` to the
ML-KEM witnesses and these four codes.
-/

open ErasureCode.SPQRReedSolomon (Chunk GF16 erasureCode)
open MLKEMBraid (SendRand)

namespace SPQR

/-- Incremental ML-KEM-768 over the witnesses of `MLKEM.mlkem768Scheme`. -/
-- ANCHOR: SPQR_v1Incremental
abbrev v1Incremental : MLKEM.mlkem768Scheme.IncrementalStructure :=
  MLKEM.mlkemIncremental .MLKEM768 MLKEM.Concrete.concreteNTTRingOps
    MLKEM.Concrete.mlkem768Primitives
-- ANCHOR_END: SPQR_v1Incremental

/-- The SPQR erasure code at threshold `k` with a caller-supplied payload layout. -/
-- ANCHOR: SPQR_v1ErasureCodePayload
noncomputable def v1ErasureCodePayload {M : Type} (k : ℕ) (hk : k ≤ 2 ^ 16) (hk_pos : 0 < k)
    (serialize : M → Fin k → Chunk GF16) (parse : (Fin k → Chunk GF16) → Option M)
    (parse_serialize : ∀ payload, parse (serialize payload) = some payload) :
    ErasureCodePayload M (Chunk GF16) :=
  { ec := erasureCode k hk hk_pos, serialize, parse, parse_serialize }
-- ANCHOR_END: SPQR_v1ErasureCodePayload

/-- SPQR v1 parameters at ML-KEM-768 with thresholds 3, 36, 30, and 5. -/
-- ANCHOR: SPQR_v1Parameters
noncomputable def v1Parameters {EpochKey Mac : Type}
    (kdfOK : MLKEM.SharedSecret → ℕ → EpochKey)
    (serializeHdr : v1Incremental.PKheader × Mac → Fin 3 → Chunk GF16)
    (parseHdr : (Fin 3 → Chunk GF16) → Option (v1Incremental.PKheader × Mac))
    (parseHdr_serializeHdr : ∀ payload, parseHdr (serializeHdr payload) = some payload)
    (serializeEk : v1Incremental.PKvector → Fin 36 → Chunk GF16)
    (parseEk : (Fin 36 → Chunk GF16) → Option v1Incremental.PKvector)
    (parseEk_serializeEk : ∀ payload, parseEk (serializeEk payload) = some payload)
    (serializeCt1 : v1Incremental.C₁ → Fin 30 → Chunk GF16)
    (parseCt1 : (Fin 30 → Chunk GF16) → Option v1Incremental.C₁)
    (parseCt1_serializeCt1 : ∀ payload, parseCt1 (serializeCt1 payload) = some payload)
    (serializeCt2 : v1Incremental.C₂ × Mac → Fin 5 → Chunk GF16)
    (parseCt2 : (Fin 5 → Chunk GF16) → Option (v1Incremental.C₂ × Mac))
    (parseCt2_serializeCt2 : ∀ payload, parseCt2 (serializeCt2 payload) = some payload) :
    MLKEMBraid.Parameters ProbComp :=
  MLKEMBraid.mlkemBraidParameters .MLKEM768 MLKEM.Concrete.concreteNTTRingOps
    MLKEM.Concrete.mlkem768Primitives kdfOK
    (v1ErasureCodePayload 3 (by norm_num) (by norm_num) serializeHdr parseHdr
      parseHdr_serializeHdr)
    (v1ErasureCodePayload 36 (by norm_num) (by norm_num) serializeEk parseEk
      parseEk_serializeEk)
    (v1ErasureCodePayload 30 (by norm_num) (by norm_num) serializeCt1 parseCt1
      parseCt1_serializeCt1)
    (v1ErasureCodePayload 5 (by norm_num) (by norm_num) serializeCt2 parseCt2
      parseCt2_serializeCt2)
-- ANCHOR_END: SPQR_v1Parameters

/-- The SPQR v1 SCKA scheme; the authenticator and initial-key sampler remain parameters. -/
-- ANCHOR: SPQR_v1Scheme
noncomputable def v1Scheme {InitKey AuthState EpochKey Mac : Type}
    (kdfOK : MLKEM.SharedSecret → ℕ → EpochKey)
    (serializeHdr : v1Incremental.PKheader × Mac → Fin 3 → Chunk GF16)
    (parseHdr : (Fin 3 → Chunk GF16) → Option (v1Incremental.PKheader × Mac))
    (parseHdr_serializeHdr : ∀ payload, parseHdr (serializeHdr payload) = some payload)
    (serializeEk : v1Incremental.PKvector → Fin 36 → Chunk GF16)
    (parseEk : (Fin 36 → Chunk GF16) → Option v1Incremental.PKvector)
    (parseEk_serializeEk : ∀ payload, parseEk (serializeEk payload) = some payload)
    (serializeCt1 : v1Incremental.C₁ → Fin 30 → Chunk GF16)
    (parseCt1 : (Fin 30 → Chunk GF16) → Option v1Incremental.C₁)
    (parseCt1_serializeCt1 : ∀ payload, parseCt1 (serializeCt1 payload) = some payload)
    (serializeCt2 : v1Incremental.C₂ × Mac → Fin 5 → Chunk GF16)
    (parseCt2 : (Fin 5 → Chunk GF16) → Option (v1Incremental.C₂ × Mac))
    (parseCt2_serializeCt2 : ∀ payload, parseCt2 (serializeCt2 payload) = some payload)
    (auth : RatchetedAuthenticator InitKey EpochKey AuthState
      v1Incremental.PKheader (v1Incremental.C₁ × v1Incremental.C₂) Mac)
    (sampleInitKey : ProbComp InitKey) :
    SCKAScheme ProbComp InitKey
      (Chunked.PartyState (v1Parameters kdfOK serializeHdr parseHdr parseHdr_serializeHdr
        serializeEk parseEk parseEk_serializeEk serializeCt1 parseCt1 parseCt1_serializeCt1
        serializeCt2 parseCt2 parseCt2_serializeCt2) AuthState)
      (Chunked.PartyState (v1Parameters kdfOK serializeHdr parseHdr parseHdr_serializeHdr
        serializeEk parseEk parseEk_serializeEk serializeCt1 parseCt1 parseCt1_serializeCt1
        serializeCt2 parseCt2 parseCt2_serializeCt2) AuthState)
      EpochKey (Chunked.Message (Chunk GF16))
      (SendRand (MLKEM.mlkemIncrementalRandLeak .MLKEM768 MLKEM.Concrete.concreteNTTRingOps
          MLKEM.Concrete.mlkem768Primitives).KeygenRand
        (MLKEM.mlkemIncrementalRandLeak .MLKEM768 MLKEM.Concrete.concreteNTTRingOps
          MLKEM.Concrete.mlkem768Primitives).Encaps1Rand)
-- ANCHOR_END: SPQR_v1Scheme
    := by
  letI : DecidableEq (v1Parameters kdfOK serializeHdr parseHdr parseHdr_serializeHdr
      serializeEk parseEk parseEk_serializeEk serializeCt1 parseCt1 parseCt1_serializeCt1
      serializeCt2 parseCt2 parseCt2_serializeCt2).Sym := by
    change DecidableEq (Chunk GF16)
    infer_instance
  exact scheme
    (v1Parameters kdfOK serializeHdr parseHdr parseHdr_serializeHdr serializeEk parseEk
      parseEk_serializeEk serializeCt1 parseCt1 parseCt1_serializeCt1 serializeCt2 parseCt2
      parseCt2_serializeCt2)
    auth
    (MLKEM.mlkemIncrementalRandLeak .MLKEM768 MLKEM.Concrete.concreteNTTRingOps
      MLKEM.Concrete.mlkem768Primitives)
    sampleInitKey

end SPQR
