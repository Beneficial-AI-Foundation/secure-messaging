/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.IncrementalKEM.Derandomized
import SecureMessaging.SCKA.MLKEMBraid.Basic

/-!
# SPQR parameters

SPQR draws coins for deterministic incremental KEM blocks. The parameters also supply
an epoch-key derivation and four erasure-coded payload streams. `Parameters.toBraid` packages
these same algorithms for comparison with the ML-KEM Braid transition system.
-/

universe u

namespace SPQR

/-- Parameters of SPQR: an incremental KEM with explicit coins, epoch-key derivation, and
four erasure-coded payload streams. -/
-- ANCHOR: SPQR_Parameters
structure Parameters (m : Type → Type u) [Monad m] where
  /-- KEM shared secret. -/
  K : Type
  /-- Encapsulation key. -/
  PK : Type
  /-- Decapsulation key. -/
  SK : Type
  /-- Ciphertext. -/
  C : Type
  /-- Deterministic incremental KEM blocks and their coin samplers. -/
  det : KEMScheme.IncrementalKEMDet m K PK SK C
  /-- Epoch key output by `KDF_OK`. -/
  EpochKey : Type
  /-- MAC tag. -/
  Mac : Type
  /-- Erasure-code symbol alphabet, shared by the four streams. -/
  Sym : Type
  /-- `KDF_OK(shared_secret, epoch)`. -/
  kdfOK : K → ℕ → EpochKey
  /-- Header stream, recovering `header ‖ mac`. -/
  ecpHdr : ErasureCodePayload (det.PKheader × Mac) Sym
  /-- Encapsulation-key-vector stream. -/
  ecpEk : ErasureCodePayload det.PKvector Sym
  /-- `ct₁` stream. -/
  ecpCt1 : ErasureCodePayload det.C₁ Sym
  /-- `ct₂` stream, recovering `ct₂ ‖ mac`. -/
  ecpCt2 : ErasureCodePayload (det.C₂ × Mac) Sym
-- ANCHOR_END: SPQR_Parameters

/-- The Braid parameters induced by the SPQR algorithms and payload streams. -/
abbrev Parameters.toBraid {m : Type → Type u} [Monad m] (P : Parameters m) :
    MLKEMBraid.Parameters m where
  K := P.K
  PK := P.PK
  SK := P.SK
  C := P.C
  kem := P.det.toKEM
  inc := P.det.toIncremental
  hDet := P.det.toDetDecaps
  hEnc2 := P.det.toDetEncaps2
  EpochKey := P.EpochKey
  Mac := P.Mac
  Sym := P.Sym
  kdfOK := P.kdfOK
  ecpHdr := P.ecpHdr
  ecpEk := P.ecpEk
  ecpCt1 := P.ecpCt1
  ecpCt2 := P.ecpCt2

end SPQR
