/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.KEM.IncrementalKEM.Derandomized
public import SecureMessaging.SCKA.MLKEMBraid.Basic

/-!
# SPQR parameters

An SPQR parameter set `P : Parameters m` consists of an incremental KEM with explicit coins
`P.det`, an epoch-key derivation `kdfOK`, a tag space, four erasure-coded payloads, and a
stream decoder for each payload.
`Parameters.toBraid` gives the ML-KEM Braid parameters with the same algorithms, for comparison
with the ML-KEM Braid transition system.

The KEM operations `generate`, `encaps1`, `encaps2`, `decaps`, and `ekMatchesHeader` run the
algorithms of `P.det`; `generate` and `encaps1` first draw their coins with its samplers, and
`generateRleak` and `encaps1Rleak` run the same computations and also return those coins.
-/

@[expose] public section

universe u

namespace SPQR

/-- Parameters of SPQR: an incremental KEM with explicit coins, epoch-key derivation, and
four erasure-coded payload streams with their decoders. -/
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
  /-- Incremental KEM with explicit coins. -/
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
  /-- Header-stream decoder. -/
  decHdr : ErasureCodePayload.Streaming.StreamDecoder (det.PKheader × Mac) Sym
  /-- Encapsulation-key-vector-stream decoder. -/
  decEk : ErasureCodePayload.Streaming.StreamDecoder det.PKvector Sym
  /-- `ct₁`-stream decoder. -/
  decCt1 : ErasureCodePayload.Streaming.StreamDecoder det.C₁ Sym
  /-- `ct₂`-stream decoder. -/
  decCt2 : ErasureCodePayload.Streaming.StreamDecoder (det.C₂ × Mac) Sym
-- ANCHOR_END: SPQR_Parameters

/-- The Braid parameters induced by the SPQR algorithms and payload streams. -/
abbrev Parameters.toBraid {m : Type → Type u} [Monad m] (P : Parameters m) :
    Braid.Parameters m where
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
  decHdr := P.decHdr
  decEk := P.decEk
  decCt1 := P.decCt1
  decCt2 := P.decCt2

namespace Parameters

variable {m : Type → Type u} [Monad m] (P : Parameters m)

-- ANCHOR: SPQR_kemOperations
/-- Draws key-generation coins and generates a key pair from them. -/
def generate : m (P.PK × P.SK) := do
  let r ← P.det.sampleKeygen
  pure (P.det.keygenDet r)

/-- `generate`, also returning the drawn coins. -/
def generateRleak : m ((P.PK × P.SK) × P.det.KeygenRand) := do
  let r ← P.det.sampleKeygen
  pure (P.det.keygenDet r, r)

/-- Draws first-stage coins and runs the first encapsulation stage on a header. -/
def encaps1 (hdr : P.det.PKheader) : m (P.det.St × P.det.C₁ × P.K) := do
  let r ← P.det.sampleEncaps1
  pure (P.det.encaps1Det hdr r)

/-- `encaps1`, also returning the drawn coins. -/
def encaps1Rleak (hdr : P.det.PKheader) :
    m ((P.det.St × P.det.C₁ × P.K) × P.det.Encaps1Rand) := do
  let r ← P.det.sampleEncaps1
  pure (P.det.encaps1Det hdr r, r)

/-- The second encapsulation stage on the vector `ek` and the first-stage state `es`; the header
is an argument of the generic second stage. -/
def encaps2 (ek : P.det.PKvector) (es : P.det.St) (hdr : P.det.PKheader) : P.det.C₂ :=
  P.det.encaps2Det es hdr ek

/-- Decapsulates the ciphertext with components `ct1` and `ct2`. -/
def decaps (dk : P.SK) (ct1 : P.det.C₁) (ct2 : P.det.C₂) : Option P.K :=
  P.det.decapsDet dk (P.det.splitC.symm (ct1, ct2))

/-- Whether the vector `ek` and the header form a public key. -/
def ekMatchesHeader (ek : P.det.PKvector) (hdr : P.det.PKheader) : Bool :=
  P.det.validPK hdr ek
-- ANCHOR_END: SPQR_kemOperations

end Parameters

end SPQR
