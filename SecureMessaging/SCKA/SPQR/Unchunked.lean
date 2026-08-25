/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.IncrementalKEM.Defs
import SecureMessaging.SCKA.MLKEMBraid.Authenticator
import ToVCVio.CryptoFoundations.KeyEncapMech

/-!
# Unchunked SPQR core

Typed role states and transitions for the unchunked `send_ek` and `send_ct` procedures of
Signal's [SparsePostQuantumRatchet](https://github.com/signalapp/SparsePostQuantumRatchet)
(`src/v1/unchunked/`), before transport fragmentation.

The ratcheted authenticator interface is the one specified for ML-KEM Braid
internal authentication; SPQR takes it as a parameter.
-/

open KEMScheme

universe u

namespace SPQR

variable {m : Type → Type u} [Monad m] {K PK SK C : Type} {kem : KEMScheme m K PK SK C}

/-- Post-KEM epoch-key derivation `KDF_OK` from a shared secret and an epoch. -/
-- ANCHOR: EpochKeyDerivation
abbrev EpochKeyDerivation (K EpochKey : Type) : Type := K → ℕ → EpochKey
-- ANCHOR_END: EpochKeyDerivation

/-! ## Role states -/

namespace EkSender

/-- State before sampling an encapsulation key. -/
structure KeysUnsampled (AuthState : Type) where
  /-- The epoch in progress. -/
  ep : ℕ
  /-- Authenticator state entering the epoch. -/
  authSt : AuthState

/-- State after sending the authenticated encapsulation-key header. -/
structure HeaderSent (inc : kem.IncrementalStructure) (AuthState : Type) where
  /-- The epoch in progress. -/
  ep : ℕ
  /-- Authenticator state entering the epoch. -/
  authSt : AuthState
  /-- The sampled encapsulation key. -/
  pk : PK
  /-- The decapsulation key held for this epoch. -/
  sk : SK

/-- State after sending the encapsulation-key vector. -/
structure EkSent (inc : kem.IncrementalStructure) (AuthState : Type) where
  /-- The epoch in progress. -/
  ep : ℕ
  /-- Authenticator state entering the epoch. -/
  authSt : AuthState
  /-- The decapsulation key held for this epoch. -/
  sk : SK

/-- State after sending the encapsulation key and receiving the first ciphertext component. -/
structure EkSentCt1Received (inc : kem.IncrementalStructure) (AuthState : Type) where
  /-- The epoch in progress. -/
  ep : ℕ
  /-- Authenticator state entering the epoch. -/
  authSt : AuthState
  /-- The decapsulation key held for this epoch. -/
  sk : SK
  /-- The received first ciphertext component. -/
  c1 : inc.C₁

end EkSender

namespace CtSender

/-- State before receiving an encapsulation-key header. -/
structure NoHeaderReceived (AuthState : Type) where
  /-- The epoch in progress. -/
  ep : ℕ
  /-- Authenticator state entering the epoch. -/
  authSt : AuthState

/-- State after receiving an authenticated encapsulation-key header. -/
structure HeaderReceived (inc : kem.IncrementalStructure) (AuthState : Type) where
  /-- The epoch in progress. -/
  ep : ℕ
  /-- Authenticator state entering the epoch. -/
  authSt : AuthState
  /-- Stored encapsulation-key header. -/
  hdr : inc.PKheader

/-- State after deriving the epoch key and sending the first ciphertext component. -/
structure Ct1Sent (inc : kem.IncrementalStructure) (AuthState : Type) where
  /-- The epoch in progress. -/
  ep : ℕ
  /-- Authenticator state after the update with this epoch's key. -/
  authSt : AuthState
  /-- Stored encapsulation-key header. -/
  hdr : inc.PKheader
  /-- The encapsulation state carried from the first stage to the second. -/
  encapsSt : inc.St
  /-- The first ciphertext component, kept for the ciphertext tag. -/
  c1 : inc.C₁

/-- State after sending the first ciphertext component and validating the encapsulation key. -/
structure Ct1SentEkReceived (inc : kem.IncrementalStructure) (AuthState : Type) where
  /-- The epoch in progress. -/
  ep : ℕ
  /-- Authenticator state after the update with this epoch's key. -/
  authSt : AuthState
  /-- Stored encapsulation-key header. -/
  hdr : inc.PKheader
  /-- The encapsulation state carried from the first stage to the second. -/
  encapsSt : inc.St
  /-- The first ciphertext component, kept for the ciphertext tag. -/
  c1 : inc.C₁
  /-- Stored encapsulation-key vector. -/
  vec : inc.PKvector

/-- State after sending the second ciphertext component and its tag. -/
structure Ct2Sent (AuthState : Type) where
  /-- The epoch in progress. -/
  ep : ℕ
  /-- Authenticator state after the update with this epoch's key. -/
  authSt : AuthState

end CtSender

variable {InitKey EpochKey AuthState Mac : Type}

/-! ## Encapsulation-key sender transitions -/

namespace EkSender

-- ANCHOR: EkSender_sendHeader
/-- Generate a KEM key pair and return the successor state, header, and tag. -/
def sendHeader (inc : kem.IncrementalStructure)
    (auth : RatchetedAuthenticator InitKey EpochKey AuthState inc.PKheader (inc.C₁ × inc.C₂) Mac)
    (st : KeysUnsampled AuthState) : m (HeaderSent inc AuthState × inc.PKheader × Mac) := do
  let (pk, sk) ← kem.keygen
  let hdr := inc.toHeader pk
  pure (⟨st.ep, st.authSt, pk, sk⟩, hdr, auth.macHeader st.authSt st.ep hdr)
-- ANCHOR_END: EkSender_sendHeader

-- ANCHOR: EkSender_sendVector
/-- Return the successor state and the vector component of the stored encapsulation key. -/
def sendVector (inc : kem.IncrementalStructure) (st : HeaderSent inc AuthState) :
    EkSent inc AuthState × inc.PKvector :=
  (⟨st.ep, st.authSt, st.sk⟩, inc.toVector st.pk)
-- ANCHOR_END: EkSender_sendVector

-- ANCHOR: EkSender_recvCt1
/-- Store the first ciphertext component. -/
def recvCt1 (inc : kem.IncrementalStructure) (st : EkSent inc AuthState)
    (c1 : inc.C₁) : EkSentCt1Received inc AuthState :=
  ⟨st.ep, st.authSt, st.sk, c1⟩
-- ANCHOR_END: EkSender_recvCt1

-- ANCHOR: EkSender_recvCt2
/-- Decapsulate and authenticate the ciphertext, returning the next role state and epoch key. -/
def recvCt2 (inc : kem.IncrementalStructure)
    (auth : RatchetedAuthenticator InitKey EpochKey AuthState inc.PKheader (inc.C₁ × inc.C₂) Mac)
    (deriveEpochKey : EpochKeyDerivation K EpochKey) (hDet : DeterministicDecaps kem)
    (st : EkSentCt1Received inc AuthState) (c2 : inc.C₂) (tag : Mac) :
    Option (CtSender.NoHeaderReceived AuthState × (ℕ × EpochKey)) :=
  match hDet.decapsDet st.sk (inc.splitC.symm (st.c1, c2)) with
  | none => none
  | some k =>
    let ik := deriveEpochKey k st.ep
    let authSt' := auth.update st.authSt st.ep ik
    if auth.verifyCiphertext authSt' st.ep (st.c1, c2) tag then
      some (⟨st.ep + 1, authSt'⟩, (st.ep, ik))
    else none
-- ANCHOR_END: EkSender_recvCt2

end EkSender

/-! ## Ciphertext sender transitions -/

namespace CtSender

-- ANCHOR: CtSender_recvHeader
/-- Verify the header tag and return the successor state on success. -/
def recvHeader (inc : kem.IncrementalStructure)
    (auth : RatchetedAuthenticator InitKey EpochKey AuthState inc.PKheader (inc.C₁ × inc.C₂) Mac)
    (st : NoHeaderReceived AuthState) (hdr : inc.PKheader) (tag : Mac) :
    Option (HeaderReceived inc AuthState) :=
  if auth.verifyHeader st.authSt st.ep hdr tag then some ⟨st.ep, st.authSt, hdr⟩ else none
-- ANCHOR_END: CtSender_recvHeader

-- ANCHOR: CtSender_sendCt1
/-- Run encapsulation stage one and return the successor state, ciphertext, and epoch key. -/
def sendCt1 (inc : kem.IncrementalStructure)
    (auth : RatchetedAuthenticator InitKey EpochKey AuthState inc.PKheader (inc.C₁ × inc.C₂) Mac)
    (deriveEpochKey : EpochKeyDerivation K EpochKey) (st : HeaderReceived inc AuthState) :
    m (Ct1Sent inc AuthState × inc.C₁ × (ℕ × EpochKey)) := do
  let (encapsSt, c1, k) ← inc.encaps1 st.hdr
  let ik := deriveEpochKey k st.ep
  pure (⟨st.ep, auth.update st.authSt st.ep ik, st.hdr, encapsSt, c1⟩, c1, (st.ep, ik))
-- ANCHOR_END: CtSender_sendCt1

-- ANCHOR: CtSender_recvVector
/-- Validate the encapsulation-key vector and return the successor state on success. -/
def recvVector (inc : kem.IncrementalStructure) (st : Ct1Sent inc AuthState)
    (vec : inc.PKvector) : Option (Ct1SentEkReceived inc AuthState) :=
  if inc.validPK st.hdr vec then
    some ⟨st.ep, st.authSt, st.hdr, st.encapsSt, st.c1, vec⟩
  else none
-- ANCHOR_END: CtSender_recvVector

-- ANCHOR: CtSender_sendCt2
/-- Run encapsulation stage two and return the successor state, ciphertext, and tag. -/
def sendCt2 (inc : kem.IncrementalStructure)
    (auth : RatchetedAuthenticator InitKey EpochKey AuthState inc.PKheader (inc.C₁ × inc.C₂) Mac)
    (st : Ct1SentEkReceived inc AuthState) : m (Ct2Sent AuthState × inc.C₂ × Mac) := do
  let c2 ← inc.encaps2 st.encapsSt st.hdr st.vec
  pure (⟨st.ep, st.authSt⟩, c2, auth.macCiphertext st.authSt st.ep (st.c1, c2))
-- ANCHOR_END: CtSender_sendCt2

-- ANCHOR: CtSender_recvNextEpoch
/-- Return the encapsulation-key-sender state exactly when `t` is the successor epoch. -/
def recvNextEpoch (st : Ct2Sent AuthState) (t : ℕ) : Option (EkSender.KeysUnsampled AuthState) :=
  if t = st.ep + 1 then some ⟨st.ep + 1, st.authSt⟩ else none
-- ANCHOR_END: CtSender_recvNextEpoch

end CtSender

end SPQR
