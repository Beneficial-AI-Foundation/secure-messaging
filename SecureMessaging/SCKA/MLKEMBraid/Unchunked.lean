/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.IncrementalKEM.Defs
import SecureMessaging.SCKA.MLKEMBraid.Authenticator
import ToVCVio.CryptoFoundations.KeyEncapMech

/-!
# Unchunked ML-KEM Braid core

Typed role states and transitions for the unchunked `send_ek` and `send_ct` procedures of
Signal's [SparsePostQuantumRatchet](https://github.com/signalapp/SparsePostQuantumRatchet),
implementing the cryptographic operations of
[ML-KEM Braid, §§2.1–2.4](https://signal.org/docs/specifications/mlkembraid/) before
transport fragmentation.
-/

open KEMScheme

universe u

namespace MLKEMBraid

variable {m : Type → Type u} [Monad m] {K PK SK C : Type} {kem : KEMScheme m K PK SK C}

/-- Post-KEM epoch-key derivation `KDF_OK` from a shared secret and an epoch. -/
-- ANCHOR: EpochKeyDerivation
abbrev EpochKeyDerivation (K EpochKey : Type) : Type := K → ℕ → EpochKey
-- ANCHOR_END: EpochKeyDerivation

/-! ## Role states -/

namespace EkSender

/-- Initial state of the encapsulation-key sender. -/
structure Start (AuthState : Type) where
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
structure VectorSent (inc : kem.IncrementalStructure) (AuthState : Type) where
  /-- The epoch in progress. -/
  ep : ℕ
  /-- Authenticator state entering the epoch. -/
  authSt : AuthState
  /-- The decapsulation key held for this epoch. -/
  sk : SK

/-- State after receiving the first ciphertext component. -/
structure AwaitingCt2 (inc : kem.IncrementalStructure) (AuthState : Type) where
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

/-- Initial state of the ciphertext sender. -/
structure Start (AuthState : Type) where
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

/-- State after validating the encapsulation-key vector. -/
structure VectorReceived (inc : kem.IncrementalStructure) (AuthState : Type) where
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

/-- Generate a KEM key pair and return its authenticated header and the successor state. -/
-- ANCHOR: EkSender_sendHeader
def sendHeader (inc : kem.IncrementalStructure)
    (auth : RatchetedAuthenticator InitKey EpochKey AuthState inc.PKheader (inc.C₁ × inc.C₂) Mac)
    (st : Start AuthState) : m ((inc.PKheader × Mac) × HeaderSent inc AuthState) := do
  let (pk, sk) ← kem.keygen
  let hdr := inc.toHeader pk
  pure ((hdr, auth.macHeader st.authSt st.ep hdr), ⟨st.ep, st.authSt, pk, sk⟩)
-- ANCHOR_END: EkSender_sendHeader

/-- Return the vector component of the stored encapsulation key and the successor state. -/
-- ANCHOR: EkSender_sendVector
def sendVector (inc : kem.IncrementalStructure) (st : HeaderSent inc AuthState) :
    inc.PKvector × VectorSent inc AuthState :=
  (inc.toVector st.pk, ⟨st.ep, st.authSt, st.sk⟩)
-- ANCHOR_END: EkSender_sendVector

/-- Store the first ciphertext component. -/
-- ANCHOR: EkSender_recvCt1
def recvCt1 (inc : kem.IncrementalStructure) (st : VectorSent inc AuthState)
    (c1 : inc.C₁) : AwaitingCt2 inc AuthState :=
  ⟨st.ep, st.authSt, st.sk, c1⟩
-- ANCHOR_END: EkSender_recvCt1

/-- Decapsulate `(c₁, c₂)`, derive the epoch key, update the authenticator, and verify the
ciphertext tag. On success, return the epoch key and the next ciphertext-sender state. -/
-- ANCHOR: EkSender_recvCt2
def recvCt2 (inc : kem.IncrementalStructure)
    (auth : RatchetedAuthenticator InitKey EpochKey AuthState inc.PKheader (inc.C₁ × inc.C₂) Mac)
    (deriveEpochKey : EpochKeyDerivation K EpochKey) (hDet : DeterministicDecaps kem)
    (st : AwaitingCt2 inc AuthState) (c2 : inc.C₂) (tag : Mac) :
    Option ((ℕ × EpochKey) × CtSender.Start AuthState) :=
  match hDet.decapsDet st.sk (inc.splitC.symm (st.c1, c2)) with
  | none => none
  | some k =>
    let ik := deriveEpochKey k st.ep
    let authSt' := auth.update st.authSt st.ep ik
    if auth.verifyCiphertext authSt' st.ep (st.c1, c2) tag then
      some ((st.ep, ik), ⟨st.ep + 1, authSt'⟩)
    else none
-- ANCHOR_END: EkSender_recvCt2

end EkSender

/-! ## Ciphertext sender transitions -/

namespace CtSender

/-- Verify the header tag and return the successor state on success. -/
-- ANCHOR: CtSender_recvHeader
def recvHeader (inc : kem.IncrementalStructure)
    (auth : RatchetedAuthenticator InitKey EpochKey AuthState inc.PKheader (inc.C₁ × inc.C₂) Mac)
    (st : Start AuthState) (hdr : inc.PKheader) (tag : Mac) :
    Option (HeaderReceived inc AuthState) :=
  if auth.verifyHeader st.authSt st.ep hdr tag then some ⟨st.ep, st.authSt, hdr⟩ else none
-- ANCHOR_END: CtSender_recvHeader

/-- Run the first encapsulation stage, derive the epoch key, update the authenticator, and
return the epoch key, `c₁`, and the successor state. -/
-- ANCHOR: CtSender_sendCt1
def sendCt1 (inc : kem.IncrementalStructure)
    (auth : RatchetedAuthenticator InitKey EpochKey AuthState inc.PKheader (inc.C₁ × inc.C₂) Mac)
    (deriveEpochKey : EpochKeyDerivation K EpochKey) (st : HeaderReceived inc AuthState) :
    m ((ℕ × EpochKey) × inc.C₁ × Ct1Sent inc AuthState) := do
  let (encapsSt, c1, k) ← inc.encaps1 st.hdr
  let ik := deriveEpochKey k st.ep
  pure ((st.ep, ik), c1, ⟨st.ep, auth.update st.authSt st.ep ik, st.hdr, encapsSt, c1⟩)
-- ANCHOR_END: CtSender_sendCt1

/-- Validate the vector against the stored header and return the successor state on success. -/
-- ANCHOR: CtSender_recvVector
def recvVector (inc : kem.IncrementalStructure) (st : Ct1Sent inc AuthState)
    (vec : inc.PKvector) : Option (VectorReceived inc AuthState) :=
  if inc.validPK st.hdr vec then
    some ⟨st.ep, st.authSt, st.hdr, st.encapsSt, st.c1, vec⟩
  else none
-- ANCHOR_END: CtSender_recvVector

/-- Run the second encapsulation stage and return `c₂`, the tag on `(c₁, c₂)`, and the
successor state. -/
-- ANCHOR: CtSender_sendCt2
def sendCt2 (inc : kem.IncrementalStructure)
    (auth : RatchetedAuthenticator InitKey EpochKey AuthState inc.PKheader (inc.C₁ × inc.C₂) Mac)
    (st : VectorReceived inc AuthState) : m ((inc.C₂ × Mac) × Ct2Sent AuthState) := do
  let c2 ← inc.encaps2 st.encapsSt st.hdr st.vec
  pure ((c2, auth.macCiphertext st.authSt st.ep (st.c1, c2)), ⟨st.ep, st.authSt⟩)
-- ANCHOR_END: CtSender_sendCt2

/-- Return the next encapsulation-key-sender state exactly when `t` is the successor epoch. -/
-- ANCHOR: CtSender_recvNextEpoch
def recvNextEpoch (st : Ct2Sent AuthState) (t : ℕ) : Option (EkSender.Start AuthState) :=
  if t = st.ep + 1 then some ⟨st.ep + 1, st.authSt⟩ else none
-- ANCHOR_END: CtSender_recvNextEpoch

end CtSender

end MLKEMBraid
