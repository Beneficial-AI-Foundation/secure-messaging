/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.SPQR.Params
public import SecureMessaging.SCKA.MLKEMBraid.Authenticator
public import ToVCVio.CryptoFoundations.KeyEncapMech

/-!
# Unchunked SPQR core

Typed role states and transitions for the unchunked `send_ek` and `send_ct` procedures of
Signal's [SparsePostQuantumRatchet](https://github.com/signalapp/SparsePostQuantumRatchet)
(`src/v1/unchunked/`), before transport fragmentation.

The ratcheted authenticator interface is the one specified for ML-KEM Braid
internal authentication; SPQR takes it as a parameter.
-/

@[expose] public section

open KEMScheme

universe u

namespace SPQR

variable {m : Type → Type u} [Monad m]

/-! ## Role states -/

namespace EkSender

/-- State before sampling an encapsulation key. -/
structure KeysUnsampled (AuthState : Type) where
  /-- The epoch in progress. -/
  ep : ℕ
  /-- Authenticator state entering the epoch. -/
  authSt : AuthState

/-- State after sending the authenticated encapsulation-key header. -/
structure HeaderSent (P : Parameters m) (AuthState : Type) where
  /-- The epoch in progress. -/
  ep : ℕ
  /-- Authenticator state entering the epoch. -/
  authSt : AuthState
  /-- The sampled encapsulation key. -/
  pk : P.PK
  /-- The decapsulation key held for this epoch. -/
  sk : P.SK

/-- State after sending the encapsulation-key vector. -/
structure EkSent (P : Parameters m) (AuthState : Type) where
  /-- The epoch in progress. -/
  ep : ℕ
  /-- Authenticator state entering the epoch. -/
  authSt : AuthState
  /-- The decapsulation key held for this epoch. -/
  sk : P.SK

/-- State after sending the encapsulation key and receiving the first ciphertext component. -/
structure EkSentCt1Received (P : Parameters m) (AuthState : Type) where
  /-- The epoch in progress. -/
  ep : ℕ
  /-- Authenticator state entering the epoch. -/
  authSt : AuthState
  /-- The decapsulation key held for this epoch. -/
  sk : P.SK
  /-- The received first ciphertext component. -/
  c1 : P.det.C₁

end EkSender

namespace CtSender

/-- State before receiving an encapsulation-key header. -/
structure NoHeaderReceived (AuthState : Type) where
  /-- The epoch in progress. -/
  ep : ℕ
  /-- Authenticator state entering the epoch. -/
  authSt : AuthState

/-- State after receiving an authenticated encapsulation-key header. -/
structure HeaderReceived (P : Parameters m) (AuthState : Type) where
  /-- The epoch in progress. -/
  ep : ℕ
  /-- Authenticator state entering the epoch. -/
  authSt : AuthState
  /-- Stored encapsulation-key header. -/
  hdr : P.det.PKheader

/-- State after deriving the epoch key and sending the first ciphertext component. -/
structure Ct1Sent (P : Parameters m) (AuthState : Type) where
  /-- The epoch in progress. -/
  ep : ℕ
  /-- Authenticator state after the update with this epoch's key. -/
  authSt : AuthState
  /-- Stored encapsulation-key header. -/
  hdr : P.det.PKheader
  /-- The encapsulation state carried from the first stage to the second. -/
  encapsSt : P.det.St
  /-- The first ciphertext component, kept for the ciphertext tag. -/
  c1 : P.det.C₁

/-- State after sending the first ciphertext component and validating the encapsulation key. -/
structure Ct1SentEkReceived (P : Parameters m) (AuthState : Type) where
  /-- The epoch in progress. -/
  ep : ℕ
  /-- Authenticator state after the update with this epoch's key. -/
  authSt : AuthState
  /-- Stored encapsulation-key header. -/
  hdr : P.det.PKheader
  /-- The encapsulation state carried from the first stage to the second. -/
  encapsSt : P.det.St
  /-- The first ciphertext component, kept for the ciphertext tag. -/
  c1 : P.det.C₁
  /-- Stored encapsulation-key vector `ek`. -/
  ek : P.det.PKvector

/-- State after sending the second ciphertext component and its tag. -/
structure Ct2Sent (AuthState : Type) where
  /-- The epoch in progress. -/
  ep : ℕ
  /-- Authenticator state after the update with this epoch's key. -/
  authSt : AuthState

end CtSender

variable {InitKey AuthState : Type}

/-! ## Encapsulation-key sender transitions -/

namespace EkSender

-- ANCHOR: EkSender_sendHeader
/-- Generate a key pair and return the successor state, the header, and its tag. -/
def sendHeader (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (st : KeysUnsampled AuthState) : m (HeaderSent P AuthState × P.det.PKheader × P.Mac) := do
  let (pk, sk) ← P.generate
  let hdr := P.det.toHeader pk
  pure (⟨st.ep, st.authSt, pk, sk⟩, hdr, auth.macHeader st.authSt st.ep hdr)
-- ANCHOR_END: EkSender_sendHeader

-- ANCHOR: EkSender_sendHeaderRleak
/-- `sendHeader` with `generate` replaced by `generateRleak`, also returning the drawn coins. -/
def sendHeaderRleak (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (st : KeysUnsampled AuthState) :
    m ((HeaderSent P AuthState × P.det.PKheader × P.Mac) × P.det.KeygenRand) := do
  let ((pk, sk), r) ← P.generateRleak
  let hdr := P.det.toHeader pk
  pure ((⟨st.ep, st.authSt, pk, sk⟩, hdr, auth.macHeader st.authSt st.ep hdr), r)
-- ANCHOR_END: EkSender_sendHeaderRleak

-- ANCHOR: EkSender_sendEk
/-- Return the successor state and the vector `ek` of the stored public key. -/
def sendEk (P : Parameters m) (st : HeaderSent P AuthState) :
    EkSent P AuthState × P.det.PKvector :=
  (⟨st.ep, st.authSt, st.sk⟩, P.det.toVector st.pk)
-- ANCHOR_END: EkSender_sendEk

-- ANCHOR: EkSender_recvCt1
/-- Store the first ciphertext component. -/
def recvCt1 (P : Parameters m) (st : EkSent P AuthState)
    (c1 : P.det.C₁) : EkSentCt1Received P AuthState :=
  ⟨st.ep, st.authSt, st.sk, c1⟩
-- ANCHOR_END: EkSender_recvCt1

-- ANCHOR: EkSender_recvCt2
/-- Decapsulate and authenticate the ciphertext, returning the next role state and epoch key. -/
def recvCt2 (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (st : EkSentCt1Received P AuthState) (c2 : P.det.C₂) (tag : P.Mac) :
    Option (CtSender.NoHeaderReceived AuthState × (ℕ × P.EpochKey)) :=
  match P.decaps st.sk st.c1 c2 with
  | none => none
  | some k =>
    let ik := P.kdfOK k st.ep
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
def recvHeader (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (st : NoHeaderReceived AuthState) (hdr : P.det.PKheader) (tag : P.Mac) :
    Option (HeaderReceived P AuthState) :=
  if auth.verifyHeader st.authSt st.ep hdr tag then some ⟨st.ep, st.authSt, hdr⟩ else none
-- ANCHOR_END: CtSender_recvHeader

-- ANCHOR: CtSender_sendCt1
/-- Run the first encapsulation stage and return the successor state, the first ciphertext
component, and the epoch key. -/
def sendCt1 (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (st : HeaderReceived P AuthState) :
    m (Ct1Sent P AuthState × P.det.C₁ × (ℕ × P.EpochKey)) := do
  let (encapsSt, c1, k) ← P.encaps1 st.hdr
  let ik := P.kdfOK k st.ep
  pure (⟨st.ep, auth.update st.authSt st.ep ik, st.hdr, encapsSt, c1⟩, c1, (st.ep, ik))
-- ANCHOR_END: CtSender_sendCt1

-- ANCHOR: CtSender_sendCt1Rleak
/-- `sendCt1` with `encaps1` replaced by `encaps1Rleak`, also returning the drawn coins. -/
def sendCt1Rleak (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (st : HeaderReceived P AuthState) :
    m ((Ct1Sent P AuthState × P.det.C₁ × (ℕ × P.EpochKey)) × P.det.Encaps1Rand) := do
  let ((encapsSt, c1, k), r) ← P.encaps1Rleak st.hdr
  let ik := P.kdfOK k st.ep
  pure ((⟨st.ep, auth.update st.authSt st.ep ik, st.hdr, encapsSt, c1⟩, c1, (st.ep, ik)), r)
-- ANCHOR_END: CtSender_sendCt1Rleak

-- ANCHOR: CtSender_recvEk
/-- Accept the vector `ek` when it matches the stored header. -/
def recvEk (P : Parameters m) (st : Ct1Sent P AuthState)
    (ek : P.det.PKvector) : Option (Ct1SentEkReceived P AuthState) :=
  if P.ekMatchesHeader ek st.hdr then
    some ⟨st.ep, st.authSt, st.hdr, st.encapsSt, st.c1, ek⟩
  else none
-- ANCHOR_END: CtSender_recvEk

-- ANCHOR: CtSender_sendCt2
/-- Run the second encapsulation stage and return the successor state, the second ciphertext
component, and the ciphertext tag. -/
def sendCt2 (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (st : Ct1SentEkReceived P AuthState) : Ct2Sent AuthState × P.det.C₂ × P.Mac :=
  let c2 := P.encaps2 st.ek st.encapsSt st.hdr
  (⟨st.ep, st.authSt⟩, c2, auth.macCiphertext st.authSt st.ep (st.c1, c2))
-- ANCHOR_END: CtSender_sendCt2

-- ANCHOR: CtSender_recvNextEpoch
/-- Return the encapsulation-key-sender state exactly when `t` is the successor epoch. -/
def recvNextEpoch (st : Ct2Sent AuthState) (t : ℕ) : Option (EkSender.KeysUnsampled AuthState) :=
  if t = st.ep + 1 then some ⟨st.ep + 1, st.authSt⟩ else none
-- ANCHOR_END: CtSender_recvNextEpoch

end CtSender

end SPQR
