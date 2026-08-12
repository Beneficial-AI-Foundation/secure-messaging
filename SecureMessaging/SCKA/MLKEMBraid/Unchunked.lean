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

The cryptographic core of ML-KEM Braid before transport fragmentation: typed role states
and the transitions between them, following
[ML-KEM Braid, §§2.1–2.4](https://signal.org/docs/specifications/mlkembraid/). It
corresponds to the `send_ek` and `send_ct` modules under `src/v1/unchunked` of Signal's
[SparsePostQuantumRatchet](https://github.com/signalapp/SparsePostQuantumRatchet).

Each epoch has two roles. The encapsulation-key sender:

- generates the key pair and sends the authenticated header;
- sends the encapsulation-key vector;
- receives the first ciphertext component;
- receives the second component with its tag, decapsulates, derives the epoch key, updates
  the authenticator, verifies the tag, emits the epoch key, and switches roles.

The ciphertext sender:

- verifies the header tag;
- runs the first encapsulation stage, emits the epoch key, updates the authenticator, and
  sends the first ciphertext component;
- validates the encapsulation-key vector against the header;
- runs the second encapsulation stage, authenticates both ciphertext components, and sends
  the second component with its tag;
- switches roles on evidence of the next epoch.

## Driver contract

The chunked layer reassembles the transport pieces of a message and drives these
transitions in the order above, buffering anything that arrives early. The core owns only
the cryptographic checks.

## Fail-closed behavior

Guarded transitions return an `Option`. A `none` produces no state, so the caller keeps
the state it had. This models the specification's rule that on a failed check all changes
to the algorithm state are discarded and undone, after which the session must not proceed.

## Authenticator threading

Header tags use the authenticator state before the epoch-key update, ciphertext tags the
state after it. The update consumes the derived epoch key, not the raw shared secret. One
ciphertext tag covers both components as a single message: the pair `(ct₁, ct₂)` models
the specification's concatenation `ct₁ ‖ ct₂`.

ML-KEM decapsulation uses implicit rejection. Detection of ciphertext tampering
therefore depends on the authenticator. This interface assumes only honest
verification; authentication security is deferred to issue #244. The failure branch
of decapsulation keeps the transitions total over KEMs that reject explicitly.

## Correspondence with the chunked state machine

The state machine of §2.5 also tracks transport progress, so one core phase can cover more
than one of its states.

| core phase | §2.5 state |
| --- | --- |
| `EkSender.Start` | `KeysUnsampled` |
| `EkSender.HeaderSent` | `KeysSampled`, then `HeaderSent` |
| `EkSender.VectorSent` | `HeaderSent`, with the vector out |
| `EkSender.AwaitingCt2` | `Ct1Received`, `EkSentCt1Received` |
| `CtSender.Start` | `NoHeaderReceived` |
| `CtSender.HeaderReceived` | `HeaderReceived` |
| `CtSender.Ct1Sent` | `Ct1Sampled` |
| `CtSender.VectorReceived` | `EkReceivedCt1Sampled`, `Ct1Acknowledged` |
| `CtSender.Ct2Sent` | `Ct2Sampled` |

`CtSender.recvNextEpoch` is the next-epoch trigger out of `Ct2Sampled`, which fires when
`msg.epoch = state.epoch + 1`, and Signal's `recv_next_epoch`. What counts as evidence of
the next epoch is a transport matter: epoch stamps carried by incoming messages, owned by
the chunked layer.

## Exclusions

Chunking, erasure coding, acknowledgements, session initialization and the `SCKAScheme`
packaging belong to the chunked layer (issue #242). The correctness and security
experiments are issues #243 and #244. A concrete HKDF derivation and a concrete HMAC
authenticator are a later instance issue.
-/

open KEMScheme

universe u

namespace MLKEMBraid

variable {m : Type → Type u} [Monad m] {K PK SK C : Type} {kem : KEMScheme m K PK SK C}

/-- Abstract post-KEM epoch-key derivation: the per-epoch output key as a function of
the KEM shared secret and the epoch, `KDF_OK` of the ML-KEM Braid specification. The
specification derives each epoch key independently (zero salt, epoch-tagged info
string), so a plain function of the pair is the faithful abstraction. A concrete HKDF
instance is a later issue. -/
-- ANCHOR: EpochKeyDerivation
abbrev EpochKeyDerivation (K EpochKey : Type) : Type := K → ℕ → EpochKey
-- ANCHOR_END: EpochKeyDerivation

/-! ## Role states

Phase types rule out transitions from states of the wrong phase; their public
constructors do not encode reachability. Initialization supplies the `Start` states;
thereafter, reachability through these transitions is a driver invariant (issue #242).

Mid-epoch phases are indexed by the incremental structure they run over; the index
also pins the key types where no field mentions them. The phases holding no KEM data
(`EkSender.Start`, `CtSender.Start`, `CtSender.Ct2Sent`) are indexed only by the
authenticator state type: they sit at the epoch boundary. -/

namespace EkSender

/-- Encapsulation-key sender at the start of its epoch: no key material sampled yet. -/
structure Start (AuthState : Type) where
  /-- The epoch in progress. -/
  ep : ℕ
  /-- Authenticator state entering the epoch. -/
  authSt : AuthState

/-- After `sendHeader`: the key pair is sampled and the authenticated header is out.
The vector part of the encapsulation key is still to be sent. -/
structure HeaderSent (inc : kem.IncrementalStructure) (AuthState : Type) where
  /-- The epoch in progress. -/
  ep : ℕ
  /-- Authenticator state entering the epoch. -/
  authSt : AuthState
  /-- The sampled encapsulation key. -/
  pk : PK
  /-- The decapsulation key held for this epoch. -/
  sk : SK

/-- After `sendVector`: the whole encapsulation key is out and its public part is
dropped. Awaiting the first ciphertext component. -/
structure VectorSent (inc : kem.IncrementalStructure) (AuthState : Type) where
  /-- The epoch in progress. -/
  ep : ℕ
  /-- Authenticator state entering the epoch. -/
  authSt : AuthState
  /-- The decapsulation key held for this epoch. -/
  sk : SK

/-- After `recvCt1`: holds the first ciphertext component, awaiting the second
component and the ciphertext tag. -/
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

/-- Ciphertext sender at the start of its epoch: awaiting the authenticated header. -/
structure Start (AuthState : Type) where
  /-- The epoch in progress. -/
  ep : ℕ
  /-- Authenticator state entering the epoch. -/
  authSt : AuthState

/-- Ciphertext-sender phase ready for the first encapsulation stage. -/
structure HeaderReceived (inc : kem.IncrementalStructure) (AuthState : Type) where
  /-- The epoch in progress. -/
  ep : ℕ
  /-- Authenticator state entering the epoch. -/
  authSt : AuthState
  /-- Stored encapsulation-key header. -/
  hdr : inc.PKheader

/-- After `sendCt1`: the epoch key is derived and reported, the authenticator is
updated, and the first ciphertext component is out. Awaiting the encapsulation-key
vector. -/
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

/-- Ciphertext-sender phase ready for the second encapsulation stage. -/
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

/-- After `sendCt2`: both ciphertext components and the tag are out. The party stays
in its epoch until the driver observes next-epoch evidence (`recvNextEpoch`). -/
structure Ct2Sent (AuthState : Type) where
  /-- The epoch in progress. -/
  ep : ℕ
  /-- Authenticator state after the update with this epoch's key. -/
  authSt : AuthState

end CtSender

variable {InitKey EpochKey AuthState Mac : Type}

/-! ## Encapsulation-key sender transitions -/

namespace EkSender

-- ANCHOR: EkSenderTransitions
/-- Start the epoch: generate the key pair and authenticate the header with the state
entering the epoch. Returns the header and its tag — the first protocol message — and
the next phase. -/
def sendHeader (inc : kem.IncrementalStructure)
    (auth : RatchetedAuthenticator InitKey EpochKey AuthState inc.PKheader (inc.C₁ × inc.C₂) Mac)
    (st : Start AuthState) : m ((inc.PKheader × Mac) × HeaderSent inc AuthState) := do
  let (pk, sk) ← kem.keygen
  let hdr := inc.toHeader pk
  pure ((hdr, auth.macHeader st.authSt st.ep hdr), ⟨st.ep, st.authSt, pk, sk⟩)

/-- Send the vector part of the encapsulation key. Pure: the message is a projection of
the stored key, and the public part is dropped once the vector is out. -/
def sendVector (inc : kem.IncrementalStructure) (st : HeaderSent inc AuthState) :
    inc.PKvector × VectorSent inc AuthState :=
  (inc.toVector st.pk, ⟨st.ep, st.authSt, st.sk⟩)

/-- Receive the first ciphertext component. Total: the component carries no tag of its
own; its authenticity is checked at `recvCt2` through the tag over both components. -/
def recvCt1 (inc : kem.IncrementalStructure) (st : VectorSent inc AuthState)
    (c1 : inc.C₁) : AwaitingCt2 inc AuthState :=
  ⟨st.ep, st.authSt, st.sk, c1⟩

/-- Receive the second ciphertext component and its tag and finish the epoch:
decapsulate, derive the epoch key, update the authenticator with it, and verify the tag
over both components with the updated state. On success the epoch key is emitted with
its epoch and the party switches roles into the next epoch's ciphertext sender. `none`
is the fail-closed outcome: no state is produced and the caller keeps the old one, the
specification's discard-on-failure rule. ML-KEM decapsulation rejects implicitly, so
tamper detection depends on the authenticator; its security is deferred to issue #244.
The `decapsDet = none` branch supports KEMs with explicit rejection. -/
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
-- ANCHOR_END: EkSenderTransitions

end EkSender

/-! ## Ciphertext sender transitions -/

namespace CtSender

-- ANCHOR: CtSenderTransitions
/-- Receive the header and its tag and verify the tag with the state entering the
epoch. `none` is the fail-closed outcome for a tag that does not verify. -/
def recvHeader (inc : kem.IncrementalStructure)
    (auth : RatchetedAuthenticator InitKey EpochKey AuthState inc.PKheader (inc.C₁ × inc.C₂) Mac)
    (st : Start AuthState) (hdr : inc.PKheader) (tag : Mac) :
    Option (HeaderReceived inc AuthState) :=
  if auth.verifyHeader st.authSt st.ep hdr tag then some ⟨st.ep, st.authSt, hdr⟩ else none

/-- Run the first encapsulation stage on the verified header: derive this epoch's key
from the fresh shared secret, report it, update the authenticator with it, and send the
first ciphertext component. The key is reported already here, before the vector
arrives, as in the specification. -/
def sendCt1 (inc : kem.IncrementalStructure)
    (auth : RatchetedAuthenticator InitKey EpochKey AuthState inc.PKheader (inc.C₁ × inc.C₂) Mac)
    (deriveEpochKey : EpochKeyDerivation K EpochKey) (st : HeaderReceived inc AuthState) :
    m ((ℕ × EpochKey) × inc.C₁ × Ct1Sent inc AuthState) := do
  let (encapsSt, c1, k) ← inc.encaps1 st.hdr
  let ik := deriveEpochKey k st.ep
  pure ((st.ep, ik), c1, ⟨st.ep, auth.update st.authSt st.ep ik, st.hdr, encapsSt, c1⟩)

/-- Receive the encapsulation-key vector and validate it against the stored header.
`none` is the fail-closed outcome for a pair that fails `validPK`. -/
def recvVector (inc : kem.IncrementalStructure) (st : Ct1Sent inc AuthState)
    (vec : inc.PKvector) : Option (VectorReceived inc AuthState) :=
  if inc.validPK st.hdr vec then
    some ⟨st.ep, st.authSt, st.hdr, st.encapsSt, st.c1, vec⟩
  else none

/-- Run the second encapsulation stage and authenticate both ciphertext components as
one message with the updated state. Returns the second component and the tag — the
final protocol message of the epoch — and parks the party in `Ct2Sent`: the switch
into the next epoch waits for `recvNextEpoch`. -/
def sendCt2 (inc : kem.IncrementalStructure)
    (auth : RatchetedAuthenticator InitKey EpochKey AuthState inc.PKheader (inc.C₁ × inc.C₂) Mac)
    (st : VectorReceived inc AuthState) : m ((inc.C₂ × Mac) × Ct2Sent AuthState) := do
  let c2 ← inc.encaps2 st.encapsSt st.hdr st.vec
  pure ((c2, auth.macCiphertext st.authSt st.ep (st.c1, c2)), ⟨st.ep, st.authSt⟩)

/-- Switch roles on next-epoch evidence: the driver reports the epoch `t` it observed
from the partner, and the party becomes the next epoch's encapsulation-key sender
exactly when `t` is the successor of its own epoch. `none` is the fail-closed outcome
for any other evidence. This is the specification's next-epoch trigger and SPQR's
`recv_next_epoch`, which requires `next_epoch == self.epoch + 1`. -/
def recvNextEpoch (st : Ct2Sent AuthState) (t : ℕ) : Option (EkSender.Start AuthState) :=
  if t = st.ep + 1 then some ⟨st.ep + 1, st.authSt⟩ else none
-- ANCHOR_END: CtSenderTransitions

end CtSender

/-! ## Fail-closed behavior

The guarded transitions reject exactly on the specification's failure events, and
honest inputs are accepted through the authenticator's honest-verification properties.
These lemmas pin that behavior; the correctness and security experiments belong to
later issues. -/

namespace CtSender

/-- A header is rejected exactly when its tag does not verify. -/
theorem recvHeader_eq_none_iff (inc : kem.IncrementalStructure)
    (auth : RatchetedAuthenticator InitKey EpochKey AuthState inc.PKheader (inc.C₁ × inc.C₂) Mac)
    {st : Start AuthState} {hdr : inc.PKheader} {tag : Mac} :
    recvHeader inc auth st hdr tag = none ↔
      auth.verifyHeader st.authSt st.ep hdr tag = false := by
  simp [recvHeader]

/-- An honestly produced header tag is accepted. -/
theorem recvHeader_macHeader (inc : kem.IncrementalStructure)
    (auth : RatchetedAuthenticator InitKey EpochKey AuthState inc.PKheader (inc.C₁ × inc.C₂) Mac)
    {st : Start AuthState} (hdr : inc.PKheader) :
    recvHeader inc auth st hdr (auth.macHeader st.authSt st.ep hdr) =
      some ⟨st.ep, st.authSt, hdr⟩ := by
  simp [recvHeader, auth.verifyHeader_correct]

/-- A vector is rejected exactly when the pair fails the consistency check. -/
theorem recvVector_eq_none_iff (inc : kem.IncrementalStructure)
    {st : Ct1Sent inc AuthState} {vec : inc.PKvector} :
    recvVector inc st vec = none ↔ inc.validPK st.hdr vec = false := by
  simp [recvVector]

/-- The honest vector of a split key passes validation and is stored. -/
theorem recvVector_toVector (inc : kem.IncrementalStructure)
    {st : Ct1Sent inc AuthState} {pk : PK} (hhdr : st.hdr = inc.toHeader pk) :
    recvVector inc st (inc.toVector pk) =
      some ⟨st.ep, st.authSt, st.hdr, st.encapsSt, st.c1, inc.toVector pk⟩ := by
  have hvalid : inc.validPK st.hdr (inc.toVector pk) = true := by
    rw [hhdr]
    exact (inc.splitPK pk).2
  simp [recvVector, hvalid]

/-- The switch rejects exactly the evidence that is not the successor epoch. -/
theorem recvNextEpoch_eq_none_iff {st : Ct2Sent AuthState} {t : ℕ} :
    recvNextEpoch st t = none ↔ t ≠ st.ep + 1 := by
  simp [recvNextEpoch]

end CtSender

namespace EkSender

/-- Complete characterization of the epoch-finishing receive: it succeeds exactly when
decapsulation returns a key whose derived epoch key makes the ciphertext tag verify
under the updated authenticator state; the emission and the successor state are then
determined. -/
theorem recvCt2_eq_some_iff (inc : kem.IncrementalStructure)
    (auth : RatchetedAuthenticator InitKey EpochKey AuthState inc.PKheader (inc.C₁ × inc.C₂) Mac)
    (deriveEpochKey : EpochKeyDerivation K EpochKey) (hDet : DeterministicDecaps kem)
    {st : AwaitingCt2 inc AuthState} {c2 : inc.C₂} {tag : Mac}
    {t : ℕ} {ik : EpochKey} {next : CtSender.Start AuthState} :
    recvCt2 inc auth deriveEpochKey hDet st c2 tag = some ((t, ik), next) ↔
      ∃ k, hDet.decapsDet st.sk (inc.splitC.symm (st.c1, c2)) = some k ∧
        auth.verifyCiphertext (auth.update st.authSt st.ep (deriveEpochKey k st.ep)) st.ep
          (st.c1, c2) tag = true ∧
        t = st.ep ∧ ik = deriveEpochKey k st.ep ∧
        next = ⟨st.ep + 1, auth.update st.authSt st.ep (deriveEpochKey k st.ep)⟩ := by
  unfold recvCt2
  cases hdec : hDet.decapsDet st.sk (inc.splitC.symm (st.c1, c2)) with
  | none => simp
  | some k =>
    by_cases hver : auth.verifyCiphertext (auth.update st.authSt st.ep (deriveEpochKey k st.ep))
        st.ep (st.c1, c2) tag = true
    · constructor
      · intro h
        simp only [hver, if_true, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        exact ⟨k, rfl, hver, rfl, rfl, rfl⟩
      · rintro ⟨k', hk, -, rfl, rfl, rfl⟩
        obtain rfl := Option.some.inj hk
        simp [hver]
    · simp [hver]

/-- An honestly produced ciphertext tag is accepted when decapsulation returns the
matching key: the epoch key is emitted and the party advances. This pins the
update-before-verify threading of the authenticator state. -/
theorem recvCt2_macCiphertext (inc : kem.IncrementalStructure)
    (auth : RatchetedAuthenticator InitKey EpochKey AuthState inc.PKheader (inc.C₁ × inc.C₂) Mac)
    (deriveEpochKey : EpochKeyDerivation K EpochKey) (hDet : DeterministicDecaps kem)
    {st : AwaitingCt2 inc AuthState} {c2 : inc.C₂} {k : K}
    (hdec : hDet.decapsDet st.sk (inc.splitC.symm (st.c1, c2)) = some k) :
    recvCt2 inc auth deriveEpochKey hDet st c2
        (auth.macCiphertext (auth.update st.authSt st.ep (deriveEpochKey k st.ep)) st.ep
          (st.c1, c2)) =
      some ((st.ep, deriveEpochKey k st.ep),
        ⟨st.ep + 1, auth.update st.authSt st.ep (deriveEpochKey k st.ep)⟩) := by
  simp [recvCt2, hdec, auth.verifyCiphertext_correct]

end EkSender

end MLKEMBraid
