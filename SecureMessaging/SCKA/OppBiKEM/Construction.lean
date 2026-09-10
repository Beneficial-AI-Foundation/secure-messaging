/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Defs
import SecureMessaging.ErasureCode.Defs
import ToVCVio.CryptoFoundations.KeyEncapMech

/-!
# Opp-BiKEM-CKA

Algorithms from Figures 17–18 of https://eprint.iacr.org/2025/2267.pdf.
A encapsulates in odd epochs and B in even epochs. Each party sends its next
public key before its ciphertext, overlapping the two directions of exchange.

Epoch counters are naturals, but we model them as integers because initialization
uses the placeholder epoch `-1`.
Acknowledgements are finite sets of integer indices, making the maximum sending
epoch directly computable. Similarly, secret keys are a finite association list.

We make the following corrections wrt the paper (more info in the docs)

1. Local-variable typos in Send-B and Rec-A (using B's responder
counter in Send-B and B's received ciphertext in Rec-A),
2. We use the existing KEM interface's
`(public key, secret key)` and `decaps secretKey ciphertext` order.
3. [The biggest change] We correct the public-key acknowledgement indices:
Send-A advertises `reqEpoch - 1` and
Send-B advertises `reqEpoch + 1` (line 21 in each figure).
Rec-A records the bit at the sender's `reqEpoch + 1`, and Rec-B at the sender's
`reqEpoch - 1` (line 8 in each figure). These are the entries set by peer-key
decoding; the printed indices prevent acknowledgement of the first public keys.
-/

open KEMScheme

universe u

namespace oppBiKemCKA


-- ANCHOR: role
/-- A party's role (`A` or `B`) in the shared Opp-BiKEM send and receive algorithms. -/
inductive Role where
  | A
  | B
  deriving DecidableEq

/-- `A`'s offset is `+1`; `B`'s is `-1`. Offset captures the division of epochs:
 - `A` is requester in even epochs
 - `B` is requester in odd epochs
Using the offset allows us to have common send/recv
algorithms for `A` and `B`. -/
def Role.offset : Role → ℤ
  | .A => 1
  | .B => -1
-- ANCHOR_END: role

/-- The paper's per-message acknowledgement bits. -/
structure Ack where
  /-- Whether the requester's public encapsulation key has been received by responder . -/
  ekRec : Bool
  /-- Whether the encapsulated session key (ciphertext) has been received by requester. -/
  ctRec : Bool

/-- `ACK[t]` is represented by membership in two finite sets. -/
-- ANCHOR: acknowledgements
structure Acknowledgements where
  /-- Epochs for which the public key has been received locally or acknowledged by the peer. -/
  ekRec : Finset ℤ
  /-- Epochs for which the ciphertext has been decapsulated locally or acknowledged by the peer. -/
  ctRec : Finset ℤ

/-- Largest nonnegative index with two adjacent acknowledged ciphertexts
(both t and t-1 in ack.ctRec).
The empty maximum is zero; honest states initially acknowledge `-1` and `0`. -/
def Acknowledgements.sendingEpoch (ack : Acknowledgements) : ℕ :=
  (ack.ctRec.filter fun t => t - 1 ∈ ack.ctRec).sup Int.toNat
-- ANCHOR_END: acknowledgements

/-- Message `(ch, t_res, t_req, t_snd, ack, b)`; selector `0` means public
key and `1` means ciphertext. The explicit sending epoch survives delayed delivery. -/
-- ANCHOR: message
abbrev Bit := Fin 2

/-- A protocol message carrying an optional erasure-coded public-key or ciphertext
chunk -/
structure Message (Sym : Type) where
  /-- Optional indexed erasure-code chunk of a public key or ciphertext. -/
  ch : Option (ℕ × Sym)
  /-- Sender's current responder epoch. -/
  resEpoch : ℤ
  /-- Sender's current requestor epoch. -/
  reqEpoch : ℤ
  /-- Sender's sending epoch when this message was created
  (both parties have keys to recover all messages in that epoch). -/
  sendingEpoch : ℕ
  /-- Receipt flags for ciphertext epoch `reqEpoch` and public-key epoch
`reqEpoch - role.offset`, using the sender's role. -/
  ack : Ack
  /-- Payload selector: `0` for a public key, `1` for a ciphertext, or `none` for no payload. -/
  bit : Option Bit
-- ANCHOR_END: message

/-- A state of the party in communication (A or B) -/
-- ANCHOR: state
structure State (PK SK C Sym : Type) where
  /-- Current responder epoch, used for outgoing ciphertexts. -/
  resEpoch : ℤ
  /-- Decoded peer public keys indexed by their encapsulation epochs. -/
  ekPeer : ℤ → Option PK
  /-- Outgoing ciphertext, retained until the peer acknowledges it. -/
  ct : Option C
  /-- Last outgoing chunk index, reset to zero when a new payload is prepared. -/
  ich : ℕ
  /-- Current requestor epoch, used for incoming ciphertexts. -/
  reqEpoch : ℤ
  /-- Retained secret keys indexed by their decapsulation epochs. -/
  dk : List (ℤ × SK)
  /-- Local public key, retained until the peer acknowledges it. -/
  ek : Option PK
  /-- Chunks accumulated for decoding the incoming payload (`L_ch` in the paper).
  Each chunk is represented as `(position, encodedSymbol)`. -/
  receivedChunks : Finset (ℕ × Sym)
  /-- Locally recorded and peer-reported receipt acknowledgements. -/
  ack : Acknowledgements

/-- Party A's local protocol state. -/
abbrev StA := State
/-- Party B's local protocol state. -/
abbrev StB := State
-- ANCHOR_END: state

/-- Both randomized calls may run in a send on arbitrary input states.
Each absent component means that this send did not run that primitive.
Used for leak versions of the send operation -/
-- ANCHOR: sendRand
structure SendRand (KeygenRand EncapsRand : Type) where
  /-- Key-generation randomness, or `none` if this send did not generate a key pair. -/
  keygen : Option KeygenRand
  /-- Encapsulation randomness, or `none` if this send did not encapsulate. -/
  encaps : Option EncapsRand
-- ANCHOR_END: sendRand

section Construction

variable {m : Type → Type u} [Monad m] {K PK SK C Sym : Type}

-- ANCHOR: initKeyGen
/-- Return the trivial initialization key: OppBiKEM protocol does not need initialization key -/
def initKeyGen : m Unit := pure ()
-- ANCHOR_END: initKeyGen

/-- Placeholder epoch indices `-1` and `0` are set to enable the first send. -/
-- ANCHOR: init
def init (role : Role) (_ik : Unit) : m (State PK SK C Sym) :=
  pure { resEpoch := if role = .A then -1 else 0
         reqEpoch := if role = .A then 0 else -1
         ekPeer := fun _ => none
         ct := none, ich := 0, dk := [], ek := none, receivedChunks := ∅
         ack := { ekRec := ∅, ctRec := {-1, 0} } }
-- ANCHOR_END: init

-- ANCHOR: initA
/-- Initialize A -/
def initA : Unit → m (StA PK SK C Sym) := init .A
-- ANCHOR_END: initA

-- ANCHOR: initB
/-- Initialize B -/
def initB : Unit → m (StB PK SK C Sym) := init .B
-- ANCHOR_END: initB


/-- For a state `st`, `vuln st` is the set of epochs `n : ℕ` such that
`0 < n` and `st` still stores a decapsulation key at index `(n : ℤ)`. (not yet deleted) -/
-- ANCHOR: vuln
def vuln (st : State PK SK C Sym) : Finset ℕ :=
  let storedEpochs := (st.dk.map Prod.fst).toFinset
  let positiveEpochs := storedEpochs.filter fun t => 0 < t
  positiveEpochs.image Int.toNat

/-- Positive epochs whose secret decapsulation keys remain in A's state. -/
def vulnA (st : StA PK SK C Sym) : Finset ℕ := vuln st

/-- Positive epochs whose secret decapsulation keys remain in B's state. -/
def vulnB (st : StB PK SK C Sym) : Finset ℕ := vuln st
-- ANCHOR_END: vuln

/-- Attach the two acknowledgement bits with their requestor-epoch meaning. -/
def message (role : Role) (st : State PK SK C Sym)
    (ch : Option (ℕ × Sym)) (bit : Option Bit) : Message Sym :=
  { ch, bit, resEpoch := st.resEpoch, reqEpoch := st.reqEpoch
    sendingEpoch := st.ack.sendingEpoch
    ack := { ekRec := decide (st.reqEpoch - role.offset ∈ st.ack.ekRec)
             ctRec := decide (st.reqEpoch ∈ st.ack.ctRec) } }

/-- Common send algorithm. Supplying the randomized primitives explicitly lets
ordinary and leaking sends share the same state transitions. -/
-- ANCHOR: sendWith
def sendWith {RKey REnc : Type} (role : Role)
    (keygen : m ((PK × SK) × RKey)) (encaps : PK → m ((C × K) × REnc))
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) :
    m (Option (Option (ℕ × K) × Message Sym × ℕ × State PK SK C Sym ×
      SendRand RKey REnc)) := do
  let (st, rKey?) ←
    if st.ek.isNone && decide (st.resEpoch ∈ st.ack.ctRec ∧
        st.resEpoch + role.offset ∈ st.ack.ctRec) then do
      let ((ek, dk), rKey) ← keygen
      let t := st.resEpoch + 2
      let keyEpoch := t + role.offset
      pure ({ st with resEpoch := t, ich := 0, ek := some ek
                      dk := (keyEpoch, dk) :: st.dk.filter (fun p => p.1 != keyEpoch) },
            some rKey)
    else pure (st, none)
  let (key?, ch?, bit?, st, rEnc?) ←
    if st.resEpoch + role.offset ∉ st.ack.ekRec then do
      let ich := st.ich + 1
      let ch? := st.ek.map (fun ek => ecEk.encode ek ich)
      pure (none, ch?, some (0 : Bit), { st with ich }, none)
    else if st.resEpoch ∉ st.ack.ctRec then do
      let (key?, st, rEnc?) ←
        if st.ct.isNone && decide (st.resEpoch ∈ st.ack.ekRec) then
          match st.ekPeer st.resEpoch with
          | none => pure (none, st, none)
          | some ekPeer => do
              let ((ct, key), rEnc) ← encaps ekPeer
              pure (some (st.resEpoch.toNat, key), { st with ct := some ct, ich := 0 },
                some rEnc)
        else pure (none, st, none)
      let ich := st.ich + 1
      let ch? := st.ct.map (fun ct => ecCt.encode ct ich)
      pure (key?, ch?, some (1 : Bit), { st with ich }, rEnc?)
    else pure (none, none, none, st, none)
  let ρ := message role st ch? bit?
  pure (some (key?, ρ, ρ.sendingEpoch, st, { keygen := rKey?, encaps := rEnc? }))
-- ANCHOR_END: sendWith

/-- Ordinary send: dummy `Unit` coins are discarded.
Returns an effectful optional result containing:
1. an optional newly established `(epoch, key)`,
2. the outgoing protocol message,
3. the message's sending epoch, and
4. the party's updated state.

The KEM randomness used internally is discarded. -/
-- ANCHOR: send
def send (role : Role) (kem : KEMScheme m K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) :
    m (Option (Option (ℕ × K) × Message Sym × ℕ × State PK SK C Sym)) := do
  let out ← sendWith role
    (do let keys ← kem.keygen; pure (keys, ()))
    (fun pk => do let out ← kem.encaps pk; pure (out, ())) ecEk ecCt st
  pure (out.map fun (key?, ρ, t, st, _) => (key?, ρ, t, st))
-- ANCHOR_END: send

-- ANCHOR: sendA
/-- Run A's send step. -/
def sendA (kem : KEMScheme m K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (stA : StA PK SK C Sym) := send .A kem ecEk ecCt stA
-- ANCHOR_END: sendA

-- ANCHOR: sendB
/-- Run B's send step. -/
def sendB (kem : KEMScheme m K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (stB : StB PK SK C Sym) := send .B kem ecEk ecCt stB
-- ANCHOR_END: sendB

-- ANCHOR: sendArleak
/-- Run A's send step, also returning randomness used for key generation and encapsulation. -/
def sendArleak (kem : KEMScheme m K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak) (stA : StA PK SK C Sym) :=
  sendWith .A leak.keygenRleak leak.encapsRleak ecEk ecCt stA
-- ANCHOR_END: sendArleak

-- ANCHOR: sendBrleak
/-- Run B's send step, also returning randomness used for key generation and encapsulation. -/
def sendBrleak (kem : KEMScheme m K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak) (stB : StB PK SK C Sym) :=
  sendWith .B leak.keygenRleak leak.encapsRleak ecEk ecCt stB
-- ANCHOR_END: sendBrleak

/-- Common receive algorithm. A stale payload is ignored, but its explicitly
indexed acknowledgements are retained. Decapsulation failure does not acknowledge
receipt of an epoch key or erase the secret key needed to recover it.
-/
-- ANCHOR: recv
def recv (role : Role) (kem : KEMScheme m K PK SK C) [DecidableEq Sym]
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym) :
    Option (Option (ℕ × K) × ℕ × State PK SK C Sym) :=
  let ack := st.ack
  let ack := if ρ.ack.ctRec then { ack with ctRec := insert ρ.reqEpoch ack.ctRec } else ack
  let ack := if ρ.ack.ekRec then
      { ack with ekRec := insert (ρ.reqEpoch + role.offset) ack.ekRec } else ack
  let st := { st with ack }
  if ρ.resEpoch < st.reqEpoch then
  -- outdated message
    some (none, ρ.sendingEpoch, st)
  else
    let st := if st.reqEpoch < ρ.resEpoch
              -- first message of the new epoch
              then { st with reqEpoch := st.reqEpoch + 2 }
              else st
    -- Captures the relation of "1 removed" epochs
    --   - if A is requesting the key for epoch t, it receives B's public key for t-1
    --   - if B is requesting the key for epoch t, it receives A's public key for t+1
    let peerKeyEpoch := st.reqEpoch - role.offset
    let (key?, st) :=
      match ρ.bit, ρ.ch with
      | some 0, some ch =>
          if (st.ekPeer peerKeyEpoch).isNone then
            let receivedChunks := insert ch st.receivedChunks
            match ecEk.decode receivedChunks with
            | none => (none, { st with receivedChunks })
            | some ekPeer =>
                (none, { st with receivedChunks := ∅
                                 ekPeer := Function.update st.ekPeer peerKeyEpoch (some ekPeer)
                                 ack := { st.ack with ekRec := insert peerKeyEpoch st.ack.ekRec } })
          else (none, st)
      | some 1, some ch =>
          if st.reqEpoch ∉ st.ack.ctRec then
            match st.dk.lookup st.reqEpoch with
            | none => (none, st)
            | some dk =>
                let receivedChunks := insert ch st.receivedChunks
                match ecCt.decode receivedChunks with
                | none => (none, { st with receivedChunks })
                | some ct =>
                    match hDet.decapsDet dk ct with
                    | none => (none, st)
                    | some key =>
                        (some (st.reqEpoch.toNat, key),
                          { st with receivedChunks := ∅
                                    dk := st.dk.filter (fun p => p.1 != st.reqEpoch)
                                    ack := { st.ack with
                                      ctRec := insert st.reqEpoch st.ack.ctRec } })
          else (none, st)
      | _, _ => (none, st)
    -- deleting the stored material that has been fully delivered
    let st := if st.resEpoch ∈ st.ack.ctRec then { st with ct := none } else st
    let st := if st.resEpoch + role.offset ∈ st.ack.ekRec then { st with ek := none } else st
    some (key?, ρ.sendingEpoch, st)
-- ANCHOR_END: recv

-- ANCHOR: recvA
/-- Process a message at A (by specializing `recv` function) -/
def recvA (kem : KEMScheme m K PK SK C) [DecidableEq Sym]
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (stA : StA PK SK C Sym) (ρ : Message Sym) := recv .A kem hDet ecEk ecCt stA ρ
-- ANCHOR_END: recvA

-- ANCHOR: recvB
/-- Process a message at B (by specializing `recv` function) -/
def recvB (kem : KEMScheme m K PK SK C) [DecidableEq Sym]
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (stB : StB PK SK C Sym) (ρ : Message Sym) := recv .B kem hDet ecEk ecCt stB ρ
-- ANCHOR_END: recvB

-- ANCHOR: scheme
/-- Assemble Opp-BiKEM as an SCKA scheme from a KEM with deterministic decapsulation,
public-key and ciphertext erasure codes, and randomness-leaking KEM operations. -/
def scheme (kem : KEMScheme m K PK SK C) [DecidableEq Sym]
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak) :
    SCKAScheme m Unit (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)
      (SendRand leak.KeygenRand leak.EncapsRand) where
  initKeyGen := initKeyGen
  initA := initA
  initB := initB
  sendA := sendA kem ecEk ecCt
  sendArleak := sendArleak kem ecEk ecCt leak
  recvA := recvA kem hDet ecEk ecCt
  sendB := sendB kem ecEk ecCt
  sendBrleak := sendBrleak kem ecEk ecCt leak
  recvB := recvB kem hDet ecEk ecCt
-- ANCHOR_END: scheme

end Construction
end oppBiKemCKA
