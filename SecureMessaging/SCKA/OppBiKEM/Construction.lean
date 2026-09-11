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
Each local state contains requester and responder substates matching `st_req` and
`st_res` in the paper, together with their shared acknowledgements.

Absent payloads (`⊥` in the pseudocode) are represented by `none`. The local
`decodeAndInsertChunk` helper makes their receive semantics explicit: an absent chunk
leaves the accumulated chunks unchanged and does not attempt decoding. This
is a modeling convention for a case the paper does not check explicitly.

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
  /-- Whether the ciphertext has been received by the requester; this does not
  by itself certify successful decapsulation. -/
  ctRec : Bool

/-- `ACK[t]` is represented by membership in two finite sets. -/
-- ANCHOR: acknowledgements
structure Acknowledgements where
  /-- Epochs for which the public key has been received locally or acknowledged by the peer. -/
  ekRec : Finset ℤ
  /-- Epochs for which the ciphertext has been decoded locally or acknowledged by the peer.
  Receipt is recorded even if subsequent decapsulation fails. -/
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
  /-- Sender's current requester epoch. -/
  reqEpoch : ℤ
  /-- Sender's sending epoch when this message was created
  (under honest correctness assumptions, both parties have keys to recover
  all messages in that epoch). -/
  sendingEpoch : ℕ
  /-- Receipt flags for ciphertext epoch `reqEpoch` and public-key epoch
`reqEpoch - role.offset`, using the sender's role. -/
  ack : Ack
  /-- Payload selector: `0` for a public key, `1` for a ciphertext, or `none` for no payload. -/
  bit : Option Bit
-- ANCHOR_END: message

-- ANCHOR: state
/-- Responder substate `st_res = (t_res, EK_peer, ct, i_ch)` in Figures 17–18.
The outgoing chunk counter is used for both public keys and ciphertexts. -/
structure ResponderState (PK C : Type) where
  /-- Current responder epoch, used for outgoing ciphertexts. -/
  resEpoch : ℤ
  /-- Decoded peer public keys indexed by their encapsulation epochs. -/
  ekPeer : ℤ → Option PK
  /-- Outgoing ciphertext, retained until the peer acknowledges it. -/
  ct : Option C
  /-- Last outgoing chunk index, reset to zero when a new payload is prepared. -/
  ich : ℕ

/-- Requester substate `st_req = (t_req, DK, ek, L_ch)` in Figures 17–18.
The incoming chunk set is used for both peer public keys and ciphertexts. -/
structure RequesterState (PK SK Sym : Type) where
  /-- Current requester epoch, used for incoming ciphertexts. -/
  reqEpoch : ℤ
  /-- Retained secret keys indexed by their decapsulation epochs. -/
  dk : List (ℤ × SK)
  /-- Local public key, retained until the peer acknowledges it. -/
  ek : Option PK
  /-- Chunks accumulated for decoding the incoming payload (`L_ch` in the paper).
  Each chunk is represented as `(position, encodedSymbol)`. -/
  receivedChunks : Finset (ℕ × Sym)

/-- A party's local state: requester and responder substates with shared `ACK`.
The paper writes this as `(st_res, st_req, ACK)`; the named fields expose each component. -/
structure State (PK SK C Sym : Type) where
  /-- Requester state containing retained decapsulation keys and incoming chunks. -/
  req : RequesterState PK SK Sym
  /-- Responder state containing decoded peer public keys and outgoing ciphertext. -/
  res : ResponderState PK C
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

/-- Initialize the state.
Placeholder epoch indices `-1` and `0` are set to enable the first send. -/
-- ANCHOR: init
def init (role : Role) (_ik : Unit) : m (State PK SK C Sym) :=
  pure { req := { reqEpoch := if role = .A then 0 else -1
                  dk := [], ek := none, receivedChunks := ∅ }
         res := { resEpoch := if role = .A then -1 else 0
                  ekPeer := fun _ => none
                  ct := none, ich := 0 }
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
`0 < n` and `st.req.dk` still stores a decapsulation key at index `(n : ℤ)`. -/
-- ANCHOR: vuln
def vuln (st : State PK SK C Sym) : Finset ℕ :=
  let storedEpochs := (st.req.dk.map Prod.fst).toFinset
  let positiveEpochs := storedEpochs.filter fun t => 0 < t
  positiveEpochs.image Int.toNat

/-- Positive epochs whose secret decapsulation keys remain in A's state. -/
def vulnA (st : StA PK SK C Sym) : Finset ℕ := vuln st

/-- Positive epochs whose secret decapsulation keys remain in B's state. -/
def vulnB (st : StB PK SK C Sym) : Finset ℕ := vuln st
-- ANCHOR_END: vuln

/-- Attach the two acknowledgement bits with their requester-epoch meaning. -/
def message (role : Role) (st : State PK SK C Sym)
    (ch : Option (ℕ × Sym)) (bit : Option Bit) : Message Sym :=
  { ch, bit, resEpoch := st.res.resEpoch, reqEpoch := st.req.reqEpoch
    sendingEpoch := st.ack.sendingEpoch
    ack := { ekRec := decide (st.req.reqEpoch - role.offset ∈ st.ack.ekRec)
             ctRec := decide (st.req.reqEpoch ∈ st.ack.ctRec) } }

/-- Common send algorithm. Supplying the randomized primitives explicitly lets
ordinary and leaking sends share the same state transitions. -/
-- ANCHOR: sendWith
def sendWith {RKey REnc : Type} (role : Role)
    (keygen : m ((PK × SK) × RKey)) (encaps : PK → m ((C × K) × REnc))
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) :
    m (Option (Option (ℕ × K) × Message Sym × ℕ × State PK SK C Sym ×
      SendRand RKey REnc)) := do
  let ⟨resEpoch, ekPeer, ct, ich⟩ := st.res
  let ⟨reqEpoch, dk, ek, receivedChunks⟩ := st.req
  let ack := st.ack
  let (resEpoch, dk, ek, ich, rKey?) ←
    -- if ready to advance the epoch (Line 4 in the paper CKA-Send-P)
    if ek.isNone && decide (resEpoch ∈ ack.ctRec ∧
        resEpoch + role.offset ∈ ack.ctRec) then do
      let ((newEk, newDk), rKey) ← keygen
      let t := resEpoch + 2
      -- the epoch for which the decapsulation key was generated
      -- (t+1 in CKA-Send-A, line 8; t-1 in CKA-Send-B, line 8)
      let keyEpoch := t + role.offset
      pure (t, (keyEpoch, newDk) :: dk.filter (fun p => p.1 != keyEpoch),
        some newEk, 0, some rKey)
    else pure (resEpoch, dk, ek, ich, none)
  let (key?, ch?, bit?, ct, ich, rEnc?) ←
    -- if the encapsulation key was not yet received by the peer (lines 9-12 in CKA-Send-P)
    if resEpoch + role.offset ∉ ack.ekRec then do
      let ich := ich + 1
      let ch? := ek.map (fun ek => ecEk.encode ek ich)
      pure (none, ch?, some (0 : Bit), ct, ich, none)
    -- if the encapsulation key was received, but ciphertext was **not** yet received by the peer
    else if resEpoch ∉ ack.ctRec then do
      let (key?, ct, ich, rEnc?) ←
        -- if no ciphertext is stored and the peer's encapsulation key has been received
        -- (lines 14-16 in CKA-Send-P)
        if ct.isNone && decide (resEpoch ∈ ack.ekRec) then
          match ekPeer resEpoch with
          | none => pure (none, ct, ich, none)
          | some peerEk => do
              let ((newCt, key), rEnc) ← encaps peerEk
              pure (some (resEpoch.toNat, key), some newCt, 0, some rEnc)
        else pure (none, ct, ich, none)
      let ich := ich + 1
      let ch? := ct.map (fun ct => ecCt.encode ct ich)
      pure (key?, ch?, some (1 : Bit), ct, ich, rEnc?)
    else pure (none, none, none, ct, ich, none)
  let st : State PK SK C Sym :=
    { res := ⟨resEpoch, ekPeer, ct, ich⟩
      req := ⟨reqEpoch, dk, ek, receivedChunks⟩
      ack }
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

-- ANCHOR: decodeChunk
/-- Accumulate an optional chunk and try to decode a payload.
For `some ch`, insert the chunk and return the updated set and decoding result.
For `none`, preserve the set and return no payload without
calling the decoder, even if the retained chunks could already decode.
The caller clears the set after successful public-key or ciphertext decoding,
including when subsequent decapsulation fails. -/
def decodeAndInsertChunk {Payload : Type} [DecidableEq Sym]
    (ec : ErasureCodePayload Payload Sym) (receivedChunks : Finset (ℕ × Sym))
    (ch? : Option (ℕ × Sym)) : Finset (ℕ × Sym) × Option Payload :=
  match ch? with
  | none => (receivedChunks, none)
  | some ch =>
      let chunks := insert ch receivedChunks
      (chunks, ec.decode chunks)
-- ANCHOR_END: decodeChunk

/-- Common receive algorithm. A stale payload is ignored, but its explicitly
indexed acknowledgements are retained. Successful ciphertext decoding clears the
chunks, acknowledges ciphertext receipt, and consumes the secret key, even if
decapsulation fails. Such a failure returns no epoch key, matching the paper's
`⊥` key within the optional epoch-key interface.
`decodeAndInsertChunk` handles absent chunks; acknowledgements, epoch processing, and
cleanup still run when a non-stale message carries no chunk. -/
-- ANCHOR: recv
def recv (role : Role) (kem : KEMScheme m K PK SK C) [DecidableEq Sym]
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym) :
    Option (Option (ℕ × K) × ℕ × State PK SK C Sym) :=
  let ⟨resEpoch, ekPeer, ct, ich⟩ := st.res
  let ⟨reqEpoch, dk, ek, receivedChunks⟩ := st.req
  let ⟨ch?, peerResEpoch, peerReqEpoch, sendingEpoch, peerAck, bit?⟩ := ρ
  -- NOTE: in the paper's pseudocode, local state acknowledgement is called `ACK` while the
  -- acknowledgment received from the peer is called `ack`.
  --  Here, we are explicitly calling the state acknowledgement `localAck`
  --  and peer acknowledgement `peerAck`.
  let localAck := st.ack
  -- incorporate acknowledgements received from the peer (lines 5-8 in CKA-Rec-P)
  let localAck := if peerAck.ctRec
    then { localAck with ctRec := insert peerReqEpoch localAck.ctRec }
    else localAck
  let localAck := if peerAck.ekRec then
      { localAck with ekRec := insert (peerReqEpoch + role.offset) localAck.ekRec } else localAck
  if peerResEpoch < reqEpoch then
    -- outdated message: retain only the acknowledgement updates
    some (none, sendingEpoch,
      { res := ⟨resEpoch, ekPeer, ct, ich⟩
        req := ⟨reqEpoch, dk, ek, receivedChunks⟩
        ack := localAck })
  else
    -- first message of the new epoch, lines 11-12
    let reqEpoch := if reqEpoch < peerResEpoch then reqEpoch + 2 else reqEpoch
    -- Captures the relation of "1 removed" epochs
    --   - if A is requesting the key for epoch t, it receives B's public key for t-1
    --   - if B is requesting the key for epoch t, it receives A's public key for t+1
    let peerKeyEpoch := reqEpoch - role.offset
    let (key?, ekPeer, dk, receivedChunks, localAck) :=
      -- if the peer's encapsulating key has not been received yet, lines 13-19
      if (ekPeer peerKeyEpoch).isNone ∧ bit? = some 0 then
        let (chunks, peerEk?) := decodeAndInsertChunk ecEk receivedChunks ch?
        match peerEk? with
        | none => (none, ekPeer, dk, chunks, localAck)
        | some peerEk =>
            (none, Function.update ekPeer peerKeyEpoch (some peerEk), dk, ∅,
              { localAck with ekRec := insert peerKeyEpoch localAck.ekRec })
      -- if ciphertext has not been received and the selector is 1, lines 20-28
      else if reqEpoch ∉ localAck.ctRec ∧ bit? = some 1 then
        match dk.lookup reqEpoch with
        -- Missing secret key: preserve payload state. Unreachable under honest executions.
        | none => (none, ekPeer, dk, receivedChunks, localAck)
        | some secretKey =>
            let (updatedReceivedChunks, peerCt?) := decodeAndInsertChunk ecCt receivedChunks ch?
            match peerCt? with
            | none => (none, ekPeer, dk, updatedReceivedChunks, localAck)
            -- the ciphertext was recovered (lines 23-28): receipt and erasure,
            -- regardless of whether decapsulation succeeds
            | some peerCt =>
                let receivedChunks : Finset (ℕ × Sym) := ∅
                let localAck := { localAck with ctRec := insert reqEpoch localAck.ctRec }
                let key? :=
                  match hDet.decapsDet secretKey peerCt with
                  | none => none
                  | some key => some (reqEpoch.toNat, key)
                let dk := dk.filter (fun p => p.1 != reqEpoch)
                (key?, ekPeer, dk, receivedChunks, localAck)
      --  This branch corresponds to a situation in which neither is true:
      --   * the encapsulating key not received and bit=0
      --   * the ciphertext not received and bit=1
      -- Reachable in honest executions while the peer is waiting for an acknowledgement
      -- (and thus keeps sending more encapsulation key chunks)
      else (none, ekPeer, dk, receivedChunks, localAck)
    -- deleting the stored material that has been fully delivered (lines 29-32)
    let ct := if resEpoch ∈ localAck.ctRec then none else ct
    let ek := if resEpoch + role.offset ∈ localAck.ekRec then none else ek
    some (key?, sendingEpoch,
      { res := ⟨resEpoch, ekPeer, ct, ich⟩
        req := ⟨reqEpoch, dk, ek, receivedChunks⟩
        ack := localAck })
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
