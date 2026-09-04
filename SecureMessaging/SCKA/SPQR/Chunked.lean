/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Basic
import SecureMessaging.SCKA.SPQR.Unchunked

/-! # SPQR chunked protocol

SPQR is Signal's implementation of the ML-KEM Braid key exchange
([SparsePostQuantumRatchet](https://github.com/signalapp/SparsePostQuantumRatchet)). Two parties
repeat the exchange throughout a conversation. Each run is an epoch: the encapsulation-key sender
publishes a fresh KEM public key, the ciphertext sender encapsulates to it, both derive the epoch
key, and the roles swap for the next epoch. A public key or a ciphertext is too large for one chat
message, so each value travels as a stream of chunks, one per message. A chunk is an erasure-code
symbol; any large enough set of chunks reconstructs the value, in any order. The incremental KEM
splits encapsulation in two: stage one needs only a short header of the public key (for ML-KEM the
matrix seed and a hash of the key), stage two needs the full vector. The ciphertext sender therefore
starts its first component while the vector is still arriving, and the two streams cross. The name
'braid' refers to that crossing.

```text
A (encapsulation-key sender)                      B (ciphertext sender)
KeyGen; hdr chunks ─────────────────────────▶     header verified: encaps stage one; key derived
first ct₁ chunk: stop hdr                   ◀──   ct₁ chunks ...
ek chunks ──────────────────────────────────▶     ... ct₁ chunks still arriving
ct₁ complete: ek chunks now carry the ack ──▶     vector complete and acked: encaps stage two
first ct₂ chunk: stop ek                    ◀──   ct₂ chunks with tag
ct₂ complete: decaps; verify tag; key derived
                        next epoch, roles swapped
```

A stream stops when the first chunk of the answering stream arrives: the first `ct₁` chunk shows
that B holds the header, the first `ct₂` chunk that B holds the vector. B cannot see when A holds
all of `ct₁`, so A says so on its vector chunks (`ekCt1Ack`). The header carries a tag, and the
second ciphertext component carries a tag over both components; the authenticator state is
ratcheted each epoch from the initial key (`RatchetedAuthenticator`). SPQR v1 uses thresholds 3,
36, 30, and 5 for the header, vector, `ct₁`, and `ct₂` streams (`SPQR.v1Parameters`).

The SPQR-verify project pins upstream revision `f2589fe`; this module models the SPQR v1 state
machine at that revision. It reproduces `src/v1/chunked/states.rs` row for row over the unchunked
core `SPQR.Unchunked`. An ignored message returns `.ok`, leaves the state unchanged, and has
`outputKey = none`.

The specification defines no epoch report. The SCKA reports follow the Rust adapter:
`sendingEpoch = st.epoch - 1` is the last epoch the receiver is guaranteed to hold, and
`receivingEpoch = msg.epoch - 1` (`lib.rs:298`, `lib.rs:425`, `src/test/v1_impls.rs:25`,
`src/test/v1_impls.rs:40`).

The model abstracts nine implementation details.

1. Byte serialization and `Message::deserialize` (`MsgDecode`, `serialize.rs`) are outside the
   transition model. Comparison with Rust is limited to messages accepted by byte decoding,
   `Message.Deserializable`: a nonzero `u64` epoch and a chunk `index < 2^16`
   (`serialize.rs:249-278`, `serialize.rs:191-201`). The successor bound is a transition
   condition (item 9).
2. The Double-Ratchet chain `index` and the operations in `chain.rs` are omitted.
3. `Ct1Ack(bool)` is represented by chunkless `ct1Ack`; the false flag is unreachable
   (`states.rs:182`, `serialize.rs:268`).
4. The byte-decoding `hax_lib::assume!` and `expect` panic paths are omitted.
5. Rust's `u16` chunk index may wrap on send, while `counterIndex` reduces modulo the code length;
   the model also omits the receive-side bound enforced during byte decoding.
6. The concrete KDF, authenticator, and serializers are parameters.
7. Rust's transactional `SerializedState` discipline is represented by a pure function into
   `Except`; the caller retains the old state on an error.
8. Concrete `PolyEncoder` and `PolyDecoder` are represented by `ErasureCodePayload`.
9. Rust uses `Epoch = u64` (`lib.rs:39`) and requires successor epochs below `u64::MAX` in
   `recv_next_epoch` (`unchunked/send_ct.rs:200`, `chunked/send_ct.rs:294`); Lean uses unbounded
   natural numbers.

The Rust state machine differs from the paper model in several places. `Payload` is the typed form
of the well-formed messages of specification §2.3 (`MLKEMBraid.Message.wellFormed`), so ill-formed
type/data combinations have no counterpart; messages rejected by byte decoding are outside the
comparison (`serialize.rs`). The `ekSentCt1Received` state sends
`Ct1Ack(true)` (`states.rs:182`). At an equal epoch, a standalone `ct1Ack` received by
`ekReceivedCt1Sampled` completes stage two (`states.rs:466-473`), and `ct1Acknowledged` accepts
plain `ek` chunks (`states.rs:479-520`, comment 487).

A future epoch outside the `ct2Sampled` successor case returns `EpochOutOfRange`
(`states.rs:284-524`). Receive reports use the incoming epoch minus one (`states.rs`, `lib.rs:425`).
Rust exposes three error names and collapses its two authentication failures (`states.rs`,
`lib.rs:145`); the model additionally folds a generic-KEM decapsulation refusal, which ML-KEM
never produces, into `macVerifyFailed`.

Both models ignore stale messages and `ct1Sampled` with `ct1Ack`; both discard the chunk in
`ekReceivedCt1Sampled` with `ekCt1Ack`; both store the first chunk in `keysSampled` and
`ct1Received` without a completeness test; and both advance `ct2Sampled` on the successor epoch.
Storing the first chunk without a test assumes that one chunk does not complete `ct₁` or `ct₂`; the
v1 thresholds 30 and 5 satisfy this, and correctness statements for a generic `P` take it as a
hypothesis together with `ErasureCode.Correct`.

See `SPQR.Construction` for SCKA packaging and `MLKEMBraid` for the transition system of the
specification.
-/

open ErasureCodePayload.Streaming

universe u

namespace SPQR.Chunked

variable {m : Type → Type u} [Monad m] {P : MLKEMBraid.Parameters m} {InitKey AuthState : Type}

/-- Wire payload, one constructor per Rust `MessagePayload` variant (`states.rs:31-39`). It replaces
the paper's separate `type` and `data` fields with a typed sum and represents only the reachable
`Ct1Ack(true)` value. -/
-- ANCHOR: Chunked_Payload
inductive Payload (Sym : Type) where
  /-- `None`: no payload (paper `type = None`, `data = none`). -/
  | none
  /-- `Hdr(chunk)`: indexed symbol of the header and tag stream. -/
  | hdr (chunk : ℕ × Sym)
  /-- `Ek(chunk)`: indexed symbol of the encapsulation-key vector. -/
  | ek (chunk : ℕ × Sym)
  /-- `EkCt1Ack(chunk)`: vector symbol, and the sender holds all of `ct₁`. -/
  | ekCt1Ack (chunk : ℕ × Sym)
  /-- `Ct1Ack(true)`: the sender holds all of `ct₁`; the false flag is unreachable
  (`states.rs:182`, `serialize.rs:268`). -/
  | ct1Ack
  /-- `Ct1(chunk)`: indexed symbol of the first ciphertext component. -/
  | ct1 (chunk : ℕ × Sym)
  /-- `Ct2(chunk)`: indexed symbol of the second ciphertext component and its tag. -/
  | ct2 (chunk : ℕ × Sym)
-- ANCHOR_END: Chunked_Payload

/-- Rust `Message` (`states.rs:41`). -/
-- ANCHOR: Chunked_Message
structure Message (Sym : Type) where
  /-- The epoch being negotiated. -/
  epoch : ℕ
  /-- The typed payload. -/
  payload : Payload Sym
-- ANCHOR_END: Chunked_Message

/-- Membership in the image of Rust `Message::deserialize`: a nonzero `u64` epoch and, for a
chunk-bearing payload, a chunk index below `2^16` (`serialize.rs:249-278`, `serialize.rs:191-201`).
Comparison with Rust is limited to these messages. -/
-- ANCHOR: Chunked_Message_Deserializable
def Message.Deserializable {Sym : Type} (msg : Message Sym) : Prop :=
  0 < msg.epoch ∧ msg.epoch < 2 ^ 64 ∧
    match msg.payload with
    | .hdr chunk | .ek chunk | .ekCt1Ack chunk | .ct1 chunk | .ct2 chunk => chunk.1 < 2 ^ 16
    | .none | .ct1Ack => True
-- ANCHOR_END: Chunked_Message_Deserializable

/-- The eleven states of Rust `States` (`states.rs:16-29`), combining an unchunked core with
the stream states stored by Rust. -/
-- ANCHOR: Chunked_PartyState
inductive PartyState (P : MLKEMBraid.Parameters m) (AuthState : Type) where
  /-- Before sampling an encapsulation key (`states.rs:17`). -/
  | keysUnsampled (core : EkSender.KeysUnsampled AuthState)
  /-- Sending the authenticated header stream (`states.rs:18`). -/
  | keysSampled (core : EkSender.HeaderSent P.inc AuthState)
      (sendingHdr : EncoderState (P.inc.PKheader × P.Mac) P.Sym)
  /-- Sending the vector and receiving the first ciphertext component (`states.rs:19-20`). -/
  | headerSent (core : EkSender.EkSent P.inc AuthState)
      (sendingEk : EncoderState P.inc.PKvector P.Sym)
      (receivingCt1 : DecoderState P.inc.C₁ P.Sym)
  /-- Sending vector chunks that acknowledge complete first-ciphertext receipt
  (`states.rs:21`). -/
  | ct1Received (core : EkSender.EkSentCt1Received P.inc AuthState)
      (sendingEk : EncoderState P.inc.PKvector P.Sym)
  /-- Receiving the second ciphertext component (`states.rs:22`). -/
  | ekSentCt1Received (core : EkSender.EkSentCt1Received P.inc AuthState)
      (receivingCt2 : DecoderState (P.inc.C₂ × P.Mac) P.Sym)
  /-- Receiving the authenticated header stream (`states.rs:23`). -/
  | noHeaderReceived (core : CtSender.NoHeaderReceived AuthState)
      (receivingHdr : DecoderState (P.inc.PKheader × P.Mac) P.Sym)
  /-- Receiving the encapsulation-key vector after authenticating the header
  (`states.rs:24`). -/
  | headerReceived (core : CtSender.HeaderReceived P.inc AuthState)
      (receivingEk : DecoderState P.inc.PKvector P.Sym)
  /-- Sending the first ciphertext component while receiving the vector
  (`states.rs:25`). -/
  | ct1Sampled (core : CtSender.Ct1Sent P.inc AuthState)
      (sendingCt1 : EncoderState P.inc.C₁ P.Sym)
      (receivingEk : DecoderState P.inc.PKvector P.Sym)
  /-- Sending the first ciphertext after validating the vector (`states.rs:26`). -/
  | ekReceivedCt1Sampled (core : CtSender.Ct1SentEkReceived P.inc AuthState)
      (sendingCt1 : EncoderState P.inc.C₁ P.Sym)
  /-- Receiving the vector after the first ciphertext is acknowledged (`states.rs:27`). -/
  | ct1Acknowledged (core : CtSender.Ct1Sent P.inc AuthState)
      (receivingEk : DecoderState P.inc.PKvector P.Sym)
  /-- Sending the second ciphertext component (`states.rs:28`). -/
  | ct2Sampled (core : CtSender.Ct2Sent AuthState)
      (sendingCt2 : EncoderState (P.inc.C₂ × P.Mac) P.Sym)
-- ANCHOR_END: Chunked_PartyState

/-- The epoch stored in a state (Rust `States::epoch`). -/
def PartyState.epoch : PartyState P AuthState → ℕ
  | .keysUnsampled core => core.ep
  | .keysSampled core _ => core.ep
  | .headerSent core _ _ => core.ep
  | .ct1Received core _ => core.ep
  | .ekSentCt1Received core _ => core.ep
  | .noHeaderReceived core _ => core.ep
  | .headerReceived core _ => core.ep
  | .ct1Sampled core _ _ => core.ep
  | .ekReceivedCt1Sampled core _ => core.ep
  | .ct1Acknowledged core _ => core.ep
  | .ct2Sampled core _ => core.ep

/-- The three Rust public errors reachable from `States::recv` (`lib.rs:96-122`). -/
-- ANCHOR: Chunked_Error
inductive Error where
  /-- The message epoch is ahead of the state. -/
  | epochOutOfRange (epoch : ℕ)
  /-- A header or ciphertext tag was rejected, or deterministic decapsulation refused the
  ciphertext; ML-KEM never refuses. -/
  | macVerifyFailed
  /-- The received vector failed validation. -/
  | erroneousDataReceived
-- ANCHOR_END: Chunked_Error

/-- Rust `Send` (`states.rs:46`) with the SCKA send report. -/
-- ANCHOR: Chunked_SendResult
structure SendResult (P : MLKEMBraid.Parameters m) (AuthState : Type) where
  /-- The message sent. -/
  msg : Message P.Sym
  /-- The latest epoch the receiver is guaranteed to know on receipt of `msg`: the entry epoch
  minus one (`lib.rs:298`). -/
  sendingEpoch : ℕ
  /-- The epoch key derived by this send, if any. -/
  outputKey : Option (ℕ × P.EpochKey)
  /-- The state after the send. -/
  state : PartyState P AuthState
-- ANCHOR_END: Chunked_SendResult

/-- Rust `Recv` (`states.rs:52`) with the SCKA receive report. -/
-- ANCHOR: Chunked_RecvResult
structure RecvResult (P : MLKEMBraid.Parameters m) (AuthState : Type) where
  /-- The incoming message epoch minus one. -/
  receivingEpoch : ℕ
  /-- The epoch key derived by this receive, if any. -/
  outputKey : Option (ℕ × P.EpochKey)
  /-- The state after the receive. -/
  state : PartyState P AuthState
-- ANCHOR_END: Chunked_RecvResult

/-- Direction A2B starts at epoch one (`lib.rs:200-203`, `unchunked/send_ek.rs:76-79`). -/
-- ANCHOR: Chunked_initA
def initA (P : MLKEMBraid.Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (ik : InitKey) : PartyState P AuthState
-- ANCHOR_END: Chunked_initA
    := .keysUnsampled ⟨1, auth.init ik 1⟩

/-- Direction B2A starts at epoch one with an empty header decoder. -/
-- ANCHOR: Chunked_initB
def initB (P : MLKEMBraid.Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (ik : InitKey) : PartyState P AuthState
-- ANCHOR_END: Chunked_initB
    := .noHeaderReceived ⟨1, auth.init ik 1⟩ (DecoderState.empty P.ecpHdr)

/-- Rust `States::send` (`states.rs:115-273`), one arm per state. The `ekSentCt1Received` arm sends
`Ct1Ack(true)`. -/
-- ANCHOR: Chunked_send
def send (P : MLKEMBraid.Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : PartyState P AuthState) : m (SendResult P AuthState)
-- ANCHOR_END: Chunked_send
    := match st with
  | .keysUnsampled core => do
      -- states.rs:120-136
      let (core', hdr, tag) ← EkSender.sendHeader P.inc auth core
      let (chunk, enc) := (EncoderState.init P.ecpHdr (hdr, tag)).nextChunk
      pure ⟨⟨core.ep, .hdr chunk⟩, core.ep - 1, none, .keysSampled core' enc⟩
  | .keysSampled core enc =>
      -- states.rs:138-148
      let (chunk, enc') := enc.nextChunk
      pure ⟨⟨core.ep, .hdr chunk⟩, core.ep - 1, none, .keysSampled core enc'⟩
  | .headerSent core enc dec =>
      -- states.rs:150-160
      let (chunk, enc') := enc.nextChunk
      pure ⟨⟨core.ep, .ek chunk⟩, core.ep - 1, none, .headerSent core enc' dec⟩
  | .ct1Received core enc =>
      -- states.rs:162-173
      let (chunk, enc') := enc.nextChunk
      pure ⟨⟨core.ep, .ekCt1Ack chunk⟩, core.ep - 1, none, .ct1Received core enc'⟩
  | .ekSentCt1Received core dec =>
      -- states.rs:175-189
      pure ⟨⟨core.ep, .ct1Ack⟩, core.ep - 1, none, .ekSentCt1Received core dec⟩
  | .noHeaderReceived core dec =>
      -- states.rs:191-201
      pure ⟨⟨core.ep, .none⟩, core.ep - 1, none, .noHeaderReceived core dec⟩
  | .headerReceived core dec => do
      -- states.rs:203-219
      let (core', c1, key) ← CtSender.sendCt1 P.inc auth P.kdfOK core
      let (chunk, enc) := (EncoderState.init P.ecpCt1 c1).nextChunk
      pure ⟨⟨core.ep, .ct1 chunk⟩, core.ep - 1, some key, .ct1Sampled core' enc dec⟩
  | .ct1Sampled core enc dec =>
      -- states.rs:221-232
      let (chunk, enc') := enc.nextChunk
      pure ⟨⟨core.ep, .ct1 chunk⟩, core.ep - 1, none, .ct1Sampled core enc' dec⟩
  | .ekReceivedCt1Sampled core enc =>
      -- states.rs:234-245
      let (chunk, enc') := enc.nextChunk
      pure ⟨⟨core.ep, .ct1 chunk⟩, core.ep - 1, none, .ekReceivedCt1Sampled core enc'⟩
  | .ct1Acknowledged core dec =>
      -- states.rs:247-257
      pure ⟨⟨core.ep, .none⟩, core.ep - 1, none, .ct1Acknowledged core dec⟩
  | .ct2Sampled core enc =>
      -- states.rs:259-271
      let (chunk, enc') := enc.nextChunk
      pure ⟨⟨core.ep, .ct2 chunk⟩, core.ep - 1, none, .ct2Sampled core enc'⟩

/-- Complete stage two at the receive site: `send_ct2` (`unchunked/send_ct.rs:177-195`) and the
encoder at the three completion sites (`chunked/send_ct.rs:177-184`, `:233-239`, `:266-272`). -/
-- ANCHOR: Chunked_completeCt2
def completeCt2 (P : MLKEMBraid.Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (core : CtSender.Ct1SentEkReceived P.inc AuthState) : PartyState P AuthState :=
  let c2 := P.hEnc2.encaps2Det core.encapsSt core.hdr core.vec
  let tag := auth.macCiphertext core.authSt core.ep (core.c1, c2)
  .ct2Sampled ⟨core.ep, core.authSt⟩ (EncoderState.init P.ecpCt2 (c2, tag))
-- ANCHOR_END: Chunked_completeCt2

/-- Rust `States::recv` (`states.rs:275-533`). Stale epochs are ignored, and future epochs are
errors except for the `ct2Sampled` successor transition. At an equal epoch, a standalone `ct1Ack`
can complete stage two, and `ct1Acknowledged` accepts plain `ek` chunks. -/
-- ANCHOR: Chunked_recv
def recv (P : MLKEMBraid.Parameters m) [DecidableEq P.Sym]
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : PartyState P AuthState) (msg : Message P.Sym) :
    Except Error (RecvResult P AuthState)
-- ANCHOR_END: Chunked_recv
    :=
  let ignore : Except Error (RecvResult P AuthState) :=
    .ok ⟨msg.epoch - 1, none, st⟩
  if msg.epoch < st.epoch then
    -- states.rs:282-531, stale rows
    ignore
  else if st.epoch < msg.epoch then
    match st with
    | .ct2Sampled core _ =>
        -- states.rs:522-531, successor epoch with any payload
        match CtSender.recvNextEpoch core msg.epoch with
        | some next => .ok ⟨msg.epoch - 1, none, .keysUnsampled next⟩
        | none => .error (.epochOutOfRange msg.epoch)
    | _ =>
        -- states.rs:284-481, future epoch
        .error (.epochOutOfRange msg.epoch)
  else
    match st, msg.payload with
    | .keysUnsampled _, _ =>
        -- states.rs:282-287, cell 1
        ignore
    | .keysSampled core _, .ct1 chunk =>
        -- states.rs:289-305, cell 2
        let (core', vec) := EkSender.sendVector P.inc core
        .ok ⟨msg.epoch - 1, none,
          .headerSent core' (EncoderState.init P.ecpEk vec)
            ((DecoderState.empty P.ecpCt1).addChunk chunk)⟩
    | .headerSent core enc dec, .ct1 chunk =>
        -- states.rs:307-330, cell 3
        let dec' := dec.addChunk chunk
        match dec'.decodedPayload with
        | some c1 => .ok ⟨msg.epoch - 1, none, .ct1Received (EkSender.recvCt1 P.inc core c1) enc⟩
        | none => .ok ⟨msg.epoch - 1, none, .headerSent core enc dec'⟩
    | .ct1Received core _, .ct2 chunk =>
        -- states.rs:332-348, cell 4
        .ok ⟨msg.epoch - 1, none,
          .ekSentCt1Received core ((DecoderState.empty P.ecpCt2).addChunk chunk)⟩
    | .ekSentCt1Received core dec, .ct2 chunk =>
        -- states.rs:350-380, cell 5
        let dec' := dec.addChunk chunk
        match dec'.decodedPayload with
        | some (c2, tag) =>
            match EkSender.recvCt2 P.inc auth P.kdfOK P.hDet core c2 tag with
            | some (next, key) =>
                .ok ⟨msg.epoch - 1, some key,
                  .noHeaderReceived next (DecoderState.empty P.ecpHdr)⟩
            | none => .error .macVerifyFailed
        | none => .ok ⟨msg.epoch - 1, none, .ekSentCt1Received core dec'⟩
    | .noHeaderReceived core dec, .hdr chunk =>
        -- states.rs:380-405, cell 6
        let dec' := dec.addChunk chunk
        match dec'.decodedPayload with
        | some (hdr, tag) =>
            match CtSender.recvHeader P.inc auth core hdr tag with
            | some core' =>
                .ok ⟨msg.epoch - 1, none,
                  .headerReceived core' (DecoderState.empty P.ecpEk)⟩
            | none => .error .macVerifyFailed
        | none => .ok ⟨msg.epoch - 1, none, .noHeaderReceived core dec'⟩
    | .headerReceived _ _, _ =>
        -- states.rs:405-412, cell 7
        ignore
    | .ct1Sampled core enc dec, .ek chunk =>
        -- states.rs:412-458, cell 8
        let dec' := dec.addChunk chunk
        match dec'.decodedPayload with
        | some vec =>
            match CtSender.recvVector P.inc core vec with
            | some core' => .ok ⟨msg.epoch - 1, none, .ekReceivedCt1Sampled core' enc⟩
            | none => .error .erroneousDataReceived
        | none => .ok ⟨msg.epoch - 1, none, .ct1Sampled core enc dec'⟩
    | .ct1Sampled core _ dec, .ekCt1Ack chunk =>
        -- states.rs:412-458, cell 9
        let dec' := dec.addChunk chunk
        match dec'.decodedPayload with
        | some vec =>
            match CtSender.recvVector P.inc core vec with
            | some core' => .ok ⟨msg.epoch - 1, none, completeCt2 P auth core'⟩
            | none => .error .erroneousDataReceived
        | none => .ok ⟨msg.epoch - 1, none, .ct1Acknowledged core dec'⟩
    | .ct1Sampled _ _ _, .ct1Ack =>
        -- states.rs:421, cell 10
        ignore
    | .ekReceivedCt1Sampled core _, .ct1Ack =>
        -- states.rs:460-478 and states.rs:466-473, cell 11
        .ok ⟨msg.epoch - 1, none, completeCt2 P auth core⟩
    | .ekReceivedCt1Sampled core _, .ekCt1Ack _ =>
        -- states.rs:460-478, cell 12
        .ok ⟨msg.epoch - 1, none, completeCt2 P auth core⟩
    | .ekReceivedCt1Sampled _ _, .ek _ =>
        -- states.rs:460-478, cell 13
        ignore
    | .ct1Acknowledged core dec, .ek chunk =>
        -- states.rs:479-520 and states.rs:487, cell 14
        let dec' := dec.addChunk chunk
        match dec'.decodedPayload with
        | some vec =>
            match CtSender.recvVector P.inc core vec with
            | some core' => .ok ⟨msg.epoch - 1, none, completeCt2 P auth core'⟩
            | none => .error .erroneousDataReceived
        | none => .ok ⟨msg.epoch - 1, none, .ct1Acknowledged core dec'⟩
    | .ct1Acknowledged core dec, .ekCt1Ack chunk =>
        -- states.rs:479-520, cell 15
        let dec' := dec.addChunk chunk
        match dec'.decodedPayload with
        | some vec =>
            match CtSender.recvVector P.inc core vec with
            | some core' => .ok ⟨msg.epoch - 1, none, completeCt2 P auth core'⟩
            | none => .error .erroneousDataReceived
        | none => .ok ⟨msg.epoch - 1, none, .ct1Acknowledged core dec'⟩
    | .ct2Sampled _ _, _ =>
        -- states.rs:522-531, cell 16
        ignore
    | _, _ =>
        -- states.rs:275-533, cell 17
        ignore

end SPQR.Chunked
