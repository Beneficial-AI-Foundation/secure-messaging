/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Construction
import SecureMessaging.SCKA.SPQR.Unchunked

/-! # SPQR chunked protocol

SPQR is Signal's implementation of the ML-KEM Braid key exchange. This module models its v1
send and receive transitions at revision `f2589fe`, using the core operations in `SPQR.Unchunked`.

## One epoch

An epoch is one key exchange. The encapsulation-key sender generates a public key. The ciphertext
sender uses that key to form a ciphertext and derive a shared key. The encapsulation-key sender
derives the same key by decapsulation when the underlying key-encapsulation mechanism (KEM) is
correct. The parties then swap roles for the next epoch.

Incremental encapsulation has two stages. The first uses a short header of the public key; the
second also uses its vector. The ciphertext sender can therefore start sending `ct₁`, the first
ciphertext component, while the vector is still arriving.

## Chunk streams

The header, vector, `ct₁`, and `ct₂` travel as separate streams of indexed chunks. The header and
`ct₂` streams also carry authentication tags. In the concrete v1 instance, each chunk has 32 bytes.
The Reed-Solomon thresholds are 3, 36, 30, and 5 respectively. Decoding requires enough correct
chunks at distinct indices.

```text
Encapsulation-key sender                       Ciphertext sender
header and tag chunks -----------------------> verify header; start encapsulation
                       <---------------------- ct₁ chunks
vector chunks -------------------------------->
vector chunks with ct₁ acknowledgement --------> finish encapsulation
                       <---------------------- ct₂ and tag chunks
decapsulate and verify
                         roles swap
```

The first `ct₁` chunk stops header transmission. Once all of `ct₁` has arrived, vector chunks
carry its acknowledgement (`ekCt1Ack`). The first `ct₂` chunk stops vector transmission.

## Epoch reports and errors

A send reports `st.epoch - 1`; a successful receive reports `msg.epoch - 1`. These are the SCKA
reports used by the Rust adapter (`lib.rs:298`, `lib.rs:425`, `src/test/v1_impls.rs:25`,
`src/test/v1_impls.rs:40`).

An ignored message returns `.ok`, keeps the state, and has `outputKey = none`. Receive failures
return `epochOutOfRange`, `macVerifyFailed`, or `erroneousDataReceived`. `SPQR.recvSCKA` maps these
errors to `none` for the current `SCKAScheme` interface.

## Relation to the Rust implementation

The transition cases follow `src/v1/chunked/states.rs`.

- Messages are typed values. Byte decoding, the Double Ratchet chain index, and byte-decoding
  assumptions and panic paths are omitted.
- Epochs and chunk indices are natural numbers. Rust byte decoding accepts nonzero `u64` epochs
  and indices below `2^16` (`states/serialize.rs:191-201`, `:249-278`). The model does not enforce
  these bounds or the Rust successor-epoch bound (`unchunked/send_ct.rs:200`,
  `chunked/send_ct.rs:294`).
- Rust's send index can wrap at `u16`; the model's `counterIndex` reduces modulo the code length.
- `ct1Ack` represents `Ct1Ack(true)`, the value emitted by send and accepted by byte decoding
  (`states.rs:182`, `states/serialize.rs:268`).
- The key-derivation function (KDF), authenticator, and payload serializers are parameters.
  Payload schemes are `ErasureCodePayload`s, encoder states are `EncoderState`s, and decoders are
  `StreamDecoder`s. Decoder soundness (`StreamDecoder.Sound`) is a separate property.
- Receive is a pure function into `Except`. On error, the caller retains the old state, modeling
  Rust's transactional state handling.
- The first `ct₁` chunk in `keysSampled` and the first `ct₂` chunk in `ct1Received` are stored
  without testing completion. The v1 thresholds for these streams are 30 and 5.

The generic KEM may refuse decapsulation. This refusal maps to `macVerifyFailed`; the ML-KEM
instance does not refuse decapsulation.

## Relation to the paper model

The paper model is `MLKEMBraid`. SPQR sends `ct1Ack` in `ekSentCt1Received`, accepts it in
`ekReceivedCt1Sampled`, and accepts plain `ek` chunks in `ct1Acknowledged`. A future epoch is an
error except for the `ct2Sampled` successor case. These cases differ from the paper transitions.

`SPQR.Construction` packages this model as an SCKA scheme. `SPQR.Correspondence` translates states
and messages into `MLKEMBraid` and states the hypotheses under which their transitions agree.
-/

open ErasureCodePayload.Streaming

universe u

namespace SPQR.Chunked

variable {m : Type → Type u} [Monad m] {P : Parameters m} {InitKey AuthState : Type}

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

/-- The eleven states of Rust `States` (`states.rs:16-29`), combining an unchunked core with
the stream states stored by Rust. -/
-- ANCHOR: Chunked_PartyState
inductive PartyState (P : Parameters m) (AuthState : Type) where
  /-- Before sampling an encapsulation key (`states.rs:17`). -/
  | keysUnsampled (core : EkSender.KeysUnsampled AuthState)
  /-- Sending the authenticated header stream (`states.rs:18`). -/
  | keysSampled (core : EkSender.HeaderSent P AuthState)
      (sendingHdr : EncoderState (P.det.PKheader × P.Mac) P.Sym)
  /-- Sending the vector and receiving the first ciphertext component (`states.rs:19-20`). -/
  | headerSent (core : EkSender.EkSent P AuthState)
      (sendingEk : EncoderState P.det.PKvector P.Sym)
      (receivingCt1 : P.decCt1.D)
  /-- Sending vector chunks that acknowledge complete first-ciphertext receipt
  (`states.rs:21`). -/
  | ct1Received (core : EkSender.EkSentCt1Received P AuthState)
      (sendingEk : EncoderState P.det.PKvector P.Sym)
  /-- Receiving the second ciphertext component (`states.rs:22`). -/
  | ekSentCt1Received (core : EkSender.EkSentCt1Received P AuthState)
      (receivingCt2 : P.decCt2.D)
  /-- Receiving the authenticated header stream (`states.rs:23`). -/
  | noHeaderReceived (core : CtSender.NoHeaderReceived AuthState)
      (receivingHdr : P.decHdr.D)
  /-- Receiving the encapsulation-key vector after authenticating the header
  (`states.rs:24`). -/
  | headerReceived (core : CtSender.HeaderReceived P AuthState)
      (receivingEk : P.decEk.D)
  /-- Sending the first ciphertext component while receiving the vector
  (`states.rs:25`). -/
  | ct1Sampled (core : CtSender.Ct1Sent P AuthState)
      (sendingCt1 : EncoderState P.det.C₁ P.Sym)
      (receivingEk : P.decEk.D)
  /-- Sending the first ciphertext after validating the vector (`states.rs:26`). -/
  | ekReceivedCt1Sampled (core : CtSender.Ct1SentEkReceived P AuthState)
      (sendingCt1 : EncoderState P.det.C₁ P.Sym)
  /-- Receiving the vector after the first ciphertext is acknowledged (`states.rs:27`). -/
  | ct1Acknowledged (core : CtSender.Ct1Sent P AuthState)
      (receivingEk : P.decEk.D)
  /-- Sending the second ciphertext component (`states.rs:28`). -/
  | ct2Sampled (core : CtSender.Ct2Sent AuthState)
      (sendingCt2 : EncoderState (P.det.C₂ × P.Mac) P.Sym)
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
structure SendResult (P : Parameters m) (AuthState : Type) where
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
structure RecvResult (P : Parameters m) (AuthState : Type) where
  /-- The incoming message epoch minus one. -/
  receivingEpoch : ℕ
  /-- The epoch key derived by this receive, if any. -/
  outputKey : Option (ℕ × P.EpochKey)
  /-- The state after the receive. -/
  state : PartyState P AuthState
-- ANCHOR_END: Chunked_RecvResult

/-- Direction A2B starts at epoch one (`lib.rs:200-203`, `unchunked/send_ek.rs:76-79`). -/
-- ANCHOR: Chunked_initA
def initA (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (ik : InitKey) : PartyState P AuthState := .keysUnsampled ⟨1, auth.init ik 1⟩
-- ANCHOR_END: Chunked_initA

/-- Direction B2A starts at epoch one with an empty header decoder. -/
-- ANCHOR: Chunked_initB
def initB (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (ik : InitKey) : PartyState P AuthState :=
  .noHeaderReceived ⟨1, auth.init ik 1⟩ P.decHdr.empty
-- ANCHOR_END: Chunked_initB

/-- Rust `States::send` (`states.rs:115-273`), one arm per state. The `ekSentCt1Received` arm sends
`Ct1Ack(true)`. -/
-- ANCHOR: Chunked_send
def send (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (st : PartyState P AuthState) : m (SendResult P AuthState) :=
  match st with
  | .keysUnsampled core => do
      -- states.rs:120-136
      let (core', hdr, tag) ← EkSender.sendHeader P auth core
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
      let (core', c1, key) ← CtSender.sendCt1 P auth core
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
-- ANCHOR_END: Chunked_send

/-- Complete stage two at the receive site: `send_ct2` (`unchunked/send_ct.rs:177-195`) and the
encoder at the three completion sites (`chunked/send_ct.rs:177-184`, `:233-239`, `:266-272`). -/
-- ANCHOR: Chunked_completeCt2
def completeCt2 (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (core : CtSender.Ct1SentEkReceived P AuthState) : PartyState P AuthState :=
  let c2 := P.encaps2 core.ek core.encapsSt core.hdr
  let tag := auth.macCiphertext core.authSt core.ep (core.c1, c2)
  .ct2Sampled ⟨core.ep, core.authSt⟩ (EncoderState.init P.ecpCt2 (c2, tag))
-- ANCHOR_END: Chunked_completeCt2

/-- Rust `States::recv` (`states.rs:275-533`). Stale epochs are ignored, and future epochs are
errors except for the `ct2Sampled` successor transition. At an equal epoch, a standalone `ct1Ack`
can complete stage two, and `ct1Acknowledged` accepts plain `ek` chunks. -/
-- ANCHOR: Chunked_recv
def recv (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (st : PartyState P AuthState) (msg : Message P.Sym) :
    Except Error (RecvResult P AuthState) :=
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
        let (core', ek) := EkSender.sendEk P core
        .ok ⟨msg.epoch - 1, none,
          .headerSent core' (EncoderState.init P.ecpEk ek)
            (P.decCt1.addChunk P.decCt1.empty chunk)⟩
    | .headerSent core enc dec, .ct1 chunk =>
        -- states.rs:307-330, cell 3
        let dec' := P.decCt1.addChunk dec chunk
        match P.decCt1.decodedPayload dec' with
        | some c1 => .ok ⟨msg.epoch - 1, none, .ct1Received (EkSender.recvCt1 P core c1) enc⟩
        | none => .ok ⟨msg.epoch - 1, none, .headerSent core enc dec'⟩
    | .ct1Received core _, .ct2 chunk =>
        -- states.rs:332-348, cell 4
        .ok ⟨msg.epoch - 1, none,
          .ekSentCt1Received core (P.decCt2.addChunk P.decCt2.empty chunk)⟩
    | .ekSentCt1Received core dec, .ct2 chunk =>
        -- states.rs:350-380, cell 5
        let dec' := P.decCt2.addChunk dec chunk
        match P.decCt2.decodedPayload dec' with
        | some (c2, tag) =>
            match EkSender.recvCt2 P auth core c2 tag with
            | some (next, key) =>
                .ok ⟨msg.epoch - 1, some key,
                  .noHeaderReceived next P.decHdr.empty⟩
            | none => .error .macVerifyFailed
        | none => .ok ⟨msg.epoch - 1, none, .ekSentCt1Received core dec'⟩
    | .noHeaderReceived core dec, .hdr chunk =>
        -- states.rs:380-405, cell 6
        let dec' := P.decHdr.addChunk dec chunk
        match P.decHdr.decodedPayload dec' with
        | some (hdr, tag) =>
            match CtSender.recvHeader P auth core hdr tag with
            | some core' =>
                .ok ⟨msg.epoch - 1, none,
                  .headerReceived core' P.decEk.empty⟩
            | none => .error .macVerifyFailed
        | none => .ok ⟨msg.epoch - 1, none, .noHeaderReceived core dec'⟩
    | .headerReceived _ _, _ =>
        -- states.rs:405-412, cell 7
        ignore
    | .ct1Sampled core enc dec, .ek chunk =>
        -- states.rs:412-458, cell 8
        let dec' := P.decEk.addChunk dec chunk
        match P.decEk.decodedPayload dec' with
        | some ek =>
            match CtSender.recvEk P core ek with
            | some core' => .ok ⟨msg.epoch - 1, none, .ekReceivedCt1Sampled core' enc⟩
            | none => .error .erroneousDataReceived
        | none => .ok ⟨msg.epoch - 1, none, .ct1Sampled core enc dec'⟩
    | .ct1Sampled core _ dec, .ekCt1Ack chunk =>
        -- states.rs:412-458, cell 9
        let dec' := P.decEk.addChunk dec chunk
        match P.decEk.decodedPayload dec' with
        | some ek =>
            match CtSender.recvEk P core ek with
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
        let dec' := P.decEk.addChunk dec chunk
        match P.decEk.decodedPayload dec' with
        | some ek =>
            match CtSender.recvEk P core ek with
            | some core' => .ok ⟨msg.epoch - 1, none, completeCt2 P auth core'⟩
            | none => .error .erroneousDataReceived
        | none => .ok ⟨msg.epoch - 1, none, .ct1Acknowledged core dec'⟩
    | .ct1Acknowledged core dec, .ekCt1Ack chunk =>
        -- states.rs:479-520, cell 15
        let dec' := P.decEk.addChunk dec chunk
        match P.decEk.decodedPayload dec' with
        | some ek =>
            match CtSender.recvEk P core ek with
            | some core' => .ok ⟨msg.epoch - 1, none, completeCt2 P auth core'⟩
            | none => .error .erroneousDataReceived
        | none => .ok ⟨msg.epoch - 1, none, .ct1Acknowledged core dec'⟩
    | .ct2Sampled _ _, _ =>
        -- states.rs:522-531, cell 16
        ignore
    | _, _ =>
        -- states.rs:275-533, cell 17
        ignore
-- ANCHOR_END: Chunked_recv

end SPQR.Chunked
