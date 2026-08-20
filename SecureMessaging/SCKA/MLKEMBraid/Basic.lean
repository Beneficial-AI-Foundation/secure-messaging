/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.ErasureCode.Streaming
import SecureMessaging.SCKA.MLKEMBraid.Authenticator

/-!
# ML-KEM Braid transition system

A Lean model of Signal's *The ML-KEM Braid Protocol*
([specification](https://signal.org/docs/specifications/mlkembraid/)): the message fields
and types of §2.3, the eleven states and their additional fields from §2.5, the
per-state `Send` and `Receive` procedures of §2.5, and `InitAlice` and `InitBob` of §2.6.
`MLKEMBraid.Construction` packages the transition system as an SCKA scheme.

Figure 1 on p. 10 of the PDF labels each state-machine edge with a number. The §2.5
pseudocode repeats that number as `# Transition (n)` immediately before the corresponding
state update. This file uses the same labels:

| Edge | State change | Event |
| ---: | --- | --- |
| 1 | `KeysUnsampled` → `KeysSampled` | Send: generate keys and start the header |
| 2 | `KeysSampled` → `HeaderSent` | Receive: first `ct₁` chunk |
| 3 | `HeaderSent` → `Ct1Received` | Receive: finish decoding `ct₁` |
| 4 | `Ct1Received` → `EkSentCt1Received` | Receive: first `ct₂` chunk |
| 5 | `EkSentCt1Received` → `NoHeaderReceived` | Receive: finish `ct₂` and advance |
| 6 | `NoHeaderReceived` → `HeaderReceived` | Receive: finish and verify the header |
| 7 | `HeaderReceived` → `Ct1Sampled` | Send: run `Encaps1` and start `ct₁` |
| 8 | `Ct1Sampled` → `Ct1Acknowledged` | Receive: acknowledgement before `ek_vector` |
| 9 | `Ct1Sampled` → `Ct2Sampled` | Receive: acknowledgement completes `ek_vector` |
| 10 | `Ct1Sampled` → `EkReceivedCt1Sampled` | Receive: finish `ek_vector` without ack |
| 11 | `Ct1Acknowledged` → `Ct2Sampled` | Receive: finish `ek_vector` after ack |
| 12 | `EkReceivedCt1Sampled` → `Ct2Sampled` | Receive: later ack; discard its chunk |
| 13 | `Ct2Sampled` → `KeysUnsampled` | Receive: next-epoch message |

Epochs are `ℕ`; a chunk is an indexed symbol `(ℕ × Sym)` produced by
`ErasureCodePayload.Streaming`. A decoder's payload type records what its stream
recovers, in place of the
`Decoder.new(message_size)` byte count of §2.2.

`send` stamps `msg.epoch = state.epoch` and returns `sending_epoch = state.epoch - 1`.
`receive` returns `receiving_epoch = state.epoch - 1` for the state it is called on,
except from `ct2Sampled`, where the report is read off the state after the transition, so
an accepted next-epoch message reports the entry epoch.

`receive` ignores any message that does not match a transition, leaving the state
unchanged and returning no output key. This includes ill-formed messages, unexpected
message types or epochs, and every message received in the `keysUnsampled` and
`headerReceived` states. An ignored message reports the entry epoch minus one.
-/

open ErasureCodePayload.Streaming

universe u

namespace MLKEMBraid

/-- The KEM value spaces and operations, header hash, epoch-key derivation, and four
erasure-coded streams used by the transition system. -/
-- ANCHOR: Braid_Parameters
structure Parameters (m : Type → Type u) where
  /-- `dk`: decapsulation key. -/
  Dk : Type
  /-- `ek_seed`: seed part of the encapsulation-key header. -/
  EkSeed : Type
  /-- `ek_vector`: vector part of the encapsulation key. -/
  EkVector : Type
  /-- `hek`: encapsulation-key hash carried in the header. -/
  Hek : Type
  /-- `encaps_secret`: state passed from the first encapsulation stage to the second. -/
  EncapsSecret : Type
  /-- `ct₁`: first ciphertext part. -/
  Ct1 : Type
  /-- `ct₂`: second ciphertext part. -/
  Ct2 : Type
  /-- KEM shared secret. -/
  SharedSecret : Type
  /-- Epoch key output by `KDF_OK`. -/
  EpochKey : Type
  /-- MAC tag. -/
  Mac : Type
  /-- Erasure-code symbol alphabet, shared by the four streams. -/
  Sym : Type
  /-- `KeyGen`, destructured as `(dk, ek_seed, ek_vector)`. -/
  keyGen : m (Dk × EkSeed × EkVector)
  /-- Header hash. -/
  hashEk : EkSeed → EkVector → Hek
  /-- `Encaps1(ek_seed, hek)`. -/
  encaps1 : EkSeed → Hek → m (EncapsSecret × Ct1 × SharedSecret)
  /-- `Encaps2(encaps_secret, ek_seed, ek_vector)`, determined by `encaps_secret`. -/
  encaps2 : EncapsSecret → EkSeed → EkVector → Ct2
  /-- `Decaps(dk, ct₁, ct₂)`, total. -/
  decaps : Dk → Ct1 → Ct2 → SharedSecret
  /-- `KDF_OK(shared_secret, epoch)`. -/
  kdfOK : SharedSecret → ℕ → EpochKey
  /-- Header stream, recovering `header ‖ mac`. -/
  ecpHdr : ErasureCodePayload ((EkSeed × Hek) × Mac) Sym
  /-- Encapsulation-key-vector stream. -/
  ecpEk : ErasureCodePayload EkVector Sym
  /-- `ct₁` stream. -/
  ecpCt1 : ErasureCodePayload Ct1 Sym
  /-- `ct₂` stream, recovering `ct₂ ‖ mac`. -/
  ecpCt2 : ErasureCodePayload (Ct2 × Mac) Sym
-- ANCHOR_END: Braid_Parameters

variable {m : Type → Type u} [Monad m] {Sym : Type} {P : Parameters m}
  {InitKey AuthState : Type}

-- ANCHOR: Braid_Message
/-- The message types. -/
inductive MessageType where
  /-- `None`: no payload. -/
  | none
  /-- `Hdr`: header-stream chunk. -/
  | hdr
  /-- `Ek`: encapsulation-key-vector chunk. -/
  | ek
  /-- `EkCt1Ack`: encapsulation-key chunk, and the sender has all of `ct₁`. -/
  | ekCt1Ack
  /-- `Ct1Ack`: the sender has all of `ct₁`, no payload. No transition sends or consumes
  it. -/
  | ct1Ack
  /-- `Ct1`: `ct₁`-stream chunk. -/
  | ct1
  /-- `Ct2`: `ct₂`-stream chunk. -/
  | ct2

/-- A protocol message: the epoch being negotiated, the type, and an
optional chunk. -/
structure Message (Sym : Type) where
  /-- `epoch`: the epoch being negotiated. -/
  epoch : ℕ
  /-- `type`: which stream, acknowledgment, or empty message this is. -/
  type : MessageType
  /-- `data`: the indexed erasure-code chunk, if any. -/
  data : Option (ℕ × Sym)

/-- The data-presence convention: `data` is present exactly when the type is
neither `None` nor `Ct1Ack`. `receive` tests it before state dispatch and ignores
messages that violate it. -/
def Message.wellFormed (msg : Message Sym) : Bool :=
  match msg.type with
  | .none | .ct1Ack => msg.data.isNone
  | .hdr | .ek | .ekCt1Ack | .ct1 | .ct2 => msg.data.isSome
-- ANCHOR_END: Braid_Message

/-- Receive failures: encapsulation-key integrity failure and rejection by either
authenticator verification. -/
-- ANCHOR: Braid_Failure
inductive Failure where
  /-- The received encapsulation-key vector does not hash to the stored `hek`. -/
  | ekIntegrity
  /-- `VfyHdr` rejected the header tag. -/
  | headerMac
  /-- `VfyCt` rejected the ciphertext tag. -/
  | ciphertextMac
-- ANCHOR_END: Braid_Failure
/-- The eleven protocol states. Every constructor carries an epoch and authenticator
state. -/
-- ANCHOR: Braid_State
inductive State (P : Parameters m) (AuthState : Type) where
  /-- "KeysUnsampled": no additional state. -/
  | keysUnsampled (epoch : ℕ) (auth : AuthState)
  /-- "KeysSampled": `dk`, `ek_vector`, `header_encoder`. -/
  | keysSampled (epoch : ℕ) (auth : AuthState) (dk : P.Dk) (ekVector : P.EkVector)
      (headerEncoder : EncoderState ((P.EkSeed × P.Hek) × P.Mac) P.Sym)
  /-- "HeaderSent": `dk`, `ct1_decoder`, `ek_encoder`. -/
  | headerSent (epoch : ℕ) (auth : AuthState) (dk : P.Dk)
      (ct1Decoder : DecoderState P.Ct1 P.Sym)
      (ekEncoder : EncoderState P.EkVector P.Sym)
  /-- "Ct1Received": `dk`, `ct1`, `ek_encoder`. -/
  | ct1Received (epoch : ℕ) (auth : AuthState) (dk : P.Dk) (ct1 : P.Ct1)
      (ekEncoder : EncoderState P.EkVector P.Sym)
  /-- "EkSentCt1Received": `dk`, `ct1`, `ct2_decoder`. -/
  | ekSentCt1Received (epoch : ℕ) (auth : AuthState) (dk : P.Dk) (ct1 : P.Ct1)
      (ct2Decoder : DecoderState (P.Ct2 × P.Mac) P.Sym)
  /-- "NoHeaderReceived": `header_decoder`. -/
  | noHeaderReceived (epoch : ℕ) (auth : AuthState)
      (headerDecoder : DecoderState ((P.EkSeed × P.Hek) × P.Mac) P.Sym)
  /-- "HeaderReceived": `ek_seed`, `hek`, `ek_decoder`. -/
  | headerReceived (epoch : ℕ) (auth : AuthState) (ekSeed : P.EkSeed) (hek : P.Hek)
      (ekDecoder : DecoderState P.EkVector P.Sym)
  /-- "Ct1Sampled": `ek_seed`, `hek`, `encaps_secret`, `ct1`, `ct1_encoder`, `ek_decoder`. -/
  | ct1Sampled (epoch : ℕ) (auth : AuthState) (ekSeed : P.EkSeed) (hek : P.Hek)
      (encapsSecret : P.EncapsSecret) (ct1 : P.Ct1)
      (ct1Encoder : EncoderState P.Ct1 P.Sym)
      (ekDecoder : DecoderState P.EkVector P.Sym)
  /-- "EkReceivedCt1Sampled": `encaps_secret`, `ct1`, `ek_seed`, `ek_vector`,
  `ct1_encoder`. -/
  | ekReceivedCt1Sampled (epoch : ℕ) (auth : AuthState)
      (encapsSecret : P.EncapsSecret) (ct1 : P.Ct1) (ekSeed : P.EkSeed)
      (ekVector : P.EkVector) (ct1Encoder : EncoderState P.Ct1 P.Sym)
  /-- "Ct1Acknowledged": `ek_seed`, `hek`, `encaps_secret`, `ct1`, `ek_decoder`. -/
  | ct1Acknowledged (epoch : ℕ) (auth : AuthState) (ekSeed : P.EkSeed)
      (hek : P.Hek) (encapsSecret : P.EncapsSecret) (ct1 : P.Ct1)
      (ekDecoder : DecoderState P.EkVector P.Sym)
  /-- "Ct2Sampled": `ct2_encoder`. -/
  | ct2Sampled (epoch : ℕ) (auth : AuthState)
      (ct2Encoder : EncoderState (P.Ct2 × P.Mac) P.Sym)

/-- The epoch stored as the first field of every state constructor. -/
def State.epoch : State P AuthState → ℕ
  | .keysUnsampled e .. => e
  | .keysSampled e .. => e
  | .headerSent e .. => e
  | .ct1Received e .. => e
  | .ekSentCt1Received e .. => e
  | .noHeaderReceived e .. => e
  | .headerReceived e .. => e
  | .ct1Sampled e .. => e
  | .ekReceivedCt1Sampled e .. => e
  | .ct1Acknowledged e .. => e
  | .ct2Sampled e .. => e
-- ANCHOR_END: Braid_State

-- ANCHOR: Braid_Results
/-- The `Send` output `(msg, sending_epoch, output_key)` with the successor state. -/
structure SendResult (P : Parameters m) (AuthState : Type) where
  /-- `msg`: the message sent. -/
  msg : Message P.Sym
  /-- `sending_epoch`: the latest epoch the other party is guaranteed to know on receipt
  of `msg`. -/
  sendingEpoch : ℕ
  /-- `output_key`: the epoch and epoch key derived by this send, if any. -/
  outputKey : Option (ℕ × P.EpochKey)
  /-- The state after the send. -/
  state : State P AuthState

/-- The `Receive` output `(receiving_epoch, output_key)` with the successor state. -/
structure RecvResult (P : Parameters m) (AuthState : Type) where
  /-- `receiving_epoch`: the `sending_epoch` the other party output when it produced the
  message. -/
  receivingEpoch : ℕ
  /-- `output_key`: the epoch and epoch key derived by this receive, if any. -/
  outputKey : Option (ℕ × P.EpochKey)
  /-- The state after the receive. -/
  state : State P AuthState
-- ANCHOR_END: Braid_Results

/-- The protocol send transition for each state. -/
def send (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      (P.EkSeed × P.Hek) (P.Ct1 × P.Ct2) P.Mac)
    (st : State P AuthState) : m (SendResult P AuthState) :=
  match st with
  | .keysUnsampled e a => do
      -- Figure 1, edge 1: sample the keys and start streaming the authenticated header.
      let (dk, ekSeed, ekVector) ← P.keyGen
      let hek := P.hashEk ekSeed ekVector
      let tag := auth.macHeader a e (ekSeed, hek)
      let (chunk, enc) := (EncoderState.init P.ecpHdr ((ekSeed, hek), tag)).nextChunk
      pure { msg := { epoch := e, type := .hdr, data := some chunk },
             sendingEpoch := e - 1, outputKey := none,
             state := .keysSampled e a dk ekVector enc }
  | .keysSampled e a dk ekVector headerEncoder =>
      let (chunk, enc) := headerEncoder.nextChunk
      pure { msg := { epoch := e, type := .hdr, data := some chunk },
             sendingEpoch := e - 1, outputKey := none,
             state := .keysSampled e a dk ekVector enc }
  | .headerSent e a dk ct1Decoder ekEncoder =>
      let (chunk, enc) := ekEncoder.nextChunk
      pure { msg := { epoch := e, type := .ek, data := some chunk },
             sendingEpoch := e - 1, outputKey := none,
             state := .headerSent e a dk ct1Decoder enc }
  | .ct1Received e a dk ct1 ekEncoder =>
      let (chunk, enc) := ekEncoder.nextChunk
      pure { msg := { epoch := e, type := .ekCt1Ack, data := some chunk },
             sendingEpoch := e - 1, outputKey := none,
             state := .ct1Received e a dk ct1 enc }
  | .ekSentCt1Received e .. =>
      pure { msg := { epoch := e, type := .none, data := none },
             sendingEpoch := e - 1, outputKey := none, state := st }
  | .noHeaderReceived e .. =>
      pure { msg := { epoch := e, type := .none, data := none },
             sendingEpoch := e - 1, outputKey := none, state := st }
  | .headerReceived e a ekSeed hek ekDecoder => do
      -- Figure 1, edge 7: `Encaps1`, `KDF_OK`, `Update`, and the first chunk of `ct₁`.
      let (encapsSecret, ct1, sharedSecret) ← P.encaps1 ekSeed hek
      let ik := P.kdfOK sharedSecret e
      let (chunk, enc) := (EncoderState.init P.ecpCt1 ct1).nextChunk
      pure { msg := { epoch := e, type := .ct1, data := some chunk },
             sendingEpoch := e - 1, outputKey := some (e, ik),
             state := .ct1Sampled e (auth.update a e ik) ekSeed hek encapsSecret ct1 enc
               ekDecoder }
  | .ct1Sampled e a ekSeed hek encapsSecret ct1 ct1Encoder ekDecoder =>
      let (chunk, enc) := ct1Encoder.nextChunk
      pure { msg := { epoch := e, type := .ct1, data := some chunk },
             sendingEpoch := e - 1, outputKey := none,
             state := .ct1Sampled e a ekSeed hek encapsSecret ct1 enc ekDecoder }
  | .ekReceivedCt1Sampled e a encapsSecret ct1 ekSeed ekVector ct1Encoder =>
      let (chunk, enc) := ct1Encoder.nextChunk
      pure { msg := { epoch := e, type := .ct1, data := some chunk },
             sendingEpoch := e - 1, outputKey := none,
             state := .ekReceivedCt1Sampled e a encapsSecret ct1 ekSeed ekVector enc }
  | .ct1Acknowledged e .. =>
      pure { msg := { epoch := e, type := .none, data := none },
             sendingEpoch := e - 1, outputKey := none, state := st }
  | .ct2Sampled e a ct2Encoder =>
      let (chunk, enc) := ct2Encoder.nextChunk
      pure { msg := { epoch := e, type := .ct2, data := some chunk },
             sendingEpoch := e - 1, outputKey := none, state := .ct2Sampled e a enc }

/-- The protocol receive transition. A message failing `Message.wellFormed` is
ignored before dispatch; each state then guards on `msg.epoch` and `msg.type`, and an
input matching no guard is ignored. -/
def receive (P : Parameters m) [DecidableEq P.Sym] [DecidableEq P.Hek]
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      (P.EkSeed × P.Hek) (P.Ct1 × P.Ct2) P.Mac)
    (st : State P AuthState) (msg : Message P.Sym) :
    Except Failure (RecvResult P AuthState) :=
  let ignore : Except Failure (RecvResult P AuthState) :=
    .ok { receivingEpoch := st.epoch - 1, outputKey := none, state := st }
  if !msg.wellFormed then
    ignore
  else
    match st with
    | .keysUnsampled .. => ignore
    | .keysSampled e a dk ekVector _ =>
        match msg.type, msg.data with
        | .ct1, some chunk =>
            if msg.epoch = e then
              -- Figure 1, edge 2: store the first `ct₁` chunk without checking
              -- completeness, then start streaming `ek_vector`.
              .ok { receivingEpoch := e - 1, outputKey := none,
                    state := .headerSent e a dk ((DecoderState.empty P.ecpCt1).addChunk chunk)
                      (EncoderState.init P.ecpEk ekVector) }
            else ignore
        | _, _ => ignore
    | .headerSent e a dk ct1Decoder ekEncoder =>
        match msg.type, msg.data with
        | .ct1, some chunk =>
            if msg.epoch = e then
              let dec := ct1Decoder.addChunk chunk
              match dec.decodedPayload with
              | some ct1 =>
                  -- Figure 1, edge 3: `ct₁` decoding completes.
                  .ok { receivingEpoch := e - 1, outputKey := none,
                        state := .ct1Received e a dk ct1 ekEncoder }
              | none =>
                  .ok { receivingEpoch := e - 1, outputKey := none,
                        state := .headerSent e a dk dec ekEncoder }
            else ignore
        | _, _ => ignore
    | .ct1Received e a dk ct1 _ =>
        match msg.type, msg.data with
        | .ct2, some chunk =>
            if msg.epoch = e then
              -- Figure 1, edge 4: store the first `ct₂` chunk without a completeness check.
              .ok { receivingEpoch := e - 1, outputKey := none,
                    state := .ekSentCt1Received e a dk ct1
                      ((DecoderState.empty P.ecpCt2).addChunk chunk) }
            else ignore
        | _, _ => ignore
    | .ekSentCt1Received e a dk ct1 ct2Decoder =>
        match msg.type, msg.data with
        | .ct2, some chunk =>
            if msg.epoch = e then
              let dec := ct2Decoder.addChunk chunk
              match dec.decodedPayload with
              | some (ct2, tag) =>
                  let ik := P.kdfOK (P.decaps dk ct1 ct2) e
                  let auth' := auth.update a e ik
                  if auth.verifyCiphertext auth' e (ct1, ct2) tag then
                    -- Figure 1, edge 5: output the key for the entry epoch and advance.
                    .ok { receivingEpoch := e - 1, outputKey := some (e, ik),
                          state := .noHeaderReceived (e + 1) auth'
                            (DecoderState.empty P.ecpHdr) }
                  else .error .ciphertextMac
              | none =>
                  .ok { receivingEpoch := e - 1, outputKey := none,
                        state := .ekSentCt1Received e a dk ct1 dec }
            else ignore
        | _, _ => ignore
    | .noHeaderReceived e a headerDecoder =>
        match msg.type, msg.data with
        | .hdr, some chunk =>
            if msg.epoch = e then
              let dec := headerDecoder.addChunk chunk
              match dec.decodedPayload with
              | some ((ekSeed, hek), tag) =>
                  if auth.verifyHeader a e (ekSeed, hek) tag then
                    -- Figure 1, edge 6: authenticated header decoding completes.
                    .ok { receivingEpoch := e - 1, outputKey := none,
                          state := .headerReceived e a ekSeed hek
                            (DecoderState.empty P.ecpEk) }
                  else .error .headerMac
              | none =>
                  .ok { receivingEpoch := e - 1, outputKey := none,
                        state := .noHeaderReceived e a dec }
            else ignore
        | _, _ => ignore
    | .headerReceived .. => ignore
    | .ct1Sampled e a ekSeed hek encapsSecret ct1 ct1Encoder ekDecoder =>
        match msg.type, msg.data with
        | .ek, some chunk =>
            if msg.epoch = e then
              let dec := ekDecoder.addChunk chunk
              match dec.decodedPayload with
              | some ekVector =>
                  if P.hashEk ekSeed ekVector = hek then
                    -- Figure 1, edge 10: vector decoding completes without acknowledgement.
                    .ok { receivingEpoch := e - 1, outputKey := none,
                          state := .ekReceivedCt1Sampled e a encapsSecret ct1 ekSeed
                            ekVector ct1Encoder }
                  else .error .ekIntegrity
              | none =>
                  .ok { receivingEpoch := e - 1, outputKey := none,
                        state := .ct1Sampled e a ekSeed hek encapsSecret ct1 ct1Encoder dec }
            else ignore
        | .ekCt1Ack, some chunk =>
            if msg.epoch = e then
              let dec := ekDecoder.addChunk chunk
              match dec.decodedPayload with
              | some ekVector =>
                  if P.hashEk ekSeed ekVector = hek then
                    -- Figure 1, edge 9: run `Encaps2`, then stream the authenticated `ct₂`.
                    let ct2 := P.encaps2 encapsSecret ekSeed ekVector
                    let tag := auth.macCiphertext a e (ct1, ct2)
                    .ok { receivingEpoch := e - 1, outputKey := none,
                          state := .ct2Sampled e a (EncoderState.init P.ecpCt2 (ct2, tag)) }
                  else .error .ekIntegrity
              | none =>
                  -- Figure 1, edge 8: acknowledgement precedes vector completion.
                  .ok { receivingEpoch := e - 1, outputKey := none,
                        state := .ct1Acknowledged e a ekSeed hek encapsSecret ct1 dec }
            else ignore
        | _, _ => ignore
    | .ekReceivedCt1Sampled e a encapsSecret ct1 ekSeed ekVector _ =>
        match msg.type, msg.data with
        | .ekCt1Ack, some _ =>
            if msg.epoch = e then
              -- Figure 1, edge 12: the guard reads no chunk, so the carried one is discarded.
              let ct2 := P.encaps2 encapsSecret ekSeed ekVector
              let tag := auth.macCiphertext a e (ct1, ct2)
              .ok { receivingEpoch := e - 1, outputKey := none,
                    state := .ct2Sampled e a (EncoderState.init P.ecpCt2 (ct2, tag)) }
            else ignore
        | _, _ => ignore
    | .ct1Acknowledged e a ekSeed hek encapsSecret ct1 ekDecoder =>
        match msg.type, msg.data with
        | .ekCt1Ack, some chunk =>
            if msg.epoch = e then
              let dec := ekDecoder.addChunk chunk
              match dec.decodedPayload with
              | some ekVector =>
                  if P.hashEk ekSeed ekVector = hek then
                    -- Figure 1, edge 11: vector decoding completes after acknowledgement.
                    let ct2 := P.encaps2 encapsSecret ekSeed ekVector
                    let tag := auth.macCiphertext a e (ct1, ct2)
                    .ok { receivingEpoch := e - 1, outputKey := none,
                          state := .ct2Sampled e a (EncoderState.init P.ecpCt2 (ct2, tag)) }
                  else .error .ekIntegrity
              | none =>
                  .ok { receivingEpoch := e - 1, outputKey := none,
                        state := .ct1Acknowledged e a ekSeed hek encapsSecret ct1 dec }
            else ignore
        | _, _ => ignore
    | .ct2Sampled e a _ =>
        if msg.epoch = e + 1 then
          -- Figure 1, edge 13: read the report from the post-transition state.
          .ok { receivingEpoch := e, outputKey := none, state := .keysUnsampled (e + 1) a }
        else ignore

-- ANCHOR: Braid_init
/-- Alice's initial state: epoch `1`, an initialized authenticator, and no sampled keys. -/
def initA (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      (P.EkSeed × P.Hek) (P.Ct1 × P.Ct2) P.Mac)
    (ik : InitKey) : State P AuthState :=
  .keysUnsampled 1 (auth.init ik 1)

/-- Bob's initial state: epoch `1`, an initialized authenticator, and an empty header
decoder. -/
def initB (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      (P.EkSeed × P.Hek) (P.Ct1 × P.Ct2) P.Mac)
    (ik : InitKey) : State P AuthState :=
  .noHeaderReceived 1 (auth.init ik 1) (DecoderState.empty P.ecpHdr)
-- ANCHOR_END: Braid_init

end MLKEMBraid
