/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.ErasureCode.Streaming
import SecureMessaging.KEM.IncrementalKEM.Defs
import SecureMessaging.SCKA.MLKEMBraid.Authenticator

/-!
# ML-KEM Braid transition system

A Lean model of Signal's *The ML-KEM Braid Protocol*
([specification](https://signal.org/docs/specifications/mlkembraid/)): the message fields
and types of §2.3, the eleven states and their additional fields from §2.5, the
per-state `Send` and `Receive` procedures of §2.5, and `InitAlice` and `InitBob` of §2.6.
`MLKEMBraid.Construction` packages the transition system as an SCKA scheme.

The trace and table use the edge numbers from Figure 1 and §2.5.

```text
Initialization: A = KeysUnsampled(1); B = NoHeaderReceived(1).
One epoch: A sends an encapsulation key; B returns the corresponding ciphertext.

A (encapsulation-key sender)                       B (ciphertext sender)
────────────────────────────                       ─────────────────────
KeysUnsampled                                      NoHeaderReceived

send [1]:
  (pk, sk) ← KeyGen
  hdr := toHeader pk; vec := toVector pk
  state := KeysSampled
             ───────── authenticated Hdr chunks ─────────▶
                                                   receive [6], once Hdr decodes:
                                                     verify header MAC
                                                     state := HeaderReceived

                                                   send [7]:
                                                     (encapsState, ct1, k) ← Encaps1 hdr
                                                     output (e, KDF_OK k e)
                                                     state := Ct1Sampled
             ◀──────────────── Ct1 chunks ────────────────

receive first Ct1 [2]:
  state := HeaderSent
             ───────────────── Ek chunks ─────────────────▶
receive Ct1 complete [3]:
  state := Ct1Received
             ────────────── EkCt1Ack chunks ──────────────▶

                                                   The Ek/ack race:
                                                     [8] ack first, vec incomplete
                                                         → Ct1Acknowledged
                                                    [11] later vec → Ct2Sampled
                                                     [9] ack completes vec → Ct2Sampled
                                                    [10] vec first → EkReceivedCt1Sampled
                                                    [12] later ack → Ct2Sampled
                                                   Each completed path runs Encaps2.
             ◀──────────────── Ct2 chunks ────────────────

receive first Ct2 [4]:
  state := EkSentCt1Received
receive Ct2 complete [5]:
  k ← Decaps(sk, ct1 || ct2); verify ciphertext MAC
  output (e, KDF_OK k e)
  state := NoHeaderReceived (e + 1)
             ─────────── epoch-(e+1) message ─────────────▶
                                                   receive [13]:
                                                     state := KeysUnsampled (e + 1)

The roles are reversed for the next epoch.
```

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

Epochs are `ℕ`; each chunk is an indexed symbol `(ℕ × Sym)`. Payload types determine the
value recovered by each stream. `send` stamps each message with the current state epoch and
reports that epoch minus one. `receive` normally reports the entry epoch minus one; edge 13
reports the entry epoch as it advances to the next. An input matching no guard leaves the
state unchanged and produces no output key.
-/

open ErasureCodePayload.Streaming

universe u

namespace MLKEMBraid

/-- Parameters for the transition system: an incremental KEM, pure implementations of the
KEM operations used by `receive`, epoch-key derivation, and four erasure-coded streams. -/
-- ANCHOR: Braid_Parameters
structure Parameters (m : Type → Type u) [Monad m] where
  /-- KEM shared secret. -/
  K : Type
  /-- Encapsulation key. -/
  PK : Type
  /-- Decapsulation key. -/
  SK : Type
  /-- Ciphertext. -/
  C : Type
  /-- The key-encapsulation mechanism. -/
  kem : KEMScheme m K PK SK C
  /-- The incremental KEM structure. -/
  inc : kem.IncrementalStructure
  /-- Pure decapsulation agreeing with `kem.decaps`. -/
  hDet : kem.DeterministicDecaps
  /-- Pure second-stage encapsulation agreeing with `inc.encaps2`. -/
  hEnc2 : inc.DeterministicEncaps2
  /-- Epoch key output by `KDF_OK`. -/
  EpochKey : Type
  /-- MAC tag. -/
  Mac : Type
  /-- Erasure-code symbol alphabet, shared by the four streams. -/
  Sym : Type
  /-- `KDF_OK(shared_secret, epoch)`. -/
  kdfOK : K → ℕ → EpochKey
  /-- Header stream, recovering `header ‖ mac`. -/
  ecpHdr : ErasureCodePayload (inc.PKheader × Mac) Sym
  /-- Encapsulation-key-vector stream. -/
  ecpEk : ErasureCodePayload inc.PKvector Sym
  /-- `ct₁` stream. -/
  ecpCt1 : ErasureCodePayload inc.C₁ Sym
  /-- `ct₂` stream, recovering `ct₂ ‖ mac`. -/
  ecpCt2 : ErasureCodePayload (inc.C₂ × Mac) Sym
-- ANCHOR_END: Braid_Parameters

variable {m : Type → Type u} [Monad m] {Sym : Type} {P : Parameters m}
  {InitKey AuthState : Type}

/-- The message types. -/
-- ANCHOR: Braid_MessageType
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
-- ANCHOR_END: Braid_MessageType

/-- A protocol message containing the negotiated epoch, message type, and optional chunk. -/
-- ANCHOR: Braid_Message
structure Message (Sym : Type) where
  /-- `epoch`: the epoch being negotiated. -/
  epoch : ℕ
  /-- `type`: which stream, acknowledgment, or empty message this is. -/
  type : MessageType
  /-- `data`: the indexed erasure-code chunk, if any. -/
  data : Option (ℕ × Sym)
-- ANCHOR_END: Braid_Message

/-- Whether `data` is present exactly when the message type carries a chunk. -/
-- ANCHOR: Braid_Message_wellFormed
def Message.wellFormed (msg : Message Sym) : Bool
-- ANCHOR_END: Braid_Message_wellFormed
    :=
  match msg.type with
  | .none | .ct1Ack => msg.data.isNone
  | .hdr | .ek | .ekCt1Ack | .ct1 | .ct2 => msg.data.isSome

/-- Receive failures. -/
-- ANCHOR: Braid_Failure
inductive Failure where
  /-- The received encapsulation-key vector fails `validPK`. -/
  | ekIntegrity
  /-- `VfyHdr` rejected the header tag. -/
  | headerMac
  /-- `VfyCt` rejected the ciphertext tag. -/
  | ciphertextMac
  /-- Deterministic decapsulation rejected the ciphertext. This cannot occur for ML-KEM. -/
  | decapsReject
-- ANCHOR_END: Braid_Failure
/-- The eleven protocol states, each with an epoch and authenticator state. -/
-- ANCHOR: Braid_State
inductive State (P : Parameters m) (AuthState : Type) where
  /-- "KeysUnsampled": no additional state. -/
  | keysUnsampled (epoch : ℕ) (auth : AuthState)
  /-- "KeysSampled": `sk`, `ek_vector`, `header_encoder`. -/
  | keysSampled (epoch : ℕ) (auth : AuthState) (sk : P.SK) (ekVector : P.inc.PKvector)
      (headerEncoder : EncoderState (P.inc.PKheader × P.Mac) P.Sym)
  /-- "HeaderSent": `sk`, `ct1_decoder`, `ek_encoder`. -/
  | headerSent (epoch : ℕ) (auth : AuthState) (sk : P.SK)
      (ct1Decoder : DecoderState P.inc.C₁ P.Sym)
      (ekEncoder : EncoderState P.inc.PKvector P.Sym)
  /-- "Ct1Received": `sk`, `ct1`, `ek_encoder`. -/
  | ct1Received (epoch : ℕ) (auth : AuthState) (sk : P.SK) (ct1 : P.inc.C₁)
      (ekEncoder : EncoderState P.inc.PKvector P.Sym)
  /-- "EkSentCt1Received": `sk`, `ct1`, `ct2_decoder`. -/
  | ekSentCt1Received (epoch : ℕ) (auth : AuthState) (sk : P.SK) (ct1 : P.inc.C₁)
      (ct2Decoder : DecoderState (P.inc.C₂ × P.Mac) P.Sym)
  /-- "NoHeaderReceived": `header_decoder`. -/
  | noHeaderReceived (epoch : ℕ) (auth : AuthState)
      (headerDecoder : DecoderState (P.inc.PKheader × P.Mac) P.Sym)
  /-- "HeaderReceived": `header`, `ek_decoder`. -/
  | headerReceived (epoch : ℕ) (auth : AuthState) (header : P.inc.PKheader)
      (ekDecoder : DecoderState P.inc.PKvector P.Sym)
  /-- "Ct1Sampled": `header`, `encaps_state`, `ct1`, `ct1_encoder`, `ek_decoder`. -/
  | ct1Sampled (epoch : ℕ) (auth : AuthState) (header : P.inc.PKheader)
      (encapsState : P.inc.St) (ct1 : P.inc.C₁)
      (ct1Encoder : EncoderState P.inc.C₁ P.Sym)
      (ekDecoder : DecoderState P.inc.PKvector P.Sym)
  /-- "EkReceivedCt1Sampled": `encaps_state`, `ct1`, `header`, `ek_vector`,
  `ct1_encoder`. -/
  | ekReceivedCt1Sampled (epoch : ℕ) (auth : AuthState)
      (encapsState : P.inc.St) (ct1 : P.inc.C₁) (header : P.inc.PKheader)
      (ekVector : P.inc.PKvector) (ct1Encoder : EncoderState P.inc.C₁ P.Sym)
  /-- "Ct1Acknowledged": `header`, `encaps_state`, `ct1`, `ek_decoder`. -/
  | ct1Acknowledged (epoch : ℕ) (auth : AuthState) (header : P.inc.PKheader)
      (encapsState : P.inc.St) (ct1 : P.inc.C₁)
      (ekDecoder : DecoderState P.inc.PKvector P.Sym)
  /-- "Ct2Sampled": `ct2_encoder`. -/
  | ct2Sampled (epoch : ℕ) (auth : AuthState)
      (ct2Encoder : EncoderState (P.inc.C₂ × P.Mac) P.Sym)
-- ANCHOR_END: Braid_State

/-- The epoch stored in a protocol state. -/
-- ANCHOR: Braid_State_epoch
def State.epoch : State P AuthState → ℕ
-- ANCHOR_END: Braid_State_epoch
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

/-- The `Send` output `(msg, sending_epoch, output_key)` with the successor state. -/
-- ANCHOR: Braid_SendResult
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
-- ANCHOR_END: Braid_SendResult

/-- The `Receive` output `(receiving_epoch, output_key)` with the successor state. -/
-- ANCHOR: Braid_RecvResult
structure RecvResult (P : Parameters m) (AuthState : Type) where
  /-- `receiving_epoch`: the `sending_epoch` the other party output when it produced the
  message. -/
  receivingEpoch : ℕ
  /-- `output_key`: the epoch and epoch key derived by this receive, if any. -/
  outputKey : Option (ℕ × P.EpochKey)
  /-- The state after the receive. -/
  state : State P AuthState
-- ANCHOR_END: Braid_RecvResult

/-- The protocol send transition for each state. -/
-- ANCHOR: Braid_send
def send (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : State P AuthState) : m (SendResult P AuthState)
-- ANCHOR_END: Braid_send
    :=
  match st with
  | .keysUnsampled e a => do
      -- Figure 1, edge 1: sample the keys and start streaming the authenticated header.
      let (pk, sk) ← P.kem.keygen
      let hdr := P.inc.toHeader pk
      let vec := P.inc.toVector pk
      let tag := auth.macHeader a e hdr
      let (chunk, enc) := (EncoderState.init P.ecpHdr (hdr, tag)).nextChunk
      pure { msg := { epoch := e, type := .hdr, data := some chunk },
             sendingEpoch := e - 1, outputKey := none,
             state := .keysSampled e a sk vec enc }
  | .keysSampled e a sk ekVector headerEncoder =>
      let (chunk, enc) := headerEncoder.nextChunk
      pure { msg := { epoch := e, type := .hdr, data := some chunk },
             sendingEpoch := e - 1, outputKey := none,
             state := .keysSampled e a sk ekVector enc }
  | .headerSent e a sk ct1Decoder ekEncoder =>
      let (chunk, enc) := ekEncoder.nextChunk
      pure { msg := { epoch := e, type := .ek, data := some chunk },
             sendingEpoch := e - 1, outputKey := none,
             state := .headerSent e a sk ct1Decoder enc }
  | .ct1Received e a sk ct1 ekEncoder =>
      let (chunk, enc) := ekEncoder.nextChunk
      pure { msg := { epoch := e, type := .ekCt1Ack, data := some chunk },
             sendingEpoch := e - 1, outputKey := none,
             state := .ct1Received e a sk ct1 enc }
  | .ekSentCt1Received e .. =>
      pure { msg := { epoch := e, type := .none, data := none },
             sendingEpoch := e - 1, outputKey := none, state := st }
  | .noHeaderReceived e .. =>
      pure { msg := { epoch := e, type := .none, data := none },
             sendingEpoch := e - 1, outputKey := none, state := st }
  | .headerReceived e a hdr ekDecoder => do
      -- Figure 1, edge 7: `Encaps1`, `KDF_OK`, `Update`, and the first chunk of `ct₁`.
      let (encapsState, ct1, k) ← P.inc.encaps1 hdr
      let ik := P.kdfOK k e
      let (chunk, enc) := (EncoderState.init P.ecpCt1 ct1).nextChunk
      pure { msg := { epoch := e, type := .ct1, data := some chunk },
             sendingEpoch := e - 1, outputKey := some (e, ik),
             state := .ct1Sampled e (auth.update a e ik) hdr encapsState ct1 enc ekDecoder }
  | .ct1Sampled e a hdr encapsState ct1 ct1Encoder ekDecoder =>
      let (chunk, enc) := ct1Encoder.nextChunk
      pure { msg := { epoch := e, type := .ct1, data := some chunk },
             sendingEpoch := e - 1, outputKey := none,
             state := .ct1Sampled e a hdr encapsState ct1 enc ekDecoder }
  | .ekReceivedCt1Sampled e a encapsState ct1 hdr ekVector ct1Encoder =>
      let (chunk, enc) := ct1Encoder.nextChunk
      pure { msg := { epoch := e, type := .ct1, data := some chunk },
             sendingEpoch := e - 1, outputKey := none,
             state := .ekReceivedCt1Sampled e a encapsState ct1 hdr ekVector enc }
  | .ct1Acknowledged e .. =>
      pure { msg := { epoch := e, type := .none, data := none },
             sendingEpoch := e - 1, outputKey := none, state := st }
  | .ct2Sampled e a ct2Encoder =>
      let (chunk, enc) := ct2Encoder.nextChunk
      pure { msg := { epoch := e, type := .ct2, data := some chunk },
             sendingEpoch := e - 1, outputKey := none, state := .ct2Sampled e a enc }

/-- Receive a message. Ill-formed messages and messages that fail the current state's epoch
or type guards are ignored. -/
-- ANCHOR: Braid_receive
def receive (P : Parameters m) [DecidableEq P.Sym]
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : State P AuthState) (msg : Message P.Sym) :
    Except Failure (RecvResult P AuthState)
-- ANCHOR_END: Braid_receive
    :=
  let ignore : Except Failure (RecvResult P AuthState) :=
    .ok { receivingEpoch := st.epoch - 1, outputKey := none, state := st }
  if !msg.wellFormed then
    ignore
  else
    match st with
    | .keysUnsampled .. => ignore
    | .keysSampled e a sk ekVector _ =>
        match msg.type, msg.data with
        | .ct1, some chunk =>
            if msg.epoch = e then
              -- Figure 1, edge 2: store the first `ct₁` chunk without checking
              -- completeness, then start streaming `ek_vector`.
              .ok { receivingEpoch := e - 1, outputKey := none,
                    state := .headerSent e a sk ((DecoderState.empty P.ecpCt1).addChunk chunk)
                      (EncoderState.init P.ecpEk ekVector) }
            else ignore
        | _, _ => ignore
    | .headerSent e a sk ct1Decoder ekEncoder =>
        match msg.type, msg.data with
        | .ct1, some chunk =>
            if msg.epoch = e then
              let dec := ct1Decoder.addChunk chunk
              match dec.decodedPayload with
              | some ct1 =>
                  -- Figure 1, edge 3: `ct₁` decoding completes.
                  .ok { receivingEpoch := e - 1, outputKey := none,
                        state := .ct1Received e a sk ct1 ekEncoder }
              | none =>
                  .ok { receivingEpoch := e - 1, outputKey := none,
                        state := .headerSent e a sk dec ekEncoder }
            else ignore
        | _, _ => ignore
    | .ct1Received e a sk ct1 _ =>
        match msg.type, msg.data with
        | .ct2, some chunk =>
            if msg.epoch = e then
              -- Figure 1, edge 4: store the first `ct₂` chunk without a completeness check.
              .ok { receivingEpoch := e - 1, outputKey := none,
                    state := .ekSentCt1Received e a sk ct1
                      ((DecoderState.empty P.ecpCt2).addChunk chunk) }
            else ignore
        | _, _ => ignore
    | .ekSentCt1Received e a sk ct1 ct2Decoder =>
        match msg.type, msg.data with
        | .ct2, some chunk =>
            if msg.epoch = e then
              let dec := ct2Decoder.addChunk chunk
              match dec.decodedPayload with
              | some (ct2, tag) =>
                  match P.hDet.decapsDet sk (P.inc.splitC.symm (ct1, ct2)) with
                  | none => .error .decapsReject
                  | some k =>
                      let ik := P.kdfOK k e
                      let auth' := auth.update a e ik
                      if auth.verifyCiphertext auth' e (ct1, ct2) tag then
                        -- Figure 1, edge 5: output the key for the entry epoch and advance.
                        .ok { receivingEpoch := e - 1, outputKey := some (e, ik),
                              state := .noHeaderReceived (e + 1) auth'
                                (DecoderState.empty P.ecpHdr) }
                      else .error .ciphertextMac
              | none =>
                  .ok { receivingEpoch := e - 1, outputKey := none,
                        state := .ekSentCt1Received e a sk ct1 dec }
            else ignore
        | _, _ => ignore
    | .noHeaderReceived e a headerDecoder =>
        match msg.type, msg.data with
        | .hdr, some chunk =>
            if msg.epoch = e then
              let dec := headerDecoder.addChunk chunk
              match dec.decodedPayload with
              | some (hdr, tag) =>
                  if auth.verifyHeader a e hdr tag then
                    -- Figure 1, edge 6: authenticated header decoding completes.
                    .ok { receivingEpoch := e - 1, outputKey := none,
                          state := .headerReceived e a hdr (DecoderState.empty P.ecpEk) }
                  else .error .headerMac
              | none =>
                  .ok { receivingEpoch := e - 1, outputKey := none,
                        state := .noHeaderReceived e a dec }
            else ignore
        | _, _ => ignore
    | .headerReceived .. => ignore
    | .ct1Sampled e a hdr encapsState ct1 ct1Encoder ekDecoder =>
        match msg.type, msg.data with
        | .ek, some chunk =>
            if msg.epoch = e then
              let dec := ekDecoder.addChunk chunk
              match dec.decodedPayload with
              | some ekVector =>
                  if P.inc.validPK hdr ekVector then
                    -- Figure 1, edge 10: vector decoding completes without acknowledgement.
                    .ok { receivingEpoch := e - 1, outputKey := none,
                          state := .ekReceivedCt1Sampled e a encapsState ct1 hdr
                            ekVector ct1Encoder }
                  else .error .ekIntegrity
              | none =>
                  .ok { receivingEpoch := e - 1, outputKey := none,
                        state := .ct1Sampled e a hdr encapsState ct1 ct1Encoder dec }
            else ignore
        | .ekCt1Ack, some chunk =>
            if msg.epoch = e then
              let dec := ekDecoder.addChunk chunk
              match dec.decodedPayload with
              | some ekVector =>
                  if P.inc.validPK hdr ekVector then
                    -- Figure 1, edge 9: run `Encaps2`, then stream the authenticated `ct₂`.
                    let ct2 := P.hEnc2.encaps2Det encapsState hdr ekVector
                    let tag := auth.macCiphertext a e (ct1, ct2)
                    .ok { receivingEpoch := e - 1, outputKey := none,
                          state := .ct2Sampled e a (EncoderState.init P.ecpCt2 (ct2, tag)) }
                  else .error .ekIntegrity
              | none =>
                  -- Figure 1, edge 8: acknowledgement precedes vector completion.
                  .ok { receivingEpoch := e - 1, outputKey := none,
                        state := .ct1Acknowledged e a hdr encapsState ct1 dec }
            else ignore
        | _, _ => ignore
    | .ekReceivedCt1Sampled e a encapsState ct1 hdr ekVector _ =>
        match msg.type, msg.data with
        | .ekCt1Ack, some _ =>
            if msg.epoch = e then
              -- Figure 1, edge 12: the guard reads no chunk, so the carried one is discarded.
              let ct2 := P.hEnc2.encaps2Det encapsState hdr ekVector
              let tag := auth.macCiphertext a e (ct1, ct2)
              .ok { receivingEpoch := e - 1, outputKey := none,
                    state := .ct2Sampled e a (EncoderState.init P.ecpCt2 (ct2, tag)) }
            else ignore
        | _, _ => ignore
    | .ct1Acknowledged e a hdr encapsState ct1 ekDecoder =>
        match msg.type, msg.data with
        | .ekCt1Ack, some chunk =>
            if msg.epoch = e then
              let dec := ekDecoder.addChunk chunk
              match dec.decodedPayload with
              | some ekVector =>
                  if P.inc.validPK hdr ekVector then
                    -- Figure 1, edge 11: vector decoding completes after acknowledgement.
                    let ct2 := P.hEnc2.encaps2Det encapsState hdr ekVector
                    let tag := auth.macCiphertext a e (ct1, ct2)
                    .ok { receivingEpoch := e - 1, outputKey := none,
                          state := .ct2Sampled e a (EncoderState.init P.ecpCt2 (ct2, tag)) }
                  else .error .ekIntegrity
              | none =>
                  .ok { receivingEpoch := e - 1, outputKey := none,
                        state := .ct1Acknowledged e a hdr encapsState ct1 dec }
            else ignore
        | _, _ => ignore
    | .ct2Sampled e a _ =>
        if msg.epoch = e + 1 then
          -- Figure 1, edge 13: read the report from the post-transition state.
          .ok { receivingEpoch := e, outputKey := none, state := .keysUnsampled (e + 1) a }
        else ignore

/-- Alice's initial state: epoch `1`, an initialized authenticator, and no sampled keys. -/
-- ANCHOR: Braid_initA
def initA (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (ik : InitKey) : State P AuthState
-- ANCHOR_END: Braid_initA
    :=
  .keysUnsampled 1 (auth.init ik 1)

/-- Bob's initial state: epoch `1`, an initialized authenticator, and an empty header decoder. -/
-- ANCHOR: Braid_initB
def initB (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (ik : InitKey) : State P AuthState
-- ANCHOR_END: Braid_initB
    :=
  .noHeaderReceived 1 (auth.init ik 1) (DecoderState.empty P.ecpHdr)

end MLKEMBraid
