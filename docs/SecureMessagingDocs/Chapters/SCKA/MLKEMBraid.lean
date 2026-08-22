import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Bibliography
import SecureMessaging.SCKA.MLKEMBraid.Authenticator
import SecureMessagingDocs.Bibliography
import SecureMessaging.SCKA.MLKEMBraid.Basic
import SecureMessaging.SCKA.MLKEMBraid.Construction
import SecureMessaging.SCKA.MLKEMBraid.Unchunked

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option verso.docstring.allowMissing true

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open Informal

set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "ML-KEM Braid" =>

*References:*

- {Informal.citet MLKEM_Braid}[]

:::group "cka_protocols_mlkem_braid"
ML-KEM Braid ({Informal.citet MLKEM_Braid}[]).
:::

:::defTitle "mlkem_braid_ratcheted_authenticator" "ML-KEM Braid ratcheted authenticator"
:::

::::definition "mlkem_braid_ratcheted_authenticator" (parent := "cka_protocols_mlkem_braid") (lean := "RatchetedAuthenticator")
$`\todo`

:::leanPillCaption "ratcheted authenticator interface"
:::

```anchor RatchetedAuthenticator (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Authenticator)
structure RatchetedAuthenticator
    (InitKey EpochKey AuthState Header Ciphertext Mac : Type) where
  /-- Initialize authenticator state from an initial key and epoch. -/
  init : InitKey → ℕ → AuthState
  /-- Ratchet the authenticator state with an epoch key at the given epoch. -/
  update : AuthState → ℕ → EpochKey → AuthState
  /-- MAC a header at the given epoch. -/
  macHeader : AuthState → ℕ → Header → Mac
  /-- Verify a MAC on a header at the given epoch. -/
  verifyHeader : AuthState → ℕ → Header → Mac → Bool
  /-- MAC a ciphertext at the given epoch. -/
  macCiphertext : AuthState → ℕ → Ciphertext → Mac
  /-- Verify a MAC on a ciphertext at the given epoch. -/
  verifyCiphertext : AuthState → ℕ → Ciphertext → Mac → Bool
  /-- Honestly produced header MACs verify successfully. -/
  verifyHeader_correct :
    ∀ (s : AuthState) (ep : ℕ) (h : Header),
      verifyHeader s ep h (macHeader s ep h) = true
  /-- Honestly produced ciphertext MACs verify successfully. -/
  verifyCiphertext_correct :
    ∀ (s : AuthState) (ep : ℕ) (c : Ciphertext),
      verifyCiphertext s ep c (macCiphertext s ep c) = true
```

{usesLabel}`uses` {uses "scka_scheme"}[] · {githubLabel}`github` {githubIssue 245}[]
::::

:::defTitle "mlkem_braid_spec" "ML-KEM Braid protocol"
:::

::::definition "mlkem_braid_spec" (parent := "cka_protocols_mlkem_braid")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "scka_scheme"}[] · {uses "incremental_kem_scheme"}[] · {uses "mlkem_braid_ratcheted_authenticator"}[] · {githubLabel}`github` {githubIssue 271}[]
::::

:::defTitle "mlkem_braid_correctness" "ML-KEM Braid correctness"
:::

::::theorem "mlkem_braid_correctness" (parent := "cka_protocols_mlkem_braid")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "mlkem_braid_spec"}[] · {uses "scka_correctness"}[] · {uses "incremental_kem_scheme"}[] · {githubLabel}`github` {githubIssue 243}[]
::::

:::defTitle "mlkem_braid_security" "ML-KEM Braid security"
:::

::::theorem "mlkem_braid_security" (parent := "cka_protocols_mlkem_braid")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "mlkem_braid_spec"}[] · {uses "scka_security"}[] · {uses "incremental_kem_scheme"}[] · {githubLabel}`github` {githubIssue 244}[]
::::

:::group "mlkem_braid_protocol"
Signal's *The ML-KEM Braid Protocol* defines the transition system formalized here: the
§2.3 message vocabulary, the eleven states and per-state send and receive procedures of
§2.5, and the §2.6 initialization.

The primitives are parameters: the KEM operations of §1.2 at their §2.5 call shapes, the
header hash of §1.2.1, `KDF_OK`, and one erasure-coded stream per §2.2 payload, with §2.4
authentication supplied by a ratcheted authenticator. A concrete ML-KEM instantiation
supplies SHA3-256, HKDF, HMAC-SHA256, and an erasure code for each stream.

Every send stamps `msg.epoch = state.epoch` and reports `state.epoch - 1`. A receive
reports `state.epoch - 1` for its entry state, except `ct2Sampled`, which reads the report
from the successor state. An accepted next-epoch message therefore reports the entry
epoch. `receive` ignores unguarded message types, epochs outside a guard, every input in
`keysUnsampled` and `headerReceived`, and any message that violates the §2.3
data-presence convention checked before state dispatch. In each case it returns the
entry state with no output key and `state.epoch - 1`.
:::

:::defTitle "mlkem_braid_protocol_parameters" "Protocol parameters"
:::

::::definition "mlkem_braid_protocol_parameters" (parent := "mlkem_braid_protocol") (lean := "MLKEMBraid.Parameters")
$`\todo`

:::leanPillCaption "KEM operations, epoch-key derivation, and the four streams"
:::

```anchor Braid_Parameters (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Basic)
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
```

{usesLabel}`uses` {uses "erasure_code_payload"}[]
::::

:::defTitle "mlkem_braid_protocol_messages" "Messages"
:::

::::definition "mlkem_braid_protocol_messages" (parent := "mlkem_braid_protocol") (lean := "MLKEMBraid.MessageType, MLKEMBraid.Message, MLKEMBraid.Message.wellFormed")
$`\todo`

:::leanPillCaption "message types, the logical protocol message, and the data-presence convention"
:::

```anchor Braid_Message (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Basic)
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
```

::::

:::defTitle "mlkem_braid_protocol_states" "Protocol states"
:::

::::definition "mlkem_braid_protocol_states" (parent := "mlkem_braid_protocol") (lean := "MLKEMBraid.State, MLKEMBraid.State.epoch")
$`\todo`

:::leanPillCaption "the eleven states and the epoch each carries"
:::

```anchor Braid_State (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Basic)
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
```

In each equation, `e` binds the first constructor field, `..` ignores the remaining
fields, and the right-hand side returns that bound epoch.

{usesLabel}`uses` {uses "erasure_code_streaming"}[]
::::

:::defTitle "mlkem_braid_protocol_transitions" "Send and receive"
:::

::::definition "mlkem_braid_protocol_transitions" (parent := "mlkem_braid_protocol") (lean := "MLKEMBraid.SendResult, MLKEMBraid.RecvResult, MLKEMBraid.Failure, MLKEMBraid.send, MLKEMBraid.receive")
$`\todo`

:::leanPillCaption "send and receive outputs"
:::

```anchor Braid_Results (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Basic)
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
```

:::leanPillCaption "receive failures"
:::

```anchor Braid_Failure (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Basic)
inductive Failure where
  /-- The received encapsulation-key vector does not hash to the stored `hek`. -/
  | ekIntegrity
  /-- `VfyHdr` rejected the header tag. -/
  | headerMac
  /-- `VfyCt` rejected the ciphertext tag. -/
  | ciphertextMac
```

Figure 1 on p. 10 of the ML-KEM Braid PDF numbers the state-machine edges. The §2.5
pseudocode repeats each number as `# Transition (n)` before the corresponding state
update. Edges 1 and 7 are sends; the other numbered edges are receives.

The eleven sends, by entry state. Every send stamps `msg.epoch = state.epoch` and reports
`state.epoch - 1`. Edge 1 is the send from `keysUnsampled` and edge 7 the send from
`headerReceived`; the other nine states emit the next chunk of the stream they are
streaming, or the empty message when they have none.

```
State                  Message              Randomized operation
keysUnsampled          Hdr chunk            KeyGen
keysSampled            Hdr chunk            —
headerSent             Ek chunk             —
ct1Received            EkCt1Ack chunk       —
ekSentCt1Received      None, no payload     —
noHeaderReceived       None, no payload     —
headerReceived         Ct1 chunk            Encaps1
ct1Sampled             Ct1 chunk            —
ekReceivedCt1Sampled   Ct1 chunk            —
ct1Acknowledged        None, no payload     —
ct2Sampled             Ct2 chunk            —
```

The eleven receive edges, by entry state. Each guard specifies an accepted message type
and epoch; `e` is the entry-state epoch. The states `keysUnsampled` and `headerReceived`
ignore every input. Every other state returns its entry state with no output key when an
input is ill-formed or matches no guard.

```
Entry state            Guard               Figure 1 edge and result
keysSampled            Ct1, epoch e        2: headerSent, storing the first ct1 chunk and
                                                starting the ek_vector stream
headerSent             Ct1, epoch e        3: ct1Received once ct1 decodes
ct1Received            Ct2, epoch e        4: ekSentCt1Received, storing the first ct2 chunk
ekSentCt1Received      Ct2, epoch e        5: once ct2 decodes and VfyCt accepts, output the
                                                epoch-e key and move to noHeaderReceived at
                                                e + 1; a VfyCt rejection raises ciphertextMac
noHeaderReceived       Hdr, epoch e        6: once the header decodes and VfyHdr accepts,
                                                headerReceived; a rejection raises headerMac
ct1Sampled             EkCt1Ack, epoch e   8: ct1Acknowledged while ek_vector is incomplete
ct1Sampled             EkCt1Ack, epoch e   9: once ek_vector decodes and hashes to hek,
                                                Encaps2 and ct2Sampled; a mismatch raises
                                                ekIntegrity
ct1Sampled             Ek, epoch e         10: once ek_vector decodes and hashes to hek,
                                                ekReceivedCt1Sampled; a mismatch raises
                                                ekIntegrity
ct1Acknowledged        EkCt1Ack, epoch e   11: once ek_vector decodes and hashes to hek,
                                                Encaps2 and ct2Sampled; a mismatch raises
                                                ekIntegrity
ekReceivedCt1Sampled   EkCt1Ack, epoch e   12: Encaps2 and ct2Sampled; the carried chunk is
                                                discarded
ct2Sampled             well-formed,         13: keysUnsampled at e + 1, reporting epoch e
                       epoch e + 1
```

{usesLabel}`uses` {uses "mlkem_braid_ratcheted_authenticator"}[] · {uses "erasure_code_streaming"}[]
::::

:::defTitle "mlkem_braid_protocol_init" "Initialization"
:::

::::definition "mlkem_braid_protocol_init" (parent := "mlkem_braid_protocol") (lean := "MLKEMBraid.initA, MLKEMBraid.initB")
$`\todo`

:::leanPillCaption "the two initial states of an epoch-1 session"
:::

```anchor Braid_init (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Basic)
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
```

{usesLabel}`uses` {uses "mlkem_braid_ratcheted_authenticator"}[] · {uses "erasure_code_streaming"}[]
::::

:::group "mlkem_braid_scka"
The SCKA construction packages the ML-KEM Braid transition system as a scheme with the
syntax of §3.1 and the game in Figure 1 of {Informal.citet SCKA25}[],
*How to Compare Bandwidth Constrained Two-Party Secure Messaging Protocols*. Both
parties run the same send and receive and differ only in their initial state.

An SCKA scheme asks for a randomness-leaking send, which §2.5 does not describe.
`RandLeak` pairs `KeyGen` and `Encaps1`, the two randomized operations of §1.2, with
their sampled randomness. `sendRleak` uses these operations in the `keysUnsampled` and
`headerReceived` branches and delegates the other nine branches to `send`.

The receive adapter reports `msg.epoch - 1` instead of the state-derived report. It maps
a failure to the outer `none`, which tells the game to refuse delivery; the inner `none`
means that a successful receive produced no epoch key. A failure contains no
`RecvResult`, so the adapter has no successor state, epoch, or key to report. Refusal
neither terminates nor renegotiates the session.

The game can replay recorded messages in any order. On each delivery,
`assertMatchingEpoch` requires the receiving epoch to equal the sending epoch recorded
with the message. Every send stamps `msg.epoch = state.epoch` and reports
`state.epoch - 1`, making `msg.epoch - 1` the recorded sending epoch. The adapter's
epoch report matches `receive` whenever a guard accepts: the guards require
`msg.epoch = state.epoch`, and an accepted `ct2Sampled` transition again reports
`msg.epoch - 1`. For an ignored message from another epoch, the adapter reports
`msg.epoch - 1` and `receive` reports the receiver's epoch.
:::

:::defTitle "mlkem_braid_scka_leakage" "Disclosed send randomness"
:::

::::definition "mlkem_braid_scka_leakage" (parent := "mlkem_braid_scka") (lean := "MLKEMBraid.SendRand, MLKEMBraid.RandLeak, MLKEMBraid.sendRleak")
$`\todo`

:::leanPillCaption "what a send discloses"
:::

```anchor Braid_SendRand (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Construction)
inductive SendRand (KeygenRand Encaps1Rand : Type) where
  /-- The send ran neither `KeyGen` nor `Encaps1`. -/
  | none
  /-- The send ran `KeyGen`. -/
  | keygen (r : KeygenRand)
  /-- The send ran `Encaps1`. -/
  | encaps1 (r : Encaps1Rand)
```

:::leanPillCaption "leaking key generation and first-stage encapsulation"
:::

```anchor Braid_RandLeak (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Construction)
structure RandLeak (P : Parameters m) where
  /-- Randomness space of `KeyGen`. -/
  KeygenRand : Type
  /-- Randomness space of `Encaps1`. -/
  Encaps1Rand : Type
  /-- `KeyGen` with its randomness. -/
  keyGenRleak : m ((P.Dk × P.EkSeed × P.EkVector) × KeygenRand)
  /-- `Encaps1` with its randomness. -/
  encaps1Rleak : P.EkSeed → P.Hek →
    m ((P.EncapsSecret × P.Ct1 × P.SharedSecret) × Encaps1Rand)
  /-- Discarding the randomness of `keyGenRleak` gives `P.keyGen`. -/
  keyGen_fst : (do let out ← keyGenRleak; pure out.1) = P.keyGen
  /-- Discarding the randomness of `encaps1Rleak` gives `P.encaps1`. -/
  encaps1_fst : ∀ seed hek,
    (do let out ← encaps1Rleak seed hek; pure out.1) = P.encaps1 seed hek
```

:::leanPillCaption "randomness-leaking send"
:::

```anchor Braid_sendRleak (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Construction)
def sendRleak (P : Parameters m) (rl : RandLeak P)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      (P.EkSeed × P.Hek) (P.Ct1 × P.Ct2) P.Mac)
    (st : State P AuthState) :
    m (SendResult P AuthState × SendRand rl.KeygenRand rl.Encaps1Rand) :=
  match st with
  | .keysUnsampled e a => do
      let ((dk, ekSeed, ekVector), r) ← rl.keyGenRleak
      let hek := P.hashEk ekSeed ekVector
      let tag := auth.macHeader a e (ekSeed, hek)
      let (chunk, enc) := (EncoderState.init P.ecpHdr ((ekSeed, hek), tag)).nextChunk
      pure ({ msg := { epoch := e, type := .hdr, data := some chunk },
              sendingEpoch := e - 1, outputKey := none,
              state := .keysSampled e a dk ekVector enc }, .keygen r)
  | .headerReceived e a ekSeed hek ekDecoder => do
      let ((encapsSecret, ct1, sharedSecret), r) ← rl.encaps1Rleak ekSeed hek
      let ik := P.kdfOK sharedSecret e
      let (chunk, enc) := (EncoderState.init P.ecpCt1 ct1).nextChunk
      pure ({ msg := { epoch := e, type := .ct1, data := some chunk },
              sendingEpoch := e - 1, outputKey := some (e, ik),
              state := .ct1Sampled e (auth.update a e ik) ekSeed hek encapsSecret ct1 enc
                ekDecoder }, .encaps1 r)
  | st => (fun r => (r, .none)) <$> send P auth st
```

Two branches remain explicit: `keysUnsampled` draws its key pair from `rl.keyGenRleak`
and discloses `keygen`, and `headerReceived` draws its first encapsulation stage from
`rl.encaps1Rleak` and discloses `encaps1`. The nine remaining states call `send` and
disclose `none`.

{usesLabel}`uses` {uses "mlkem_braid_protocol_transitions"}[]
::::

:::defTitle "mlkem_braid_scka_scheme" "SCKA scheme"
:::

::::definition "mlkem_braid_scka_scheme" (parent := "mlkem_braid_scka") (lean := "MLKEMBraid.recvSCKA, MLKEMBraid.scheme")
$`\todo`

:::leanPillCaption "receive adapter"
:::

```anchor Braid_recvSCKA (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Construction)
def recvSCKA (P : Parameters m) [DecidableEq P.Sym] [DecidableEq P.Hek]
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      (P.EkSeed × P.Hek) (P.Ct1 × P.Ct2) P.Mac)
    (st : State P AuthState) (msg : Message P.Sym) :
    Option (Option (ℕ × P.EpochKey) × ℕ × State P AuthState) :=
  match receive P auth st msg with
  | .error _ => none
  | .ok r => some (r.outputKey, msg.epoch - 1, r.state)
```

:::leanPillCaption "the protocol as an SCKA scheme"
:::

```anchor Braid_scheme (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Construction)
def scheme (P : Parameters m) [DecidableEq P.Sym] [DecidableEq P.Hek]
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      (P.EkSeed × P.Hek) (P.Ct1 × P.Ct2) P.Mac)
    (rl : RandLeak P) (sampleInitKey : m InitKey) :
    SCKAScheme m InitKey (State P AuthState) (State P AuthState)
      P.EpochKey (Message P.Sym) (SendRand rl.KeygenRand rl.Encaps1Rand) :=
  let sendSCKA (st : State P AuthState) := do
    let r ← send P auth st
    pure (some (r.outputKey, r.msg, r.sendingEpoch, r.state))
  let sendRleakSCKA (st : State P AuthState) := do
    let (r, rand) ← sendRleak P rl auth st
    pure (some (r.outputKey, r.msg, r.sendingEpoch, r.state, rand))
  { initKeyGen := sampleInitKey
    initA := fun ik => pure (initA P auth ik)
    initB := fun ik => pure (initB P auth ik)
    sendA := sendSCKA
    sendArleak := sendRleakSCKA
    recvA := recvSCKA P auth
    sendB := sendSCKA
    sendBrleak := sendRleakSCKA
    recvB := recvSCKA P auth }
```

{usesLabel}`uses` {uses "scka_scheme"}[] · {uses "mlkem_braid_protocol_transitions"}[] · {uses "mlkem_braid_protocol_init"}[]
::::
