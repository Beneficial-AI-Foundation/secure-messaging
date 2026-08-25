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
ML-KEM Braid.
:::

:::defTitle "mlkem_braid_protocol_parameters" "Protocol parameters"
:::

::::definition "mlkem_braid_protocol_parameters" (parent := "mlkem_braid_protocol") (lean := "MLKEMBraid.Parameters")
$`\todo`

:::leanPillCaption "incremental KEM, pure receive operations, epoch-key derivation, and streams"
:::

```anchor Braid_Parameters (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Basic)
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
```

{usesLabel}`uses` {uses "incremental_kem_scheme"}[] · {uses "erasure_code_payload"}[]
::::

:::defTitle "mlkem_braid_protocol_messages" "Messages"
:::

::::definition "mlkem_braid_protocol_messages" (parent := "mlkem_braid_protocol") (lean := "MLKEMBraid.MessageType, MLKEMBraid.Message")
$`\todo`

:::leanPillCaption "message types"
:::

```anchor Braid_MessageType (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Basic)
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
```

:::leanPillCaption "protocol message"
:::

```anchor Braid_Message (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Basic)
structure Message (Sym : Type) where
  /-- `epoch`: the epoch being negotiated. -/
  epoch : ℕ
  /-- `type`: which stream, acknowledgment, or empty message this is. -/
  type : MessageType
  /-- `data`: the indexed erasure-code chunk, if any. -/
  data : Option (ℕ × Sym)
```

::::

:::defTitle "mlkem_braid_protocol_states" "Protocol states"
:::

::::definition "mlkem_braid_protocol_states" (parent := "mlkem_braid_protocol") (lean := "MLKEMBraid.State, MLKEMBraid.State.epoch")
$`\todo`

:::leanPillCaption "the eleven protocol states"
:::

```anchor Braid_State (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Basic)
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
```

:::leanPillCaption "state epoch projection"
:::

```anchor Braid_State_epoch (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Basic)
def State.epoch : State P AuthState → ℕ
```

{usesLabel}`uses` {uses "erasure_code_streaming"}[]
::::

:::defTitle "mlkem_braid_protocol_transitions" "Send and receive"
:::

::::definition "mlkem_braid_protocol_transitions" (parent := "mlkem_braid_protocol") (lean := "MLKEMBraid.SendResult, MLKEMBraid.RecvResult, MLKEMBraid.Failure, MLKEMBraid.SendRand, MLKEMBraid.send, MLKEMBraid.sendRleak, MLKEMBraid.receive")
$`\todo`

:::leanPillCaption "send output"
:::

```anchor Braid_SendResult (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Basic)
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
```

:::leanPillCaption "receive output"
:::

```anchor Braid_RecvResult (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Basic)
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
  /-- The received encapsulation-key vector fails `validPK`. -/
  | ekIntegrity
  /-- `VfyHdr` rejected the header tag. -/
  | headerMac
  /-- `VfyCt` rejected the ciphertext tag. -/
  | ciphertextMac
  /-- Deterministic decapsulation rejected the ciphertext. This cannot occur for ML-KEM. -/
  | decapsReject
```

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

:::leanPillCaption "send transition"
:::

```anchor Braid_send (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Basic)
def send (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : State P AuthState) : m (SendResult P AuthState)
```

:::leanPillCaption "randomness-leaking send"
:::

```anchor Braid_sendRleak (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Construction)
def sendRleak (P : Parameters m) (irl : P.kem.IncrementalRandLeak P.inc)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : State P AuthState) :
    m (SendResult P AuthState × SendRand irl.KeygenRand irl.Encaps1Rand)
```

:::leanPillCaption "receive transition"
:::

```anchor Braid_receive (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Basic)
def receive (P : Parameters m) [DecidableEq P.Sym]
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : State P AuthState) (msg : Message P.Sym) :
    Except Failure (RecvResult P AuthState)
```

{usesLabel}`uses` {uses "mlkem_braid_protocol_parameters"}[] · {uses "mlkem_braid_ratcheted_authenticator"}[] · {uses "erasure_code_streaming"}[] · {uses "incremental_kem_rand_leak"}[]
::::

:::defTitle "mlkem_braid_protocol_init" "Initialization"
:::

::::definition "mlkem_braid_protocol_init" (parent := "mlkem_braid_protocol") (lean := "MLKEMBraid.initA, MLKEMBraid.initB")
$`\todo`

:::leanPillCaption "Alice's initial state"
:::

```anchor Braid_initA (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Basic)
def initA (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (ik : InitKey) : State P AuthState
```

:::leanPillCaption "Bob's initial state"
:::

```anchor Braid_initB (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Basic)
def initB (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (ik : InitKey) : State P AuthState
```

{usesLabel}`uses` {uses "mlkem_braid_ratcheted_authenticator"}[] · {uses "erasure_code_streaming"}[]
::::

:::group "mlkem_braid_scka"
`scheme` packages the transition system with the SCKA syntax of {Informal.citet SCKA25}[].
`sendRleak` consumes `KEMScheme.IncrementalRandLeak` for key generation and first-stage
encapsulation. `recvSCKA` maps failures to refused deliveries and uses the message-derived
epoch required by SCKA; `Basic.receive` retains the state-derived §2.5 report.
:::

:::defTitle "mlkem_braid_scka_scheme" "SCKA scheme"
:::

::::definition "mlkem_braid_scka_scheme" (parent := "mlkem_braid_scka") (lean := "MLKEMBraid.recvSCKA, MLKEMBraid.scheme")
$`\todo`

:::leanPillCaption "receive adapter"
:::

```anchor Braid_recvSCKA (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Construction)
def recvSCKA (P : Parameters m) [DecidableEq P.Sym]
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : State P AuthState) (msg : Message P.Sym) :
    Option (Option (ℕ × P.EpochKey) × ℕ × State P AuthState)
```

:::leanPillCaption "the protocol as an SCKA scheme"
:::

```anchor Braid_scheme (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Construction)
def scheme (P : Parameters m) [DecidableEq P.Sym]
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc) (sampleInitKey : m InitKey) :
    SCKAScheme m InitKey (State P AuthState) (State P AuthState)
      P.EpochKey (Message P.Sym) (SendRand irl.KeygenRand irl.Encaps1Rand)
```

{usesLabel}`uses` {uses "scka_scheme"}[] · {uses "mlkem_braid_protocol_transitions"}[] · {uses "mlkem_braid_protocol_init"}[]
::::
