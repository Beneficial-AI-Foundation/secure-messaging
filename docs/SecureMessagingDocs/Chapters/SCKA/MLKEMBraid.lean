import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Bibliography
import SecureMessaging.SCKA.MLKEMBraid.Authenticator
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

:::group "mlkem_braid_protocol"
ML-KEM Braid.
:::

:::defTitle "mlkem_braid_protocol_parameters" "Protocol parameters"
:::

::::definition "mlkem_braid_protocol_parameters" (parent := "mlkem_braid_protocol") (lean := "MLKEMBraid.Parameters")

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

::::definition "mlkem_braid_protocol_states" (parent := "mlkem_braid_protocol") (lean := "MLKEMBraid.State")

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

{usesLabel}`uses` {uses "erasure_code_streaming"}[]
::::

:::defTitle "mlkem_braid_protocol_transitions" "Send and receive"
:::

::::definition "mlkem_braid_protocol_transitions" (parent := "mlkem_braid_protocol") (lean := "MLKEMBraid.send, MLKEMBraid.receive")

:::leanPillCaption "send transition"
:::

```anchor Braid_send (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Basic)
def send (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : State P AuthState) : m (SendResult P AuthState)
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

{usesLabel}`uses` {uses "mlkem_braid_protocol_parameters"}[] · {uses "mlkem_braid_ratcheted_authenticator"}[] · {uses "erasure_code_streaming"}[]
::::

:::defTitle "mlkem_braid_protocol_init" "Initialization"
:::

::::definition "mlkem_braid_protocol_init" (parent := "mlkem_braid_protocol") (lean := "MLKEMBraid.initA, MLKEMBraid.initB")

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

:::defTitle "mlkem_braid_spec" "ML-KEM Braid protocol"
:::

::::definition "mlkem_braid_spec" (parent := "cka_protocols_mlkem_braid") (lean := "MLKEMBraid.scheme")

:::leanPillCaption "ML-KEM Braid as an SCKA scheme"
:::

```anchor Braid_scheme (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Construction)
def scheme (P : Parameters m) [DecidableEq P.Sym]
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc) (sampleInitKey : m InitKey) :
    SCKAScheme m InitKey (State P AuthState) (State P AuthState)
      P.EpochKey (Message P.Sym) (SendRand irl.KeygenRand irl.Encaps1Rand)
    :=
  let sendSCKA (st : State P AuthState) := do
    let r ← send P auth st
    pure (some (r.outputKey, r.msg, r.sendingEpoch, r.state))
  let sendRleakSCKA (st : State P AuthState) := do
    let (r, rand) ← sendRleak P irl auth st
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

{usesLabel}`uses` {uses "scka_scheme"}[] · {uses "mlkem_braid_protocol_transitions"}[] · {uses "mlkem_braid_protocol_init"}[] · {githubLabel}`github` {githubIssue 271}[]
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
