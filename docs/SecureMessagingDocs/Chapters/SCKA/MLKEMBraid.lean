import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Bibliography
import SecureMessaging.SCKA.MLKEMBraid.Authenticator
import SecureMessaging.SCKA.MLKEMBraid.Basic
import SecureMessaging.SCKA.MLKEMBraid.Construction
import SecureMessaging.SCKA.MLKEMBraid.Correctness
import SecureMessaging.SCKA.MLKEMBraid.Security

/-! # Blueprint chapter: ML-KEM Braid -/

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
- {Informal.citet SCKA25}[]

:::group "cka_protocols_mlkem_braid"
ML-KEM Braid ({Informal.citet MLKEM_Braid}[]).
:::

:::defTitle "mlkem_braid_ratcheted_authenticator" "ML-KEM Braid ratcheted authenticator"
:::

::::definition "mlkem_braid_ratcheted_authenticator" (parent := "cka_protocols_mlkem_braid") (lean := "RatchetedAuthenticator") (tags := "gh-245") (uses := "scka_scheme")
Let $`\mathcal I_{\mathsf{CKA}}` be an initial-key space, $`E` an epoch-key space, $`H` and $`C`
message spaces, and $`T` a tag space. A *ratcheted authenticator* $`\mathsf{Auth}` is a pair of
message authentication codes, on $`H` and on $`C`, with tags in $`T` and a common state that is
initialized from an initial key and updated with an epoch key at each epoch. Formally,
$`\mathsf{Auth}` consists of a state space $`\mathcal S_{\mathsf{Auth}}` and the following
algorithms:

- $`\mathsf{Init}:\mathcal I_{\mathsf{CKA}}\times\mathbb N\to\mathcal S_{\mathsf{Auth}}`, the initial state
  for an initial key and an epoch;
- $`\mathsf{Update}:\mathcal S_{\mathsf{Auth}}\times\mathbb N\times E\to\mathcal S_{\mathsf{Auth}}`, the state
  updated with the epoch key of an epoch;
- $`\mathsf{Mac}_H:\mathcal S_{\mathsf{Auth}}\times\mathbb N\times H\to T` and
  $`\mathsf{Verify}_H:\mathcal S_{\mathsf{Auth}}\times\mathbb N\times H\times T\to\{\mathsf{true},\mathsf{false}\}`,
  computing and verifying the tag of a message in $`H` at an epoch;
- $`\mathsf{Mac}_C:\mathcal S_{\mathsf{Auth}}\times\mathbb N\times C\to T` and
  $`\mathsf{Verify}_C:\mathcal S_{\mathsf{Auth}}\times\mathbb N\times C\times T\to\{\mathsf{true},\mathsf{false}\}`,
  computing and verifying the tag of a message in $`C` at an epoch,

satisfying the correctness condition that, for all $`s\in\mathcal S_{\mathsf{Auth}}`, $`\mathsf{ep}\in\mathbb N`,
$`h\in H`, and $`c\in C`,

$$`\mathsf{Verify}_H(s,\mathsf{ep},h,\mathsf{Mac}_H(s,\mathsf{ep},h))
  =\mathsf{Verify}_C(s,\mathsf{ep},c,\mathsf{Mac}_C(s,\mathsf{ep},c))=\mathsf{true}.`

ML-KEM Braid takes for $`H` and $`C=C_1\times C_2` the header and ciphertext spaces of its
{bpref "incremental_kem_scheme"}[incremental KEM].

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
::::

:::group "mlkem_braid_protocol"
ML-KEM Braid.
:::

:::defTitle "mlkem_braid_protocol_parameters" "Protocol parameters"
:::

::::definition "mlkem_braid_protocol_parameters" (parent := "mlkem_braid_protocol") (lean := "MLKEMBraid.Parameters") (uses := "incremental_kem_scheme, erasure_code_payload")

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
  /-- Header-stream decoder. -/
  decHdr : StreamDecoder (inc.PKheader × Mac) Sym
  /-- Encapsulation-key-vector-stream decoder. -/
  decEk : StreamDecoder inc.PKvector Sym
  /-- `ct₁`-stream decoder. -/
  decCt1 : StreamDecoder inc.C₁ Sym
  /-- `ct₂`-stream decoder. -/
  decCt2 : StreamDecoder (inc.C₂ × Mac) Sym
```
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

::::definition "mlkem_braid_protocol_states" (parent := "mlkem_braid_protocol") (lean := "MLKEMBraid.State") (uses := "erasure_code_streaming")

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
      (ct1Decoder : P.decCt1.D)
      (ekEncoder : EncoderState P.inc.PKvector P.Sym)
  /-- "Ct1Received": `sk`, `ct1`, `ek_encoder`. -/
  | ct1Received (epoch : ℕ) (auth : AuthState) (sk : P.SK) (ct1 : P.inc.C₁)
      (ekEncoder : EncoderState P.inc.PKvector P.Sym)
  /-- "EkSentCt1Received": `sk`, `ct1`, `ct2_decoder`. -/
  | ekSentCt1Received (epoch : ℕ) (auth : AuthState) (sk : P.SK) (ct1 : P.inc.C₁)
      (ct2Decoder : P.decCt2.D)
  /-- "NoHeaderReceived": `header_decoder`. -/
  | noHeaderReceived (epoch : ℕ) (auth : AuthState)
      (headerDecoder : P.decHdr.D)
  /-- "HeaderReceived": `header`, `ek_decoder`. -/
  | headerReceived (epoch : ℕ) (auth : AuthState) (header : P.inc.PKheader)
      (ekDecoder : P.decEk.D)
  /-- "Ct1Sampled": `header`, `encaps_state`, `ct1`, `ct1_encoder`, `ek_decoder`. -/
  | ct1Sampled (epoch : ℕ) (auth : AuthState) (header : P.inc.PKheader)
      (encapsState : P.inc.St) (ct1 : P.inc.C₁)
      (ct1Encoder : EncoderState P.inc.C₁ P.Sym)
      (ekDecoder : P.decEk.D)
  /-- "EkReceivedCt1Sampled": `encaps_state`, `ct1`, `header`, `ek_vector`,
  `ct1_encoder`. -/
  | ekReceivedCt1Sampled (epoch : ℕ) (auth : AuthState)
      (encapsState : P.inc.St) (ct1 : P.inc.C₁) (header : P.inc.PKheader)
      (ekVector : P.inc.PKvector) (ct1Encoder : EncoderState P.inc.C₁ P.Sym)
  /-- "Ct1Acknowledged": `header`, `encaps_state`, `ct1`, `ek_decoder`. -/
  | ct1Acknowledged (epoch : ℕ) (auth : AuthState) (header : P.inc.PKheader)
      (encapsState : P.inc.St) (ct1 : P.inc.C₁)
      (ekDecoder : P.decEk.D)
  /-- "Ct2Sampled": `ct2_encoder`. -/
  | ct2Sampled (epoch : ℕ) (auth : AuthState)
      (ct2Encoder : EncoderState (P.inc.C₂ × P.Mac) P.Sym)
```
::::

:::defTitle "mlkem_braid_protocol_transitions" "Send and receive"
:::

::::definition "mlkem_braid_protocol_transitions" (parent := "mlkem_braid_protocol") (lean := "MLKEMBraid.send, MLKEMBraid.receive") (uses := "mlkem_braid_protocol_parameters, mlkem_braid_ratcheted_authenticator, erasure_code_streaming")

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
def receive (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : State P AuthState) (msg : Message P.Sym) :
    Except Failure (RecvResult P AuthState)
```
::::

:::defTitle "mlkem_braid_protocol_init" "Initialization"
:::

::::definition "mlkem_braid_protocol_init" (parent := "mlkem_braid_protocol") (lean := "MLKEMBraid.initA, MLKEMBraid.initB") (uses := "mlkem_braid_ratcheted_authenticator, erasure_code_streaming")

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
::::

:::defTitle "mlkem_braid_spec" "ML-KEM Braid protocol"
:::

::::definition "mlkem_braid_spec" (parent := "cka_protocols_mlkem_braid") (lean := "MLKEMBraid.scheme") (tags := "gh-271") (uses := "scka_scheme, mlkem_braid_protocol_parameters, mlkem_braid_ratcheted_authenticator, mlkem_braid_protocol_transitions, mlkem_braid_protocol_init")
Let $`P` be a set of {bpref "mlkem_braid_protocol_parameters"}[protocol parameters], let
$`\mathsf{Auth}` be a {bpref "mlkem_braid_ratcheted_authenticator"}[ratcheted authenticator] for
the epoch keys, headers, ciphertexts in $`C_1\times C_2` and tags of $`P`, and let
$`\mathsf{InitKeyGen}` be an algorithm that samples the initial key of $`\mathsf{Auth}`. ML-KEM
Braid $`\mathsf{Braid}(P,\mathsf{Auth},\mathsf{InitKeyGen})` is the
{bpref "scka_scheme"}[SCKA scheme] whose parties run the
{bpref "mlkem_braid_protocol_transitions"}[send and receive algorithms], starting from the
{bpref "mlkem_braid_protocol_init"}[initial states]. Headers and ciphertexts carry tags that
$`\mathsf{Auth}` computes and verifies. $`\mathsf{Auth}` updates its state with each derived epoch
key.

:::leanPillCaption "ML-KEM Braid as an SCKA scheme"
:::

```anchor Braid_scheme (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Construction)
def scheme (P : Parameters m)
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
::::

:::defTitle "mlkem_braid_correctness" "ML-KEM Braid correctness"
:::

::::theorem "mlkem_braid_correctness" (parent := "cka_protocols_mlkem_braid") (lean := "MLKEMBraid.correctness_error_le, MLKEMBraid.mlkemBraidScheme_correctness_error_le") (tags := "gh-243") (uses := "mlkem_braid_spec, scka_correctness, incremental_kem_scheme, incremental_kem_rand_leak, erasure_code_correctness, stream_decoder")
$`\todo`

:::leanPillCaption "Correctness error bound"
:::

```anchor Braid_correctness_error_le (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Correctness)
theorem correctness_error_le
    (P : Parameters ProbComp) [DecidableEq P.K]
    [DecidableEq P.EpochKey]
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc)
    (sampleInitKey : ProbComp InitKey)
    (hHdrSound : P.decHdr.Sound P.ecpHdr)
    (hEkSound : P.decEk.Sound P.ecpEk)
    (hCt1Sound : P.decCt1.Sound P.ecpCt1)
    (hCt2Sound : P.decCt2.Sound P.ecpCt2)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message P.Sym))
    (q : ℕ) (hq : SCKAScheme.SendQueryBound adv q) :
    1 - Pr{let x ← SCKAScheme.correctnessExp (scheme P auth irl sampleInitKey) adv}[x = true] ≤
      (q : ℝ≥0∞) * P.kem.correctnessError ProbCompRuntime.probComp
```
::::

:::defTitle "mlkem_braid_noauth_spec" "ML-KEM Braid without authentication"
:::

::::definition "mlkem_braid_noauth_spec" (parent := "cka_protocols_mlkem_braid") (lean := "MLKEMBraid.NoAuth.auth, MLKEMBraid.NoAuth.scheme") (uses := "mlkem_braid_spec, mlkem_braid_ratcheted_authenticator")
Let $`P` be a set of protocol parameters whose tag space $`P.\mathsf{Mac}` is the unit type. The
*trivial authenticator* $`\mathsf{Auth}_\top` has the unit type as its state space, gives the unit
tag to every header and ciphertext, and accepts every tag:
$`\mathsf{Verify}_H=\mathsf{Verify}_C=\mathsf{true}`.
*ML-KEM Braid without authentication* is the protocol
$`\mathsf{Braid}_{\mathsf{NoAuth}}(P)=\mathsf{Braid}(P,\mathsf{Auth}_\top,\mathsf{InitKeyGen}_\top)` of
{bpref "mlkem_braid_spec"}[], where $`\mathsf{InitKeyGen}_\top` returns the unit initial key.

:::leanPillCaption "trivial authenticator"
:::

```anchor noAuthAuthenticator (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Security.NoAuth)
def auth (P : Parameters ProbComp) (hMac : P.Mac = Unit) :
    RatchetedAuthenticator Unit P.EpochKey Unit
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac where
  init := fun _ _ => ()
  update := fun _ _ _ => ()
  macHeader := fun _ _ _ => hMac.symm ▸ ()
  macCiphertext := fun _ _ _ => hMac.symm ▸ ()
  verifyHeader := fun _ _ _ _ => true
  verifyCiphertext := fun _ _ _ _ => true
  verifyHeader_correct := fun _ _ _ => rfl
  verifyCiphertext_correct := fun _ _ _ => rfl
```

:::leanPillCaption "ML-KEM Braid without authentication"
:::

```anchor noAuthScheme (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Security.NoAuth)
def scheme (P : Parameters ProbComp)
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc) :=
  MLKEMBraid.scheme P (auth P hMac) irl (pure ())
```
::::

:::defTitle "mlkem_braid_noauth_vulnerable_epochs" "Vulnerable epochs of ML-KEM Braid without authentication"
:::

::::definition "mlkem_braid_noauth_vulnerable_epochs" (parent := "cka_protocols_mlkem_braid") (lean := "MLKEMBraid.NoAuth.vuln, MLKEMBraid.NoAuth.sendExposure, MLKEMBraid.NoAuth.nativeExposure, MLKEMBraid.NoAuth.sendExposure_eq_delta") (uses := "mlkem_braid_noauth_spec, mlkem_braid_protocol_states, scka_oracles")
The security game of {bpref "scka_oracles"}[] for $`\mathsf{Braid}_{\mathsf{NoAuth}}(P)` uses the
following exposure functions for both parties. Let $`\mathsf{st}` be a local state
({bpref "mlkem_braid_protocol_states"}[]) with epoch $`\mathsf{ep}(\mathsf{st})`, and let $`r` be
the randomness of a send. Then

$$`\mathsf{vuln}^{\mathsf{corr}}(\mathsf{st})=\begin{cases}
\emptyset & \mathsf{st}\text{ is }\mathsf{keysUnsampled},\ \mathsf{noHeaderReceived},\ \mathsf{headerReceived}\text{ or }\mathsf{ct2Sampled},\\
\{\mathsf{ep}(\mathsf{st})\} & \text{otherwise},\end{cases}`

$$`\mathsf{vuln}^{\mathsf{rleak}}(\mathsf{st},r)=\begin{cases}
\{\mathsf{ep}(\mathsf{st})\} & r=\mathsf{keygen}(\cdot)\text{ or }r=\mathsf{encaps}_1(\cdot),\\
\emptyset & r=\mathsf{none}.\end{cases}`

That is, a corruption exposes the current epoch of the party, except before key generation, while
the party waits for a header, between receiving a header and the first stage of encapsulation, and
after the second stage of encapsulation, when the party keeps only the encoder of the second
ciphertext component.
A send that reveals its randomness exposes its epoch if it generates a key pair or runs the first
stage of encapsulation.

If a send of the protocol with randomness $`r` takes a party from $`\mathsf{st}` to
$`\mathsf{st}'`, then
$`\mathsf{vuln}^{\mathsf{rleak}}(\mathsf{st},r)=\mathsf{vuln}^{\mathsf{corr}}(\mathsf{st}')\setminus\mathsf{vuln}^{\mathsf{corr}}(\mathsf{st})`.
This is the exposure rule of {Informal.citet SCKA25}[], Figure 1.

:::leanPillCaption "epochs exposed by a corruption"
:::

```anchor noAuthVuln (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Security.NoAuth)
def vuln {P : Parameters ProbComp} (st : State P Unit) : Finset ℕ :=
  match st with
  | .keysUnsampled .. | .noHeaderReceived .. | .headerReceived .. | .ct2Sampled .. => ∅
  | _ => {st.epoch}
```

:::leanPillCaption "epochs exposed by the randomness of a send"
:::

```anchor noAuthSendExposure (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Security.NoAuth)
def sendExposure {P : Parameters ProbComp} {KeygenRand Encaps1Rand : Type}
    (st : State P Unit) (coins : SendRand KeygenRand Encaps1Rand) : Finset ℕ :=
  match coins with
  | .none => ∅
  | .keygen _ | .encaps1 _ => {st.epoch}
```

:::leanPillCaption "exposure functions of the game"
:::

```anchor nativeExposure (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Security.NoAuth)
def nativeExposure (P : Parameters ProbComp)
    (irl : P.kem.IncrementalRandLeak P.inc) :
    SCKAScheme.VulnerableEpochs (State P Unit)
      (SendRand irl.KeygenRand irl.Encaps1Rand) where
  corrupt := vuln
  rleak := sendExposure
```
::::

:::defTitle "mlkem_braid_noauth_security" "Security of ML-KEM Braid without authentication"
:::

::::theorem "mlkem_braid_noauth_security" (parent := "cka_protocols_mlkem_braid") (lean := "MLKEMBraid.NoAuth.security, MLKEMBraid.security, MLKEMBraid.Bounded.parameters, ErasureCode.SPQRReedSolomon.byteBlocksEquiv, MLKEMBraid.NoAuth.SendQueryBound, MLKEMBraid.NoAuth.kemMixReduction, MLKEMBraid.NoAuth.kdfMixReduction") (tags := "gh-244") (uses := "mlkem_braid_noauth_spec, mlkem_braid_noauth_vulnerable_epochs, scka_security, scka_oracles, incremental_kem_scheme, incremental_kem_rand_leak, erasure_code_correctness, erasure_code_streaming, kdf_context_game")
Let $`\Pi=\mathsf{Braid}_{\mathsf{NoAuth}}(P)` ({bpref "mlkem_braid_noauth_spec"}[]), and assume
that:

* the KEM $`\Gamma` of $`P` has an {bpref "incremental_kem_scheme"}[incremental structure] with
  {bpref "incremental_kem_rand_leak"}[randomness leakage], deterministic decapsulation and a
  deterministic second stage;
* the decoders of the four streams are sound for their erasure codes
  ({bpref "erasure_code_streaming"}[]).

Then for every SCKA adversary $`\mathcal A` against $`\Pi` making at most $`q` ordinary or
leaking sends in total, the IND-CPA adversary $`\mathcal B` against $`\Gamma` and the
key-derivation adversary $`\mathcal C`, both constructed from $`\mathcal A`, satisfy

$$`\Adv{\mathsf{guess}}{\mathsf{SCKA},\Pi}(\mathcal A)
\le \frac q2\left(\Adv{\mathsf{IND\text{-}CPA}}{\mathsf{KEM},\Gamma}(\mathcal B)
+\Adv{\mathsf{KDF}}{\mathsf{kdfOK}}(\mathcal C)\right)+q\varepsilon,`

where:

* $`\Adv{\mathsf{guess}}{\mathsf{SCKA},\Pi}` is the guessing advantage of
  {bpref "scka_security"}[] with the exposure functions of
  {bpref "mlkem_braid_noauth_vulnerable_epochs"}[];
* $`\Adv{\mathsf{IND\text{-}CPA}}{\mathsf{KEM},\Gamma}(\mathcal B)` is the advantage of
  $`\mathcal B` against $`\Gamma` in the KEM IND-CPA security game, and $`\varepsilon` is the
  correctness error of $`\Gamma`;
* $`\Adv{\mathsf{KDF}}{\mathsf{kdfOK}}(\mathcal C)` is the advantage in the
  {bpref "kdf_context_game"}[key-derivation game with an adversarially chosen label];
* $`\mathcal B` and $`\mathcal C` draw an epoch $`e\leftarrow\mathsf{epochChoice}(q)`, which is
  uniform on $`\{1,\dots,q\}` for $`q>0` and is $`1` for $`q=0`. They then run $`\mathcal A`
  against a simulation of the security game. $`\mathcal B` embeds its challenge public key,
  ciphertext and key in epoch $`e`, and $`\mathcal C` answers the challenge of epoch $`e` with the
  key that it receives. Both answer the challenges of earlier epochs with uniform keys and those of
  later epochs with their real keys. They output the bit that $`\mathcal A` outputs, or $`0` if
  epoch $`e` becomes exposed.

The same bound holds for ML-KEM with byte encodings of the prescribed lengths, with Reed–Solomon
codes and the set-based decoder on the four streams. Here $`\mathcal B` is the adversary of the
general case, run on raw ML-KEM inputs through `MLKEM.Bounded.liftAdversary`, and $`\varepsilon`
is the correctness error of ML-KEM. The four payload encodings use `byteBlocksEquiv` to turn
32-byte blocks into chunks of 16 field elements. The field enumeration is abstract;
correspondence with SPQR's runtime field representation remains unproved. The bound depends on
$`\mathsf{kdfOK}` only through
$`\Adv{\mathsf{KDF}}{\mathsf{kdfOK}}(\mathcal C)`. The Braid specification instantiates
$`\mathsf{kdfOK}` with HKDF.

:::leanPillCaption "bytes as erasure-code messages"
:::

```anchor byteBlocksEquiv (project := ".") (module := SecureMessaging.ErasureCode.SPQRReedSolomon.Payload)
noncomputable def byteBlocksEquiv (k : ℕ) :
    Vector UInt8 (32 * k) ≃ (Fin k → Chunk GF16)
```

:::leanPillCaption "security for ML-KEM"
:::

```anchor security (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Security)
theorem MLKEMBraid.security
    (p : MLKEM.ParameterSet) (ring : MLKEM.NTTRingOps)
    (prims : MLKEM.Primitives (MLKEM.ParameterSet.params p)
      (MLKEM.Concrete.concreteEncoding (MLKEM.ParameterSet.params p)))
    {EpochKey : Type} [SampleableType EpochKey] [DecidableEq EpochKey]
    (kdfOK : MLKEM.SharedSecret → ℕ → EpochKey) :
    let P := MLKEMBraid.Bounded.parameters p ring prims kdfOK
    let irl := MLKEM.incrementalRandLeak ring
      (MLKEM.Bounded.encoding (MLKEM.ParameterSet.params p))
      (MLKEM.Bounded.primitives (MLKEM.ParameterSet.params p) prims)
    ∀ (A : MLKEMBraid.NoAuth.Adversary P irl) (q : ℕ),
      MLKEMBraid.NoAuth.SendQueryBound A q →
      let ℬ := MLKEM.Bounded.liftAdversary p ring prims
        (MLKEMBraid.NoAuth.kemMixReduction P rfl irl A q)
      let 𝒞 := MLKEMBraid.NoAuth.kdfMixReduction P rfl irl A q
      let ε := ((MLKEM.mlkemScheme p ring prims).correctnessError
        ProbCompRuntime.probComp).toReal
      SCKAScheme.sckaGuessAdvantage
        (MLKEMBraid.NoAuth.scheme P rfl irl) A
        (MLKEMBraid.NoAuth.nativeExposure P irl)
        (MLKEMBraid.NoAuth.nativeExposure P irl) ≤
        (q / 2 : ℝ) *
          (((MLKEM.mlkemScheme p ring prims).IND_CPA_Advantage ProbCompRuntime.probComp ℬ).toReal +
            MLKEMBraid.kdfAdvantage P.kdfOK 𝒞) + q * ε
```

:::leanPillCaption "security for an abstract KEM and abstract codes"
:::

```anchor genericSecurity (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Security)
theorem MLKEMBraid.NoAuth.security (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.K] [DecidableEq P.EpochKey]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (hHdrSound : P.decHdr.Sound P.ecpHdr) (hEkSound : P.decEk.Sound P.ecpEk)
    (hCt1Sound : P.decCt1.Sound P.ecpCt1) (hCt2Sound : P.decCt2.Sound P.ecpCt2)
    (A : Adversary P irl) (q : ℕ) (hq : SendQueryBound A q) :
    let ℬ := kemMixReduction P hMac irl A q
    let 𝒞 := kdfMixReduction P hMac irl A q
    let ε := (P.kem.correctnessError ProbCompRuntime.probComp).toReal
    SCKAScheme.sckaGuessAdvantage (scheme P hMac irl) A
        (nativeExposure P irl) (nativeExposure P irl) ≤
      (q / 2 : ℝ) * ((P.kem.IND_CPA_Advantage ProbCompRuntime.probComp ℬ).toReal +
        kdfAdvantage P.kdfOK 𝒞) + q * ε
```

:::leanPillCaption "send budget"
:::

```anchor sendQueryBound (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Security.Games)
def SendQueryBound {P : Parameters ProbComp}
    {irl : P.kem.IncrementalRandLeak P.inc}
    (A : Adversary P irl) (qS : ℕ) : Prop :=
  A.IsQueryBoundP (fun t => SCKAScheme.sckaSecuritySpec.isSendQuery t = true) qS
```

:::leanPillCaption "IND-CPA adversary B"
:::

```anchor kemMixReduction (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Security.Reduction.Average)
def kemMixReduction (A : Adversary P irl) (q : ℕ) : P.kem.IND_CPA_Adversary where
  State := P.PK × ℕ
  preChallenge pk := do pure (pk, ← epochChoice q)
  postChallenge
    | (_, 0), _, _ => pure false
    | (pk, e + 1), c, k => stoppedRun
        (simImpl P hMac irl (e + 1)
          { pk, ct1 := (P.inc.splitC c).1, ct2 := (P.inc.splitC c).2, key := k })
        (simStop (e + 1)) A (simInit P hMac)
```

:::leanPillCaption "key-derivation adversary C"
:::

```anchor kdfMixReduction (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Security.Reduction.Average)
def kdfMixReduction (A : Adversary P irl) (q : ℕ) : KDFContextAdversary P.EpochKey where
  State := ℕ
  context := do let e ← epochChoice q; pure (e, e)
  guess e x := kdfReduction P hMac irl A e x
```

::::

:::defTitle "mlkem_braid_security" "ML-KEM Braid security"
:::

::::theorem "mlkem_braid_security" (parent := "cka_protocols_mlkem_braid") (tags := "gh-244") (uses := "mlkem_braid_spec, scka_security, incremental_kem_scheme")
$`\todo`

:::leanPill "missing"
:::
::::
