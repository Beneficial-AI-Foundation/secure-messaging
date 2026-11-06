import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.SPQRStates
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessaging.SCKA.SPQR.Params
import SecureMessaging.SCKA.SPQR.Unchunked
import SecureMessaging.SCKA.SPQR.Chunked
import SecureMessaging.SCKA.SPQR.Construction
import SecureMessaging.SCKA.SPQR.Instances

/-! # Blueprint chapter: SPQR -/

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

-- The protocol atom nests its game cells, pills, and Lean excerpts in one block, whose compiled
-- code nests deeper than the code generator's default recursion limit.
set_option maxRecDepth 50000

#doc (Manual) "SPQR" =>

:::group "cka_protocols_spqr"
Sparse Post-Quantum Ratchet (SPQR).
:::

:::defTitle "spqr_parameters" "SPQR parameters"
:::

:::::::definition "spqr_parameters" (parent := "cka_protocols_spqr") (lean := "SPQR.Parameters, SPQR.Parameters.generate, SPQR.Parameters.generateRleak, SPQR.Parameters.encaps1, SPQR.Parameters.encaps1Rleak, SPQR.Parameters.encaps2, SPQR.Parameters.decaps, SPQR.Parameters.ekMatchesHeader") (tags := "gh-252") (uses := "incremental_kem_det, erasure_code_payload")
An *SPQR parameter set* $`P` consists of

- an {bpref "incremental_kem_det"}[incremental KEM with explicit coins]:
  - a shared-key space $`K`;
  - public keys $`\mathsf{pk}=(\mathsf{hdr},\mathsf{ek})` with header $`\mathsf{hdr}\in H` and
    vector $`\mathsf{ek}\in V` such that $`\mathsf{Valid}(\mathsf{hdr},\mathsf{ek})`;
  - ciphertexts $`c=(c_1,c_2)\in C_1\times C_2`;
  - algorithms $`\mathsf{KeyGen}`, $`\mathsf{Encaps}_1`, $`\mathsf{Encaps}_2`, $`\mathsf{Decaps}`;
  - coin distributions $`\mathcal D_K` and $`\mathcal D_1`;
- an epoch-key space $`E` and an epoch-key derivation
  $`\mathsf{KDF}_{\mathsf{OK}}:K\times\mathbb N\to E`;
- a tag space $`T`; and
- a symbol alphabet $`\Sigma` and four {bpref "erasure_code_payload"}[erasure codes] over
  $`\Sigma` with their {bpref "erasure_code_streaming"}[streaming] interface:
  - $`\mathsf{Code}_H`, $`\mathsf{Code}_V`, $`\mathsf{Code}_1`, and $`\mathsf{Code}_2`, with payloads
    $`H\times T`, $`V`, $`C_1`, and $`C_2\times T` respectively;
  - encoder algorithms $`\mathsf{Enc}_X` and $`\mathsf{Next}`, decoder algorithms $`\mathsf{Empty}_X`,
    $`\mathsf{Add}`, and $`\mathsf{Decode}`.

:::leanPillCaption "Parameters"
:::

```anchor SPQR_Parameters (project := ".") (module := SecureMessaging.SCKA.SPQR.Params)
structure Parameters (m : Type → Type u) [Monad m] where
  /-- KEM shared secret. -/
  K : Type
  /-- Encapsulation key. -/
  PK : Type
  /-- Decapsulation key. -/
  SK : Type
  /-- Ciphertext. -/
  C : Type
  /-- Incremental KEM with explicit coins. -/
  det : KEMScheme.IncrementalKEMDet m K PK SK C
  /-- Epoch key output by `KDF_OK`. -/
  EpochKey : Type
  /-- MAC tag. -/
  Mac : Type
  /-- Erasure-code symbol alphabet, shared by the four streams. -/
  Sym : Type
  /-- `KDF_OK(shared_secret, epoch)`. -/
  kdfOK : K → ℕ → EpochKey
  /-- Header stream, recovering `header ‖ mac`. -/
  ecpHdr : ErasureCodePayload (det.PKheader × Mac) Sym
  /-- Encapsulation-key-vector stream. -/
  ecpEk : ErasureCodePayload det.PKvector Sym
  /-- `ct₁` stream. -/
  ecpCt1 : ErasureCodePayload det.C₁ Sym
  /-- `ct₂` stream, recovering `ct₂ ‖ mac`. -/
  ecpCt2 : ErasureCodePayload (det.C₂ × Mac) Sym
```

:::leanPillCaption "KEM operations"
:::

```anchor SPQR_kemOperations (project := ".") (module := SecureMessaging.SCKA.SPQR.Params)
/-- Draws key-generation coins and generates a key pair from them. -/
def generate : m (P.PK × P.SK) := do
  let r ← P.det.sampleKeygen
  pure (P.det.keygenDet r)

/-- `generate`, also returning the drawn coins. -/
def generateRleak : m ((P.PK × P.SK) × P.det.KeygenRand) := do
  let r ← P.det.sampleKeygen
  pure (P.det.keygenDet r, r)

/-- Draws first-stage coins and runs the first encapsulation stage on a header. -/
def encaps1 (hdr : P.det.PKheader) : m (P.det.St × P.det.C₁ × P.K) := do
  let r ← P.det.sampleEncaps1
  pure (P.det.encaps1Det hdr r)

/-- `encaps1`, also returning the drawn coins. -/
def encaps1Rleak (hdr : P.det.PKheader) :
    m ((P.det.St × P.det.C₁ × P.K) × P.det.Encaps1Rand) := do
  let r ← P.det.sampleEncaps1
  pure (P.det.encaps1Det hdr r, r)

/-- The second encapsulation stage on the vector `ek` and the first-stage state `es`; the header
is an argument of the generic second stage. -/
def encaps2 (ek : P.det.PKvector) (es : P.det.St) (hdr : P.det.PKheader) : P.det.C₂ :=
  P.det.encaps2Det es hdr ek

/-- Decapsulates the ciphertext with components `ct1` and `ct2`. -/
def decaps (dk : P.SK) (ct1 : P.det.C₁) (ct2 : P.det.C₂) : Option P.K :=
  P.det.decapsDet dk (P.det.splitC.symm (ct1, ct2))

/-- Whether the vector `ek` and the header form a public key. -/
def ekMatchesHeader (ek : P.det.PKvector) (hdr : P.det.PKheader) : Bool :=
  P.det.validPK hdr ek
```
:::::::

:::defTitle "spqr_chunked_scheme" "SPQR protocol"
:::

:::::::definition "spqr_chunked_scheme" (parent := "cka_protocols_spqr") (lean := "SPQR.scheme") (tags := "gh-252, gh-263") (uses := "spqr_parameters, mlkem_braid_ratcheted_authenticator, scka_scheme, erasure_code_streaming")
Let $`P` be an {bpref "spqr_parameters"}[SPQR parameter set], $`\mathsf{Auth}` a
{bpref "mlkem_braid_ratcheted_authenticator"}[ratcheted authenticator] for the epoch keys $`E`, the
headers $`H`, the ciphertexts $`C_1\times C_2`, and the tags $`T` of $`P`, with initial-key space
$`\mathcal I_{\mathsf{CKA}}`, state space $`\mathcal S_{\mathsf{Auth}}`, and algorithms

- $`\mathsf{Init}:\mathcal I_{\mathsf{CKA}}\times\mathbb N\to\mathcal S_{\mathsf{Auth}}` and
  $`\mathsf{Update}:\mathcal S_{\mathsf{Auth}}\times\mathbb N\times E\to\mathcal S_{\mathsf{Auth}}`;
- $`\mathsf{Mac}_H:\mathcal S_{\mathsf{Auth}}\times\mathbb N\times H\to T` and
  $`\mathsf{Verify}_H:\mathcal S_{\mathsf{Auth}}\times\mathbb N\times H\times T\to\{\mathsf{true},\mathsf{false}\}`
  on headers;
- $`\mathsf{Mac}_C:\mathcal S_{\mathsf{Auth}}\times\mathbb N\times(C_1\times C_2)\to T` and
  $`\mathsf{Verify}_C:\mathcal S_{\mathsf{Auth}}\times\mathbb N\times(C_1\times C_2)\times T\to\{\mathsf{true},\mathsf{false}\}`
  on ciphertexts,

and $`\Init\text{-}\KeyGen\to I_{\mathsf{CKA}}\in\mathcal I_{\mathsf{CKA}}` a generator of its
initial keys. $`\mathsf{SPQR}(P,\mathsf{Auth},\Init\text{-}\KeyGen)`, Signal's implementation of
{bpref "mlkem_braid_spec"}[ML-KEM Braid], is the {bpref "scka_scheme"}[SCKA scheme] with
initial-key generator $`\Init\text{-}\KeyGen` and the algorithms below.

:::leanPillCaption "scheme"
:::

```anchor SPQR_scheme (project := ".") (module := SecureMessaging.SCKA.SPQR.Construction)
def scheme (P : Parameters m) [DecidableEq P.Sym]
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (sampleInitKey : m InitKey) :
    SCKAScheme m InitKey (PartyState P AuthState) (PartyState P AuthState)
      P.EpochKey (Message P.Sym) (SendRand P.det.KeygenRand P.det.Encaps1Rand) :=
  let sendSCKA (st : PartyState P AuthState) := do
    let r ← send P auth st
    pure (some (r.outputKey, r.msg, r.sendingEpoch, r.state))
  let sendRleakSCKA (st : PartyState P AuthState) := do
    let (r, rand) ← sendRleak P auth st
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

::::::gameGrid
:::::gameCell "\\textsf{States, messages, and transitions}" (kind := "game") (tag := "spqr-states")
$$`\begin{array}{rcl}
\textsf{encapsulation-key sender} & & \textsf{ciphertext sender}\\[0.5em]
(\mathsf{pk},\mathsf{sk})\gets\mathsf{KeyGen}() & & \\
(\mathsf{hdr},\mathsf{ek})\gets\mathsf{pk} & \xrightarrow{\hspace{2em}(\mathsf{hdr},\mathsf{tag})\hspace{2em}} & (\mathsf{encapsSt},\mathsf{ct1},k)\gets\mathsf{Encaps}_1(\mathsf{hdr})\\
 & & \mathsf{epochKey}\gets\mathsf{KDF}_{\mathsf{OK}}(k,\mathsf{ep})\\[0.3em]
 & \xleftarrow{\hspace{3.5em}\mathsf{ct1}\hspace{3.5em}} & \\[0.3em]
 & \xrightarrow{\hspace{3.5em}\mathsf{ek}\hspace{3.5em}} & \mathsf{ct2}\gets\mathsf{Encaps}_2(\mathsf{encapsSt},\mathsf{hdr},\mathsf{ek})\\[0.3em]
k\gets\mathsf{Decaps}(\mathsf{sk},(\mathsf{ct1},\mathsf{ct2})) & \xleftarrow{\hspace{2em}(\mathsf{ct2},\mathsf{tag})\hspace{2em}} & \\[0.5em]
\mathsf{epochKey}\gets\mathsf{KDF}_{\mathsf{OK}}(k,\mathsf{ep}) & &
\end{array}`

A is the encapsulation-key sender in odd epochs and B in even ones. The boxes are numbered in the
order a party visits them: 1 to 5 as encapsulation-key sender, 6 to 10 as ciphertext sender of the
next epoch. From 8 a party reaches 10 directly, when an $`\mathsf{EkCt1Ack}` chunk completes
$`\mathsf{ek}`, or through 9a or 9b.

:::spqrStates
:::

Every state also holds $`\mathsf{ep}` and $`\mathsf{auth}`, and states 8 to 9b hold $`\mathsf{hdr}`
and $`\mathsf{encapsSt}` for $`\mathsf{Encaps}_2`. The values of a state:

:::table +header (align := left)
*
  * Value
  * Meaning
*
  * $`\mathsf{ep}\in\mathbb N`
  * the current epoch
*
  * $`\mathsf{auth}\in\mathcal S_{\mathsf{Auth}}`
  * the authenticator state, ratcheted with the epoch key at $`\mathsf{SendCt1}` and $`\mathsf{RecvCt2}`
*
  * $`\mathsf{pk}=(\mathsf{hdr},\mathsf{ek})`, $`\mathsf{sk}`
  * the key pair of the encapsulation-key sender, with header $`\mathsf{hdr}\in H` and vector $`\mathsf{ek}\in V`
*
  * $`\mathsf{encapsSt}`
  * the state passed from $`\mathsf{Encaps}_1` to $`\mathsf{Encaps}_2` by the ciphertext sender
*
  * $`\mathsf{ct1}\in C_1`
  * the first ciphertext component
*
  * $`\mathsf{encoder}`
  * the encoder of the stream being sent
*
  * $`\mathsf{decoder}`
  * the decoder of the stream being received
:::

Orange arrows are sends that draw coins; the others are receives of a message $`\rho=(t,p)`,
labelled $`\mathsf{Rec}(p)` by its payload $`p`; $`t` is the sender's epoch:

:::table +header (align := left)
*
  * Payload $`p`
  * Meaning
*
  * $`\mathsf{Hdr}(\chunk)`
  * a chunk $`\chunk\in\mathbb N\times\Sigma` of the header stream
*
  * $`\mathsf{Ek}(\chunk)`
  * a chunk of the $`\mathsf{ek}` stream
*
  * $`\mathsf{EkCt1Ack}(\chunk)`
  * a chunk of the $`\mathsf{ek}` stream, and $`\mathsf{ct1}` has been recovered
*
  * $`\mathsf{Ct1Ack}`
  * $`\mathsf{ct1}` has been recovered, no chunk
*
  * $`\mathsf{Ct1}(\chunk)`
  * a chunk of the $`\mathsf{ct1}` stream
*
  * $`\mathsf{Ct2}(\chunk)`
  * a chunk of the $`\mathsf{ct2}` stream
*
  * $`\mathsf{None}`
  * nothing to send
:::

:::leanPillCaption "PartyState"
:::

```anchor Chunked_PartyState (project := ".") (module := SecureMessaging.SCKA.SPQR.Chunked)
inductive PartyState (P : Parameters m) (AuthState : Type) where
  /-- Before sampling an encapsulation key (`states.rs:17`). -/
  | keysUnsampled (core : EkSender.KeysUnsampled AuthState)
  /-- Sending the authenticated header stream (`states.rs:18`). -/
  | keysSampled (core : EkSender.HeaderSent P AuthState)
      (sendingHdr : EncoderState (P.det.PKheader × P.Mac) P.Sym)
  /-- Sending the vector and receiving the first ciphertext component (`states.rs:19-20`). -/
  | headerSent (core : EkSender.EkSent P AuthState)
      (sendingEk : EncoderState P.det.PKvector P.Sym)
      (receivingCt1 : DecoderState P.det.C₁ P.Sym)
  /-- Sending vector chunks that acknowledge complete first-ciphertext receipt
  (`states.rs:21`). -/
  | ct1Received (core : EkSender.EkSentCt1Received P AuthState)
      (sendingEk : EncoderState P.det.PKvector P.Sym)
  /-- Receiving the second ciphertext component (`states.rs:22`). -/
  | ekSentCt1Received (core : EkSender.EkSentCt1Received P AuthState)
      (receivingCt2 : DecoderState (P.det.C₂ × P.Mac) P.Sym)
  /-- Receiving the authenticated header stream (`states.rs:23`). -/
  | noHeaderReceived (core : CtSender.NoHeaderReceived AuthState)
      (receivingHdr : DecoderState (P.det.PKheader × P.Mac) P.Sym)
  /-- Receiving the encapsulation-key vector after authenticating the header
  (`states.rs:24`). -/
  | headerReceived (core : CtSender.HeaderReceived P AuthState)
      (receivingEk : DecoderState P.det.PKvector P.Sym)
  /-- Sending the first ciphertext component while receiving the vector
  (`states.rs:25`). -/
  | ct1Sampled (core : CtSender.Ct1Sent P AuthState)
      (sendingCt1 : EncoderState P.det.C₁ P.Sym)
      (receivingEk : DecoderState P.det.PKvector P.Sym)
  /-- Sending the first ciphertext after validating the vector (`states.rs:26`). -/
  | ekReceivedCt1Sampled (core : CtSender.Ct1SentEkReceived P AuthState)
      (sendingCt1 : EncoderState P.det.C₁ P.Sym)
  /-- Receiving the vector after the first ciphertext is acknowledged (`states.rs:27`). -/
  | ct1Acknowledged (core : CtSender.Ct1Sent P AuthState)
      (receivingEk : DecoderState P.det.PKvector P.Sym)
  /-- Sending the second ciphertext component (`states.rs:28`). -/
  | ct2Sampled (core : CtSender.Ct2Sent AuthState)
      (sendingCt2 : EncoderState (P.det.C₂ × P.Mac) P.Sym)
```

:::leanPillCaption "Payload"
:::

```anchor Chunked_Payload (project := ".") (module := SecureMessaging.SCKA.SPQR.Chunked)
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
```

:::leanPillCaption "Message"
:::

```anchor Chunked_Message (project := ".") (module := SecureMessaging.SCKA.SPQR.Chunked)
structure Message (Sym : Type) where
  /-- The epoch being negotiated. -/
  epoch : ℕ
  /-- The typed payload. -/
  payload : Payload Sym
```
:::::
::::::

::::::gameGrid
:::::gameCell "\\InitA(I_{\\mathsf{CKA}})" (kind := "compact") (tag := "spqr-init-a") (state := "\\textsf{A, encapsulation-key sender in epoch 1}")
$`\Return\mathsf{keysUnsampled}(1,\mathsf{Init}(I_{\mathsf{CKA}},1))`

:::leanPillCaption "initA"
:::

```anchor Chunked_initA (project := ".") (module := SecureMessaging.SCKA.SPQR.Chunked)
def initA (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (ik : InitKey) : PartyState P AuthState := .keysUnsampled ⟨1, auth.init ik 1⟩
```

:::::

:::::gameCell "\\InitB(I_{\\mathsf{CKA}})" (kind := "compact") (tag := "spqr-init-b") (state := "\\textsf{B, ciphertext sender in epoch 1}")
$`\Return\mathsf{noHeaderReceived}(1,\mathsf{Init}(I_{\mathsf{CKA}},1),\mathsf{Empty}_H)`

:::leanPillCaption "initB"
:::

```anchor Chunked_initB (project := ".") (module := SecureMessaging.SCKA.SPQR.Chunked)
def initB (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (ik : InitKey) : PartyState P AuthState :=
  .noHeaderReceived ⟨1, auth.init ik 1⟩ (DecoderState.empty P.ecpHdr)
```
:::::
::::::

::::::gameGrid
:::::gameCell "\\textsf{Send}" (kind := "game") (tag := "spqr-send")
$`\begin{array}{l}
\mathsf{Send}(\mathsf{st}):\pcomment{\mathsf{ep}\text{: the epoch of }\mathsf{st}}\\
\quad \mathsf{out}\gets(\bot,\bot);\quad\mathsf{st}'\gets\mathsf{st}\\[0.6em]
\quad\pcommentline{\text{first send of the epoch as encapsulation-key sender:}}\\
\quad\pcommentline{\text{sample the key pair and start streaming the tagged header}}\\
\quad\pif\ \mathsf{st}=\mathsf{keysUnsampled}(\mathsf{ep},\mathsf{auth})\ \pthen\\
\qquad(\mathsf{core},\mathsf{data})\gets\mathsf{SendHeader}(\mathsf{ep},\mathsf{auth})\\
\qquad(\chunk,\mathsf{encoder})\gets\mathsf{Next}(\mathsf{Enc}_H(\mathsf{data}));\quad\mathsf{st}'\gets\mathsf{keysSampled}(\mathsf{core},\mathsf{encoder})\\
\qquad p\gets\mathsf{Hdr}(\chunk)\\[0.6em]
\quad\pcommentline{\text{first send after the header was verified:}}\\
\quad\pcommentline{\text{encapsulate, output the epoch key, and start streaming }\mathsf{ct1}}\\
\quad\pelse\ \pif\ \mathsf{st}=\mathsf{headerReceived}(\mathsf{ep},\mathsf{auth},\mathsf{hdr},\mathsf{decoder})\ \pthen\\
\qquad(\mathsf{core},\mathsf{ct1},\mathsf{out})\gets\mathsf{SendCt1}(\mathsf{ep},\mathsf{auth},\mathsf{hdr})\\
\qquad(\chunk,\mathsf{encoder})\gets\mathsf{Next}(\mathsf{Enc}_1(\mathsf{ct1}))\\
\qquad\mathsf{st}'\gets\mathsf{ct1Sampled}(\mathsf{core},\mathsf{encoder},\mathsf{decoder})\\
\qquad p\gets\mathsf{Ct1}(\chunk)\\[0.6em]
\quad\pcommentline{\text{a stream is in progress: emit its next chunk}}\\
\quad\pelse\ \pif\ \mathsf{st}\in\{\mathsf{keysSampled},\mathsf{headerSent},\mathsf{ct1Received},\\
\qquad\qquad\mathsf{ct1Sampled},\mathsf{ekReceivedCt1Sampled},\mathsf{ct2Sampled}\}\ \pthen\\
\qquad\pcommentline{\mathsf{encoder}\text{: the encoder of }\mathsf{st}}\\
\qquad(\chunk,\mathsf{encoder}')\gets\mathsf{Next}(\mathsf{encoder});\quad\mathsf{st}'\gets\mathsf{st}[\mathsf{encoder}\mapsto\mathsf{encoder}']\\
\qquad p\gets\begin{cases}
\mathsf{Hdr}(\chunk)&\text{if }\mathsf{st}\in\mathsf{keysSampled}\pcomment{\text{header}}\\
\mathsf{Ek}(\chunk)&\text{if }\mathsf{st}\in\mathsf{headerSent}\pcomment{\mathsf{ek}}\\
\mathsf{EkCt1Ack}(\chunk)&\text{if }\mathsf{st}\in\mathsf{ct1Received}\pcomment{\mathsf{ek}\text{; }\mathsf{ct1}\text{ recovered}}\\
\mathsf{Ct1}(\chunk)&\text{if }\mathsf{st}\in\{\mathsf{ct1Sampled},\mathsf{ekReceivedCt1Sampled}\}\\
\mathsf{Ct2}(\chunk)&\text{if }\mathsf{st}\in\mathsf{ct2Sampled}\pcomment{(\mathsf{ct2},\mathsf{tag})}
\end{cases}\\[0.6em]
\quad\pcommentline{\mathsf{ek}\text{ got through: only acknowledge }\mathsf{ct1}}\\
\quad\pelse\ \pif\ \mathsf{st}\in\mathsf{ekSentCt1Received}\ \pthen\ p\gets\mathsf{Ct1Ack}\\[0.6em]
\quad\pcommentline{\text{waiting for the header, or for }\mathsf{ek}\text{ once }\mathsf{ct1}\text{ is acknowledged}}\\
\quad\pelse\ p\gets\mathsf{None}\\[0.6em]
\quad\Return(\mathsf{out},(\mathsf{ep},p),\mathsf{ep}-1,\mathsf{st}')
\end{array}`

$`\mathsf{Send}\text{-}\mathsf{rleak}(\mathsf{st})` runs $`\mathsf{Send}(\mathsf{st})` with
$`\mathsf{KeyGen}` and $`\mathsf{Encaps}_1` replaced by their
{bpref "incremental_kem_det"}[coin-returning variants] and also returns those coins: $`r_K` from
$`\mathsf{keysUnsampled}`, $`r_1` from $`\mathsf{headerReceived}`, and $`\bot` from every other state.

:::leanPillCaption "Chunked.send"
:::

```anchor Chunked_send (project := ".") (module := SecureMessaging.SCKA.SPQR.Chunked)
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
```

:::leanPillCaption "SendResult"
:::

```anchor Chunked_SendResult (project := ".") (module := SecureMessaging.SCKA.SPQR.Chunked)
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
```

:::leanPillCaption "SPQR.send"
:::

```anchor SPQR_send (project := ".") (module := SecureMessaging.SCKA.SPQR.Construction)
def send (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (st : PartyState P AuthState) : m (SendResult P AuthState) :=
  Chunked.send P auth st
```

:::leanPillCaption "sendRleak"
:::

```anchor SPQR_sendRleak (project := ".") (module := SecureMessaging.SCKA.SPQR.Construction)
def sendRleak (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (st : PartyState P AuthState) :
    m (SendResult P AuthState × SendRand P.det.KeygenRand P.det.Encaps1Rand) :=
  match st with
  | .keysUnsampled core => do
      let ((core', hdr, tag), r) ← EkSender.sendHeaderRleak P auth core
      let (chunk, enc) := (EncoderState.init P.ecpHdr (hdr, tag)).nextChunk
      pure (⟨⟨core.ep, .hdr chunk⟩, core.ep - 1, none, .keysSampled core' enc⟩, .keygen r)
  | .headerReceived core dec => do
      let ((core', c1, key), r) ← CtSender.sendCt1Rleak P auth core
      let (chunk, enc) := (EncoderState.init P.ecpCt1 c1).nextChunk
      pure (⟨⟨core.ep, .ct1 chunk⟩, core.ep - 1, some key, .ct1Sampled core' enc dec⟩, .encaps1 r)
  | st => (·, .none) <$> send P auth st
```

$$`\SendA=\SendB=\mathsf{Send},\quad\SendARLeak=\SendBRLeak=\mathsf{Send}\text{-}\mathsf{rleak}`
:::::

:::::gameCell "\\textsf{Send helpers}" (kind := "compact")
$`\begin{array}{l}
\mathsf{SendHeader}(\mathsf{ep},\mathsf{auth})\\
\hline
\pcommentline{\text{encapsulation-key sender}}\\
(\mathsf{pk},\mathsf{sk})\gets\mathsf{KeyGen}()\\
(\mathsf{hdr},\mathsf{ek})\gets \mathsf{pk}\\
\mathsf{tag}\gets\mathsf{Mac}_H(\mathsf{auth},\mathsf{ep},\mathsf{hdr})\\
\Return((\mathsf{ep},\mathsf{auth},\mathsf{pk},\mathsf{sk}),(\mathsf{hdr},\mathsf{tag}))
\end{array}`

:::leanPillCaption "sendHeader"
:::

```anchor EkSender_sendHeader (project := ".") (module := SecureMessaging.SCKA.SPQR.Unchunked)
/-- Generate a key pair and return the successor state, the header, and its tag. -/
def sendHeader (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (st : KeysUnsampled AuthState) : m (HeaderSent P AuthState × P.det.PKheader × P.Mac) := do
  let (pk, sk) ← P.generate
  let hdr := P.det.toHeader pk
  pure (⟨st.ep, st.authSt, pk, sk⟩, hdr, auth.macHeader st.authSt st.ep hdr)
```

:::leanPillCaption "sendHeaderRleak"
:::

```anchor EkSender_sendHeaderRleak (project := ".") (module := SecureMessaging.SCKA.SPQR.Unchunked)
/-- `sendHeader` with `generate` replaced by `generateRleak`, also returning the drawn coins. -/
def sendHeaderRleak (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (st : KeysUnsampled AuthState) :
    m ((HeaderSent P AuthState × P.det.PKheader × P.Mac) × P.det.KeygenRand) := do
  let ((pk, sk), r) ← P.generateRleak
  let hdr := P.det.toHeader pk
  pure ((⟨st.ep, st.authSt, pk, sk⟩, hdr, auth.macHeader st.authSt st.ep hdr), r)
```

$`\begin{array}{l}
\mathsf{SendCt1}(\mathsf{ep},\mathsf{auth},\mathsf{hdr})\\
\hline
\pcommentline{\text{ciphertext sender}}\\
(\mathsf{encapsSt},\mathsf{ct1},k)\gets\mathsf{Encaps}_1(\mathsf{hdr})\\
\mathsf{epochKey}\gets\mathsf{KDF}_{\mathsf{OK}}(k,\mathsf{ep})\\
 \mathsf{auth}'\gets\mathsf{Update}(\mathsf{auth},\mathsf{ep},\mathsf{epochKey})\\
\Return((\mathsf{ep},\mathsf{auth}',\mathsf{hdr},\mathsf{encapsSt},\mathsf{ct1}),\\
\qquad\mathsf{ct1},(\mathsf{ep},\mathsf{epochKey}))
\end{array}`

:::leanPillCaption "sendCt1"
:::

```anchor CtSender_sendCt1 (project := ".") (module := SecureMessaging.SCKA.SPQR.Unchunked)
/-- Run the first encapsulation stage and return the successor state, the first ciphertext
component, and the epoch key. -/
def sendCt1 (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (st : HeaderReceived P AuthState) :
    m (Ct1Sent P AuthState × P.det.C₁ × (ℕ × P.EpochKey)) := do
  let (encapsSt, c1, k) ← P.encaps1 st.hdr
  let ik := P.kdfOK k st.ep
  pure (⟨st.ep, auth.update st.authSt st.ep ik, st.hdr, encapsSt, c1⟩, c1, (st.ep, ik))
```

:::leanPillCaption "sendCt1Rleak"
:::

```anchor CtSender_sendCt1Rleak (project := ".") (module := SecureMessaging.SCKA.SPQR.Unchunked)
/-- `sendCt1` with `encaps1` replaced by `encaps1Rleak`, also returning the drawn coins. -/
def sendCt1Rleak (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (st : HeaderReceived P AuthState) :
    m ((Ct1Sent P AuthState × P.det.C₁ × (ℕ × P.EpochKey)) × P.det.Encaps1Rand) := do
  let ((encapsSt, c1, k), r) ← P.encaps1Rleak st.hdr
  let ik := P.kdfOK k st.ep
  pure ((⟨st.ep, auth.update st.authSt st.ep ik, st.hdr, encapsSt, c1⟩, c1, (st.ep, ik)), r)
```
:::::
::::::

::::::gameGrid
:::::gameCell "\\textsf{Receive}" (kind := "game") (tag := "spqr-receive")
$`\begin{array}{l}
\mathsf{Rec}(\mathsf{st},(t,p)):\pcomment{\mathsf{ep}\text{: the epoch of }\mathsf{st}}\\
\quad\pif\ t<\mathsf{ep}\ \pthen\ \Return((\bot,\bot),t-1,\mathsf{st})\pcomment{\text{earlier epoch: ignored}}\\[0.6em]
\quad\pcommentline{\text{later epoch: accepted only while }\mathsf{ct2}\text{ is being streamed,}}\\
\quad\pcommentline{\text{otherwise rejected with }\mathsf{epochOutOfRange}}\\
\quad\pif\ t>\mathsf{ep}\ \pthen\\
\qquad\req\mathsf{st}=\mathsf{ct2Sampled}(\mathsf{ep},\mathsf{auth},\mathsf{encoder})\\
\qquad\mathsf{core}\gets\mathsf{RecvNextEpoch}((\mathsf{ep},\mathsf{auth}),t)\\
\qquad\Return((\bot,\bot),t-1,\mathsf{keysUnsampled}(\mathsf{core}))\pcomment{\text{epoch }t\text{ as key sender}}\\[0.6em]
\quad \mathsf{out}\gets(\bot,\bot);\quad\mathsf{st}'\gets\mathsf{st}\pcomment{\text{pairs not listed below are ignored}}\\[0.6em]
\quad\pcommentline{\text{first }\mathsf{ct1}\text{ chunk while streaming the header:}}\\
\quad\pcommentline{\text{the header got through, so release }\mathsf{ek}}\\
\quad\pif\ \mathsf{st}=\mathsf{keysSampled}(\mathsf{ep},\mathsf{auth},\mathsf{pk},\mathsf{sk},\mathsf{encoder})\wedge p=\mathsf{Ct1}(\chunk)\ \pthen\\
\qquad(\mathsf{core},\mathsf{ek})\gets\mathsf{SendEk}(\mathsf{ep},\mathsf{auth},\mathsf{pk},\mathsf{sk})\\
\qquad\mathsf{st}'\gets\mathsf{headerSent}(\mathsf{core},\mathsf{Enc}_V(\mathsf{ek}),\mathsf{Add}(\mathsf{Empty}_1,\chunk))\\[0.6em]
\quad\pcommentline{\mathsf{ct1}\text{ chunk while streaming }\mathsf{ek}\text{: collect }\mathsf{ct1}\text{; once decoded, store it}}\\
\quad\pelse\ \pif\ \mathsf{st}=\mathsf{headerSent}(\mathsf{ep},\mathsf{auth},\mathsf{sk},\mathsf{encoder},\mathsf{decoder})\wedge p=\mathsf{Ct1}(\chunk)\ \pthen\\
\qquad\mathsf{decoder}\gets\mathsf{Add}(\mathsf{decoder},\chunk);\quad \mathsf{ct1}\gets\mathsf{Decode}(\mathsf{decoder})\\
\qquad\pif\ \mathsf{ct1}=\bot\ \pthen\ \mathsf{st}'\gets\mathsf{headerSent}(\mathsf{ep},\mathsf{auth},\mathsf{sk},\mathsf{encoder},\mathsf{decoder})\\
\qquad\pelse\ \mathsf{st}'\gets\mathsf{ct1Received}(\mathsf{RecvCt1}((\mathsf{ep},\mathsf{auth},\mathsf{sk}),\mathsf{ct1}),\mathsf{encoder})\\[0.6em]
\quad\pcommentline{\text{first }\mathsf{ct2}\text{ chunk: }\mathsf{ek}\text{ got through, so start collecting }\mathsf{ct2}}\\
\quad\pelse\ \pif\ \mathsf{st}=\mathsf{ct1Received}(\mathsf{ep},\mathsf{auth},\mathsf{sk},\mathsf{ct1},\mathsf{encoder})\wedge p=\mathsf{Ct2}(\chunk)\ \pthen\\
\qquad\mathsf{st}'\gets\mathsf{ekSentCt1Received}(\mathsf{ep},\mathsf{auth},\mathsf{sk},\mathsf{ct1},\mathsf{Add}(\mathsf{Empty}_2,\chunk))\\[0.6em]
\quad\pcommentline{\mathsf{ct2}\text{ chunk: once decoded, decapsulate, output the epoch key,}}\\
\quad\pcommentline{\text{and enter the next epoch as ciphertext sender}}\\
\quad\pelse\ \pif\ \mathsf{st}=\mathsf{ekSentCt1Received}(\mathsf{ep},\mathsf{auth},\mathsf{sk},\mathsf{ct1},\mathsf{decoder})\wedge p=\mathsf{Ct2}(\chunk)\ \pthen\\
\qquad\mathsf{decoder}\gets\mathsf{Add}(\mathsf{decoder},\chunk);\quad \mathsf{data}\gets\mathsf{Decode}(\mathsf{decoder})\\
\qquad\pif\ \mathsf{data}=\bot\ \pthen\ \mathsf{st}'\gets\mathsf{ekSentCt1Received}(\mathsf{ep},\mathsf{auth},\mathsf{sk},\mathsf{ct1},\mathsf{decoder})\\
\qquad\pelse\ (\mathsf{core},\mathsf{out})\gets\mathsf{RecvCt2}((\mathsf{ep},\mathsf{auth},\mathsf{sk},\mathsf{ct1}),\mathsf{data})\\
\qquad\quad\ \ \mathsf{st}'\gets\mathsf{noHeaderReceived}(\mathsf{core},\mathsf{Empty}_H)\\
\qquad\quad\pcommentline{\bot\text{ on a bad tag: }\mathsf{macVerifyFailed}}\\[0.6em]
\quad\pcommentline{\text{header chunk: once decoded, verify the header tag}}\\
\quad\pelse\ \pif\ \mathsf{st}=\mathsf{noHeaderReceived}(\mathsf{ep},\mathsf{auth},\mathsf{decoder})\wedge p=\mathsf{Hdr}(\chunk)\ \pthen\\
\qquad\mathsf{decoder}\gets\mathsf{Add}(\mathsf{decoder},\chunk);\quad \mathsf{data}\gets\mathsf{Decode}(\mathsf{decoder})\\
\qquad\pif\ \mathsf{data}=\bot\ \pthen\ \mathsf{st}'\gets\mathsf{noHeaderReceived}(\mathsf{ep},\mathsf{auth},\mathsf{decoder})\\
\qquad\pelse\ \mathsf{st}'\gets\mathsf{headerReceived}(\mathsf{RecvHeader}((\mathsf{ep},\mathsf{auth}),\mathsf{data}),\mathsf{Empty}_V)\\
\qquad\quad\pcommentline{\bot\text{ on a bad tag: }\mathsf{macVerifyFailed}}\\[0.6em]
\quad\pcommentline{\mathsf{ek}\text{ chunk while streaming }\mathsf{ct1}\text{: once decoded, validate }\mathsf{ek}}\\
\quad\pelse\ \pif\ \mathsf{st}=\mathsf{ct1Sampled}(\mathsf{ep},\mathsf{auth},\mathsf{hdr},\mathsf{encapsSt},\mathsf{ct1},\mathsf{encoder},\mathsf{decoder})\\
\qquad\qquad\wedge p=\mathsf{Ek}(\chunk)\ \pthen\\
\qquad\mathsf{decoder}\gets\mathsf{Add}(\mathsf{decoder},\chunk);\quad \mathsf{ek}\gets\mathsf{Decode}(\mathsf{decoder})\\
\qquad\pif\ \mathsf{ek}=\bot\ \pthen\\
\qquad\quad\mathsf{st}'\gets\mathsf{ct1Sampled}(\mathsf{ep},\mathsf{auth},\mathsf{hdr},\mathsf{encapsSt},\mathsf{ct1},\mathsf{encoder},\mathsf{decoder})\\
\qquad\pelse\ \mathsf{core}\gets\mathsf{RecvEk}((\mathsf{ep},\mathsf{auth},\mathsf{hdr},\mathsf{encapsSt},\mathsf{ct1}),\mathsf{ek})\\
\qquad\quad\ \ \mathsf{st}'\gets\mathsf{ekReceivedCt1Sampled}(\mathsf{core},\mathsf{encoder})\\
\qquad\quad\pcommentline{\bot\text{ when }\mathsf{ek}\text{ does not match }\mathsf{hdr}\text{: }\mathsf{erroneousDataReceived}}\\[0.6em]
\quad\pcommentline{\mathsf{ek}\text{ chunk acknowledging }\mathsf{ct1}\text{: stop streaming }\mathsf{ct1}\text{;}}\\
\quad\pcommentline{\text{once }\mathsf{ek}\text{ is decoded, validate it and compute }\mathsf{ct2}}\\
\quad\pelse\ \pif\ \mathsf{st}=\mathsf{ct1Sampled}(\mathsf{ep},\mathsf{auth},\mathsf{hdr},\mathsf{encapsSt},\mathsf{ct1},\mathsf{encoder},\mathsf{decoder})\\
\qquad\qquad\wedge p=\mathsf{EkCt1Ack}(\chunk)\ \pthen\\
\qquad\mathsf{decoder}\gets\mathsf{Add}(\mathsf{decoder},\chunk);\quad \mathsf{ek}\gets\mathsf{Decode}(\mathsf{decoder})\\
\qquad\pif\ \mathsf{ek}=\bot\ \pthen\\
\qquad\quad\mathsf{st}'\gets\mathsf{ct1Acknowledged}(\mathsf{ep},\mathsf{auth},\mathsf{hdr},\mathsf{encapsSt},\mathsf{ct1},\mathsf{decoder})\\
\qquad\pelse\ \mathsf{core}\gets\mathsf{RecvEk}((\mathsf{ep},\mathsf{auth},\mathsf{hdr},\mathsf{encapsSt},\mathsf{ct1}),\mathsf{ek})\\
\qquad\quad\pcommentline{\bot\text{ when }\mathsf{ek}\text{ does not match }\mathsf{hdr}\text{: }\mathsf{erroneousDataReceived}}\\
\qquad\quad\ \ (\mathsf{core}',\mathsf{data})\gets\mathsf{SendCt2}(\mathsf{core})\\
\qquad\quad\ \ \mathsf{st}'\gets\mathsf{ct2Sampled}(\mathsf{core}',\mathsf{Enc}_2(\mathsf{data}))\\[0.6em]
\quad\pcommentline{\mathsf{ct1}\text{ acknowledged after }\mathsf{ek}\text{ was validated: compute }\mathsf{ct2}}\\
\quad\pelse\ \pif\ \mathsf{st}=\mathsf{ekReceivedCt1Sampled}(\mathsf{core},\mathsf{encoder})\\
\qquad\qquad\wedge(p=\mathsf{Ct1Ack}\vee p=\mathsf{EkCt1Ack}(\chunk))\ \pthen\\
\qquad(\mathsf{core}',\mathsf{data})\gets\mathsf{SendCt2}(\mathsf{core})\\
\qquad\mathsf{st}'\gets\mathsf{ct2Sampled}(\mathsf{core}',\mathsf{Enc}_2(\mathsf{data}))\\[0.6em]
\quad\pcommentline{\mathsf{ek}\text{ chunk after }\mathsf{ct1}\text{ was acknowledged:}}\\
\quad\pcommentline{\text{once decoded, validate }\mathsf{ek}\text{ and compute }\mathsf{ct2}}\\
\quad\pelse\ \pif\ \mathsf{st}=\mathsf{ct1Acknowledged}(\mathsf{ep},\mathsf{auth},\mathsf{hdr},\mathsf{encapsSt},\mathsf{ct1},\mathsf{decoder})\\
\qquad\qquad\wedge p\in\{\mathsf{Ek}(\chunk),\mathsf{EkCt1Ack}(\chunk)\}\ \pthen\\
\qquad\mathsf{decoder}\gets\mathsf{Add}(\mathsf{decoder},\chunk);\quad \mathsf{ek}\gets\mathsf{Decode}(\mathsf{decoder})\\
\qquad\pif\ \mathsf{ek}=\bot\ \pthen\\
\qquad\quad\mathsf{st}'\gets\mathsf{ct1Acknowledged}(\mathsf{ep},\mathsf{auth},\mathsf{hdr},\mathsf{encapsSt},\mathsf{ct1},\mathsf{decoder})\\
\qquad\pelse\ \mathsf{core}\gets\mathsf{RecvEk}((\mathsf{ep},\mathsf{auth},\mathsf{hdr},\mathsf{encapsSt},\mathsf{ct1}),\mathsf{ek})\\
\qquad\quad\pcommentline{\bot\text{ when }\mathsf{ek}\text{ does not match }\mathsf{hdr}\text{: }\mathsf{erroneousDataReceived}}\\
\qquad\quad\ \ (\mathsf{core}',\mathsf{data})\gets\mathsf{SendCt2}(\mathsf{core})\\
\qquad\quad\ \ \mathsf{st}'\gets\mathsf{ct2Sampled}(\mathsf{core}',\mathsf{Enc}_2(\mathsf{data}))\\[0.6em]
\quad\Return(\mathsf{out},t-1,\mathsf{st}')
\end{array}`

:::leanPillCaption "recv"
:::

```anchor Chunked_recv (project := ".") (module := SecureMessaging.SCKA.SPQR.Chunked)
def recv (P : Parameters m) [DecidableEq P.Sym]
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
            ((DecoderState.empty P.ecpCt1).addChunk chunk)⟩
    | .headerSent core enc dec, .ct1 chunk =>
        -- states.rs:307-330, cell 3
        let dec' := dec.addChunk chunk
        match dec'.decodedPayload with
        | some c1 => .ok ⟨msg.epoch - 1, none, .ct1Received (EkSender.recvCt1 P core c1) enc⟩
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
            match EkSender.recvCt2 P auth core c2 tag with
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
            match CtSender.recvHeader P auth core hdr tag with
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
        | some ek =>
            match CtSender.recvEk P core ek with
            | some core' => .ok ⟨msg.epoch - 1, none, .ekReceivedCt1Sampled core' enc⟩
            | none => .error .erroneousDataReceived
        | none => .ok ⟨msg.epoch - 1, none, .ct1Sampled core enc dec'⟩
    | .ct1Sampled core _ dec, .ekCt1Ack chunk =>
        -- states.rs:412-458, cell 9
        let dec' := dec.addChunk chunk
        match dec'.decodedPayload with
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
        let dec' := dec.addChunk chunk
        match dec'.decodedPayload with
        | some ek =>
            match CtSender.recvEk P core ek with
            | some core' => .ok ⟨msg.epoch - 1, none, completeCt2 P auth core'⟩
            | none => .error .erroneousDataReceived
        | none => .ok ⟨msg.epoch - 1, none, .ct1Acknowledged core dec'⟩
    | .ct1Acknowledged core dec, .ekCt1Ack chunk =>
        -- states.rs:479-520, cell 15
        let dec' := dec.addChunk chunk
        match dec'.decodedPayload with
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
```

:::leanPillCaption "completeCt2"
:::

```anchor Chunked_completeCt2 (project := ".") (module := SecureMessaging.SCKA.SPQR.Chunked)
def completeCt2 (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (core : CtSender.Ct1SentEkReceived P AuthState) : PartyState P AuthState :=
  let c2 := P.encaps2 core.ek core.encapsSt core.hdr
  let tag := auth.macCiphertext core.authSt core.ep (core.c1, c2)
  .ct2Sampled ⟨core.ep, core.authSt⟩ (EncoderState.init P.ecpCt2 (c2, tag))
```

:::leanPillCaption "Error"
:::

```anchor Chunked_Error (project := ".") (module := SecureMessaging.SCKA.SPQR.Chunked)
inductive Error where
  /-- The message epoch is ahead of the state. -/
  | epochOutOfRange (epoch : ℕ)
  /-- A header or ciphertext tag was rejected, or deterministic decapsulation refused the
  ciphertext; ML-KEM never refuses. -/
  | macVerifyFailed
  /-- The received vector failed validation. -/
  | erroneousDataReceived
```

:::leanPillCaption "RecvResult"
:::

```anchor Chunked_RecvResult (project := ".") (module := SecureMessaging.SCKA.SPQR.Chunked)
structure RecvResult (P : Parameters m) (AuthState : Type) where
  /-- The incoming message epoch minus one. -/
  receivingEpoch : ℕ
  /-- The epoch key derived by this receive, if any. -/
  outputKey : Option (ℕ × P.EpochKey)
  /-- The state after the receive. -/
  state : PartyState P AuthState
```

:::leanPillCaption "recvSCKA"
:::

```anchor SPQR_recvSCKA (project := ".") (module := SecureMessaging.SCKA.SPQR.Construction)
def recvSCKA (P : Parameters m) [DecidableEq P.Sym]
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (st : PartyState P AuthState) (msg : Message P.Sym) :
    Option (Option (ℕ × P.EpochKey) × ℕ × PartyState P AuthState) := match recv P auth st msg with
  | .error _ => none
  | .ok r => some (r.outputKey, r.receivingEpoch, r.state)
```

$$`\RecA=\RecB=\mathsf{Rec}`
:::::

:::::gameCell "\\textsf{Receive helpers}" (kind := "compact")
$`\begin{array}{l}
\mathsf{RecvNextEpoch}((\mathsf{ep},\mathsf{auth}),t)\\
\hline
\pcommentline{\text{ciphertext sender}}\\
\req t=\mathsf{ep}+1\\
\Return(\mathsf{ep}+1,\mathsf{auth})
\end{array}`

:::leanPillCaption "recvNextEpoch"
:::

```anchor CtSender_recvNextEpoch (project := ".") (module := SecureMessaging.SCKA.SPQR.Unchunked)
/-- Return the encapsulation-key-sender state exactly when `t` is the successor epoch. -/
def recvNextEpoch (st : Ct2Sent AuthState) (t : ℕ) : Option (EkSender.KeysUnsampled AuthState) :=
  if t = st.ep + 1 then some ⟨st.ep + 1, st.authSt⟩ else none
```

$`\begin{array}{l}
\mathsf{SendEk}(\mathsf{ep},\mathsf{auth},\mathsf{pk},\mathsf{sk})\\
\hline
\pcommentline{\text{encapsulation-key sender}}\\
(\mathsf{hdr},\mathsf{ek})\gets \mathsf{pk}\\
\Return((\mathsf{ep},\mathsf{auth},\mathsf{sk}),\mathsf{ek})
\end{array}`

:::leanPillCaption "sendEk"
:::

```anchor EkSender_sendEk (project := ".") (module := SecureMessaging.SCKA.SPQR.Unchunked)
/-- Return the successor state and the vector `ek` of the stored public key. -/
def sendEk (P : Parameters m) (st : HeaderSent P AuthState) :
    EkSent P AuthState × P.det.PKvector :=
  (⟨st.ep, st.authSt, st.sk⟩, P.det.toVector st.pk)
```

$`\begin{array}{l}
\mathsf{RecvCt1}((\mathsf{ep},\mathsf{auth},\mathsf{sk}),\mathsf{ct1})\\
\hline
\pcommentline{\text{encapsulation-key sender}}\\
\Return(\mathsf{ep},\mathsf{auth},\mathsf{sk},\mathsf{ct1})
\end{array}`

:::leanPillCaption "recvCt1"
:::

```anchor EkSender_recvCt1 (project := ".") (module := SecureMessaging.SCKA.SPQR.Unchunked)
/-- Store the first ciphertext component. -/
def recvCt1 (P : Parameters m) (st : EkSent P AuthState)
    (c1 : P.det.C₁) : EkSentCt1Received P AuthState :=
  ⟨st.ep, st.authSt, st.sk, c1⟩
```

$`\begin{array}{l}
\mathsf{RecvCt2}((\mathsf{ep},\mathsf{auth},\mathsf{sk},\mathsf{ct1}),(\mathsf{ct2},\mathsf{tag}))\\
\hline
\pcommentline{\text{encapsulation-key sender}}\\
k\gets\mathsf{Decaps}(\mathsf{sk},(\mathsf{ct1},\mathsf{ct2}))\\
\req k\ne\bot\\
\mathsf{epochKey}\gets\mathsf{KDF}_{\mathsf{OK}}(k,\mathsf{ep})\\
 \mathsf{auth}'\gets\mathsf{Update}(\mathsf{auth},\mathsf{ep},\mathsf{epochKey})\\
\req\mathsf{Verify}_C(\mathsf{auth}',\mathsf{ep},(\mathsf{ct1},\mathsf{ct2}),\mathsf{tag})\\
\Return((\mathsf{ep}+1,\mathsf{auth}'),(\mathsf{ep},\mathsf{epochKey}))
\end{array}`

:::leanPillCaption "recvCt2"
:::

```anchor EkSender_recvCt2 (project := ".") (module := SecureMessaging.SCKA.SPQR.Unchunked)
/-- Decapsulate and authenticate the ciphertext, returning the next role state and epoch key. -/
def recvCt2 (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (st : EkSentCt1Received P AuthState) (c2 : P.det.C₂) (tag : P.Mac) :
    Option (CtSender.NoHeaderReceived AuthState × (ℕ × P.EpochKey)) :=
  match P.decaps st.sk st.c1 c2 with
  | none => none
  | some k =>
    let ik := P.kdfOK k st.ep
    let authSt' := auth.update st.authSt st.ep ik
    if auth.verifyCiphertext authSt' st.ep (st.c1, c2) tag then
      some (⟨st.ep + 1, authSt'⟩, (st.ep, ik))
    else none
```

$`\begin{array}{l}
\mathsf{RecvHeader}((\mathsf{ep},\mathsf{auth}),(\mathsf{hdr},\mathsf{tag}))\\
\hline
\pcommentline{\text{ciphertext sender}}\\
\req\mathsf{Verify}_H(\mathsf{auth},\mathsf{ep},\mathsf{hdr},\mathsf{tag})\\
\Return(\mathsf{ep},\mathsf{auth},\mathsf{hdr})
\end{array}`

:::leanPillCaption "recvHeader"
:::

```anchor CtSender_recvHeader (project := ".") (module := SecureMessaging.SCKA.SPQR.Unchunked)
/-- Verify the header tag and return the successor state on success. -/
def recvHeader (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (st : NoHeaderReceived AuthState) (hdr : P.det.PKheader) (tag : P.Mac) :
    Option (HeaderReceived P AuthState) :=
  if auth.verifyHeader st.authSt st.ep hdr tag then some ⟨st.ep, st.authSt, hdr⟩ else none
```

$`\begin{array}{l}
\mathsf{RecvEk}((\mathsf{ep},\mathsf{auth},\mathsf{hdr},\mathsf{encapsSt},\mathsf{ct1}),\mathsf{ek})\\
\hline
\pcommentline{\text{ciphertext sender}}\\
\req\mathsf{Valid}(\mathsf{hdr},\mathsf{ek})\\
\Return(\mathsf{ep},\mathsf{auth},\mathsf{hdr},\mathsf{encapsSt},\mathsf{ct1},\mathsf{ek})
\end{array}`

:::leanPillCaption "recvEk"
:::

```anchor CtSender_recvEk (project := ".") (module := SecureMessaging.SCKA.SPQR.Unchunked)
/-- Accept the vector `ek` when it matches the stored header. -/
def recvEk (P : Parameters m) (st : Ct1Sent P AuthState)
    (ek : P.det.PKvector) : Option (Ct1SentEkReceived P AuthState) :=
  if P.ekMatchesHeader ek st.hdr then
    some ⟨st.ep, st.authSt, st.hdr, st.encapsSt, st.c1, ek⟩
  else none
```

$`\begin{array}{l}
\mathsf{SendCt2}(\mathsf{ep},\mathsf{auth},\mathsf{hdr},\mathsf{encapsSt},\mathsf{ct1},\mathsf{ek})\\
\hline
\pcommentline{\text{ciphertext sender}}\\
\mathsf{ct2}\gets\mathsf{Encaps}_2(\mathsf{encapsSt},\mathsf{hdr},\mathsf{ek})\\
\mathsf{tag}\gets\mathsf{Mac}_C(\mathsf{auth},\mathsf{ep},(\mathsf{ct1},\mathsf{ct2}))\\
\Return((\mathsf{ep},\mathsf{auth}),(\mathsf{ct2},\mathsf{tag}))
\end{array}`

:::leanPillCaption "sendCt2"
:::

```anchor CtSender_sendCt2 (project := ".") (module := SecureMessaging.SCKA.SPQR.Unchunked)
/-- Run the second encapsulation stage and return the successor state, the second ciphertext
component, and the ciphertext tag. -/
def sendCt2 (P : Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (st : Ct1SentEkReceived P AuthState) : Ct2Sent AuthState × P.det.C₂ × P.Mac :=
  let c2 := P.encaps2 st.ek st.encapsSt st.hdr
  (⟨st.ep, st.authSt⟩, c2, auth.macCiphertext st.authSt st.ep (st.c1, c2))
```
:::::
::::::
:::::::

:::defTitle "spqr_protocol_spec" "SPQR v1 instance"
:::

:::::::definition "spqr_protocol_spec" (parent := "cka_protocols_spqr") (lean := "SPQR.v1Incremental, SPQR.v1ErasureCodePayload, SPQR.v1Parameters, SPQR.v1Scheme") (tags := "gh-268") (uses := "spqr_parameters, spqr_chunked_scheme, spqr_reed_solomon_code, incremental_kem_from_ml_kem_spec")
The *v1 parameter set* $`P_{\mathsf{v1}}` uses
{bpref "incremental_kem_from_ml_kem_spec"}[ML-KEM-768 with explicit coins] and the
{bpref "spqr_reed_solomon_code"}[SPQR Reed–Solomon codes] over 32-byte symbols;
$`\mathsf{KDF}_{\mathsf{OK}}`, $`T`, the serializations, $`\mathsf{Auth}`, and
$`\Init\text{-}\KeyGen` remain parameters.

::::::gameGrid
:::::gameCell "\\textsf{Coin samplers}" (kind := "game")
$`\begin{array}{l}
\mathcal D_K=U(B_{64});\quad r_K=d\mathbin\Vert z\pcomment{d,z\in B_{32}}\\
\mathcal D_1=U(B_{32})\pcomment{U(B_n)\text{: uniform on the byte strings }B_n\text{ of length }n}
\end{array}`

:::leanPillCaption "mlkemIncrementalDet"
:::

```anchor mlkemIncrementalDet (project := ".") (module := SecureMessaging.KEM.IncrementalKEM.FromMLKEM)
def mlkemIncrementalDet (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p))) :
    IncrementalKEMDet ProbComp SharedSecret
      (EncapsulationKey (ParameterSet.params p)
        (Concrete.concreteEncoding (ParameterSet.params p)))
      (DecapsulationKey (ParameterSet.params p)
        (Concrete.concreteEncoding (ParameterSet.params p)))
      (Ciphertext (ParameterSet.params p)
        (Concrete.concreteEncoding (ParameterSet.params p))) :=
  let inc := mlkemIncremental p ring prims
  { PKheader := inc.PKheader
    PKvector := inc.PKvector
    C₁ := inc.C₁
    C₂ := inc.C₂
    St := inc.St
    KeygenRand := Bytes 64
    Encaps1Rand := Message
    validPK := inc.validPK
    splitPK := inc.splitPK
    splitC := inc.splitC
    keygenDet := fun r => keygenInternal ring
      (Concrete.concreteEncoding (ParameterSet.params p)) prims (r.take 32) (r.drop 32)
    encaps1Det := incrementalEncaps1 ring prims
    encaps2Det := fun st _hdr vec => incrementalEncaps2 ring st vec
    decapsDet := fun sk c => some (decapsInternal ring
      (Concrete.concreteEncoding (ParameterSet.params p)) prims sk c)
    sampleKeygen := $ᵗ Bytes 64
    sampleEncaps1 := $ᵗ Message }
```
:::::
::::::

:::table +header (align := left)
*
  * Stream $`X`
  * Payload
  * Sender
  * Threshold
*
  * $`H`
  * $`(\mathsf{hdr},\mathsf{tag})`
  * Encapsulation-key sender
  * 3
*
  * $`V`
  * $`\mathsf{ek}`
  * Encapsulation-key sender
  * 36
*
  * $`1`
  * $`\mathsf{ct1}`
  * Ciphertext sender
  * 30
*
  * $`2`
  * $`(\mathsf{ct2},\mathsf{tag})`
  * Ciphertext sender
  * 5
:::

:::leanPillCaption "v1Parameters"
:::

```anchor SPQR_v1Parameters (project := ".") (module := SecureMessaging.SCKA.SPQR.Instances)
noncomputable def v1Parameters {EpochKey Mac : Type}
    (kdfOK : MLKEM.SharedSecret → ℕ → EpochKey)
    (serializeHdr : v1Incremental.PKheader × Mac → Fin 3 → Chunk GF16)
    (parseHdr : (Fin 3 → Chunk GF16) → Option (v1Incremental.PKheader × Mac))
    (parseHdr_serializeHdr : ∀ payload, parseHdr (serializeHdr payload) = some payload)
    (serializeEk : v1Incremental.PKvector → Fin 36 → Chunk GF16)
    (parseEk : (Fin 36 → Chunk GF16) → Option v1Incremental.PKvector)
    (parseEk_serializeEk : ∀ payload, parseEk (serializeEk payload) = some payload)
    (serializeCt1 : v1Incremental.C₁ → Fin 30 → Chunk GF16)
    (parseCt1 : (Fin 30 → Chunk GF16) → Option v1Incremental.C₁)
    (parseCt1_serializeCt1 : ∀ payload, parseCt1 (serializeCt1 payload) = some payload)
    (serializeCt2 : v1Incremental.C₂ × Mac → Fin 5 → Chunk GF16)
    (parseCt2 : (Fin 5 → Chunk GF16) → Option (v1Incremental.C₂ × Mac))
    (parseCt2_serializeCt2 : ∀ payload, parseCt2 (serializeCt2 payload) = some payload) :
    Parameters ProbComp where
  K := MLKEM.SharedSecret
  PK := MLKEM.EncapsulationKey MLKEM.mlkem768 MLKEM.Concrete.mlkem768Encoding
  SK := MLKEM.DecapsulationKey MLKEM.mlkem768 MLKEM.Concrete.mlkem768Encoding
  C := MLKEM.Ciphertext MLKEM.mlkem768 MLKEM.Concrete.mlkem768Encoding
  det := v1Det
  EpochKey := EpochKey
  Mac := Mac
  Sym := Chunk GF16
  kdfOK := kdfOK
  ecpHdr := v1ErasureCodePayload 3 (by norm_num) (by norm_num) serializeHdr parseHdr
    parseHdr_serializeHdr
  ecpEk := v1ErasureCodePayload 36 (by norm_num) (by norm_num) serializeEk parseEk
    parseEk_serializeEk
  ecpCt1 := v1ErasureCodePayload 30 (by norm_num) (by norm_num) serializeCt1 parseCt1
    parseCt1_serializeCt1
  ecpCt2 := v1ErasureCodePayload 5 (by norm_num) (by norm_num) serializeCt2 parseCt2
    parseCt2_serializeCt2
```

:::leanPillCaption "v1Incremental"
:::

```anchor SPQR_v1Incremental (project := ".") (module := SecureMessaging.SCKA.SPQR.Instances)
abbrev v1Incremental : v1Det.toKEM.IncrementalStructure := v1Det.toIncremental
```

:::leanPillCaption "v1ErasureCodePayload"
:::

```anchor SPQR_v1ErasureCodePayload (project := ".") (module := SecureMessaging.SCKA.SPQR.Instances)
noncomputable def v1ErasureCodePayload {M : Type} (k : ℕ) (hk : k ≤ 2 ^ 16) (hk_pos : 0 < k)
    (serialize : M → Fin k → Chunk GF16) (parse : (Fin k → Chunk GF16) → Option M)
    (parse_serialize : ∀ payload, parse (serialize payload) = some payload) :
    ErasureCodePayload M (Chunk GF16) :=
  { ec := erasureCode k hk hk_pos, serialize, parse, parse_serialize }
```

:::leanPillCaption "v1Scheme"
:::

```anchor SPQR_v1Scheme (project := ".") (module := SecureMessaging.SCKA.SPQR.Instances)
noncomputable def v1Scheme {InitKey AuthState EpochKey Mac : Type}
    (kdfOK : MLKEM.SharedSecret → ℕ → EpochKey)
    (serializeHdr : v1Incremental.PKheader × Mac → Fin 3 → Chunk GF16)
    (parseHdr : (Fin 3 → Chunk GF16) → Option (v1Incremental.PKheader × Mac))
    (parseHdr_serializeHdr : ∀ payload, parseHdr (serializeHdr payload) = some payload)
    (serializeEk : v1Incremental.PKvector → Fin 36 → Chunk GF16)
    (parseEk : (Fin 36 → Chunk GF16) → Option v1Incremental.PKvector)
    (parseEk_serializeEk : ∀ payload, parseEk (serializeEk payload) = some payload)
    (serializeCt1 : v1Incremental.C₁ → Fin 30 → Chunk GF16)
    (parseCt1 : (Fin 30 → Chunk GF16) → Option v1Incremental.C₁)
    (parseCt1_serializeCt1 : ∀ payload, parseCt1 (serializeCt1 payload) = some payload)
    (serializeCt2 : v1Incremental.C₂ × Mac → Fin 5 → Chunk GF16)
    (parseCt2 : (Fin 5 → Chunk GF16) → Option (v1Incremental.C₂ × Mac))
    (parseCt2_serializeCt2 : ∀ payload, parseCt2 (serializeCt2 payload) = some payload)
    (auth : RatchetedAuthenticator InitKey EpochKey AuthState
      v1Incremental.PKheader (v1Incremental.C₁ × v1Incremental.C₂) Mac)
    (sampleInitKey : ProbComp InitKey) :
    SCKAScheme ProbComp InitKey
      (Chunked.PartyState (v1Parameters kdfOK serializeHdr parseHdr parseHdr_serializeHdr
        serializeEk parseEk parseEk_serializeEk serializeCt1 parseCt1 parseCt1_serializeCt1
        serializeCt2 parseCt2 parseCt2_serializeCt2) AuthState)
      (Chunked.PartyState (v1Parameters kdfOK serializeHdr parseHdr parseHdr_serializeHdr
        serializeEk parseEk parseEk_serializeEk serializeCt1 parseCt1 parseCt1_serializeCt1
        serializeCt2 parseCt2 parseCt2_serializeCt2) AuthState)
      EpochKey (Chunked.Message (Chunk GF16))
      (SendRand (MLKEM.Bytes 64) MLKEM.Message) := by
  letI : DecidableEq (v1Parameters kdfOK serializeHdr parseHdr parseHdr_serializeHdr
      serializeEk parseEk parseEk_serializeEk serializeCt1 parseCt1 parseCt1_serializeCt1
      serializeCt2 parseCt2 parseCt2_serializeCt2).Sym := by
    change DecidableEq (Chunk GF16)
    infer_instance
  exact scheme
    (v1Parameters kdfOK serializeHdr parseHdr parseHdr_serializeHdr serializeEk parseEk
      parseEk_serializeEk serializeCt1 parseCt1 parseCt1_serializeCt1 serializeCt2 parseCt2
      parseCt2_serializeCt2)
    auth
    sampleInitKey
```
:::::::

:::defTitle "spqr_protocol_correctness" "SPQR protocol correctness"
:::

::::theorem "spqr_protocol_correctness" (parent := "cka_protocols_spqr") (tags := "gh-269") (uses := "spqr_protocol_spec, scka_correctness, erasure_code_correctness")
$`\todo`

:::leanPill "missing"
:::
::::

:::defTitle "spqr_protocol_security" "SPQR protocol security"
:::

::::theorem "spqr_protocol_security" (parent := "cka_protocols_spqr") (tags := "gh-270") (uses := "spqr_protocol_spec, scka_security, erasure_code_scheme")
$`\todo`

:::leanPill "missing"
:::
::::

*References:*

- {Informal.citet SPQR}[]
- {Informal.citet MLKEM_Braid}[]
- {Informal.citet SCKA25}[]
