import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessaging.SCKA.SPQR.Unchunked
import SecureMessaging.SCKA.SPQR.Chunked
import SecureMessaging.SCKA.SPQR.Construction
import SecureMessaging.SCKA.SPQR.Correspondence
import SecureMessaging.SCKA.SPQR.Instances

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

#doc (Manual) "SPQR" =>

*References:*

- {Informal.citet SPQR}[]
- {Informal.citet MLKEM_Braid}[]
- {Informal.citet SCKA25}[]

:::group "cka_protocols_spqr"
Sparse Post-Quantum Ratchet (SPQR) ({Informal.citet SPQR}[]).
:::

:::group "spqr_unchunked_core"
Unchunked SPQR core.
:::

:::defTitle "spqr_unchunked_ek_sender" "SPQR unchunked encapsulation-key sender"
:::

::::definition "spqr_unchunked_ek_sender" (parent := "spqr_unchunked_core") (lean := "SPQR.EkSender.KeysUnsampled, SPQR.EkSender.HeaderSent, SPQR.EkSender.EkSent, SPQR.EkSender.EkSentCt1Received, SPQR.EkSender.sendHeader, SPQR.EkSender.sendVector, SPQR.EkSender.recvCt1, SPQR.EkSender.recvCt2")
$`\todo`

:::leanPillCaption "send authenticated encapsulation-key header"
:::

```anchor EkSender_sendHeader (project := ".") (module := SecureMessaging.SCKA.SPQR.Unchunked)
/-- Generate a KEM key pair and return the successor state, header, and tag. -/
def sendHeader (inc : kem.IncrementalStructure)
    (auth : RatchetedAuthenticator InitKey EpochKey AuthState inc.PKheader (inc.C₁ × inc.C₂) Mac)
    (st : KeysUnsampled AuthState) : m (HeaderSent inc AuthState × inc.PKheader × Mac) := do
  let (pk, sk) ← kem.keygen
  let hdr := inc.toHeader pk
  pure (⟨st.ep, st.authSt, pk, sk⟩, hdr, auth.macHeader st.authSt st.ep hdr)
```

:::leanPillCaption "send encapsulation-key vector"
:::

```anchor EkSender_sendVector (project := ".") (module := SecureMessaging.SCKA.SPQR.Unchunked)
/-- Return the successor state and the vector component of the stored encapsulation key. -/
def sendVector (inc : kem.IncrementalStructure) (st : HeaderSent inc AuthState) :
    EkSent inc AuthState × inc.PKvector :=
  (⟨st.ep, st.authSt, st.sk⟩, inc.toVector st.pk)
```

:::leanPillCaption "receive first ciphertext component"
:::

```anchor EkSender_recvCt1 (project := ".") (module := SecureMessaging.SCKA.SPQR.Unchunked)
/-- Store the first ciphertext component. -/
def recvCt1 (inc : kem.IncrementalStructure) (st : EkSent inc AuthState)
    (c1 : inc.C₁) : EkSentCt1Received inc AuthState :=
  ⟨st.ep, st.authSt, st.sk, c1⟩
```

:::leanPillCaption "receive second ciphertext component and tag"
:::

```anchor EkSender_recvCt2 (project := ".") (module := SecureMessaging.SCKA.SPQR.Unchunked)
/-- Decapsulate and authenticate the ciphertext, returning the next role state and epoch key. -/
def recvCt2 (inc : kem.IncrementalStructure)
    (auth : RatchetedAuthenticator InitKey EpochKey AuthState inc.PKheader (inc.C₁ × inc.C₂) Mac)
    (deriveEpochKey : EpochKeyDerivation K EpochKey) (hDet : DeterministicDecaps kem)
    (st : EkSentCt1Received inc AuthState) (c2 : inc.C₂) (tag : Mac) :
    Option (CtSender.NoHeaderReceived AuthState × (ℕ × EpochKey)) :=
  match hDet.decapsDet st.sk (inc.splitC.symm (st.c1, c2)) with
  | none => none
  | some k =>
    let ik := deriveEpochKey k st.ep
    let authSt' := auth.update st.authSt st.ep ik
    if auth.verifyCiphertext authSt' st.ep (st.c1, c2) tag then
      some (⟨st.ep + 1, authSt'⟩, (st.ep, ik))
    else none
```

{usesLabel}`uses` {uses "incremental_kem_scheme"}[] · {githubLabel}`github` {githubIssue 252}[]
::::

:::defTitle "spqr_unchunked_ct_sender" "SPQR unchunked ciphertext sender"
:::

::::definition "spqr_unchunked_ct_sender" (parent := "spqr_unchunked_core") (lean := "SPQR.CtSender.NoHeaderReceived, SPQR.CtSender.HeaderReceived, SPQR.CtSender.Ct1Sent, SPQR.CtSender.Ct1SentEkReceived, SPQR.CtSender.Ct2Sent, SPQR.CtSender.recvHeader, SPQR.CtSender.sendCt1, SPQR.CtSender.recvVector, SPQR.CtSender.sendCt2, SPQR.CtSender.recvNextEpoch")
$`\todo`

:::leanPillCaption "receive authenticated encapsulation-key header"
:::

```anchor CtSender_recvHeader (project := ".") (module := SecureMessaging.SCKA.SPQR.Unchunked)
/-- Verify the header tag and return the successor state on success. -/
def recvHeader (inc : kem.IncrementalStructure)
    (auth : RatchetedAuthenticator InitKey EpochKey AuthState inc.PKheader (inc.C₁ × inc.C₂) Mac)
    (st : NoHeaderReceived AuthState) (hdr : inc.PKheader) (tag : Mac) :
    Option (HeaderReceived inc AuthState) :=
  if auth.verifyHeader st.authSt st.ep hdr tag then some ⟨st.ep, st.authSt, hdr⟩ else none
```

:::leanPillCaption "send first ciphertext component"
:::

```anchor CtSender_sendCt1 (project := ".") (module := SecureMessaging.SCKA.SPQR.Unchunked)
/-- Run encapsulation stage one and return the successor state, ciphertext, and epoch key. -/
def sendCt1 (inc : kem.IncrementalStructure)
    (auth : RatchetedAuthenticator InitKey EpochKey AuthState inc.PKheader (inc.C₁ × inc.C₂) Mac)
    (deriveEpochKey : EpochKeyDerivation K EpochKey) (st : HeaderReceived inc AuthState) :
    m (Ct1Sent inc AuthState × inc.C₁ × (ℕ × EpochKey)) := do
  let (encapsSt, c1, k) ← inc.encaps1 st.hdr
  let ik := deriveEpochKey k st.ep
  pure (⟨st.ep, auth.update st.authSt st.ep ik, st.hdr, encapsSt, c1⟩, c1, (st.ep, ik))
```

:::leanPillCaption "receive encapsulation-key vector"
:::

```anchor CtSender_recvVector (project := ".") (module := SecureMessaging.SCKA.SPQR.Unchunked)
/-- Validate the encapsulation-key vector and return the successor state on success. -/
def recvVector (inc : kem.IncrementalStructure) (st : Ct1Sent inc AuthState)
    (vec : inc.PKvector) : Option (Ct1SentEkReceived inc AuthState) :=
  if inc.validPK st.hdr vec then
    some ⟨st.ep, st.authSt, st.hdr, st.encapsSt, st.c1, vec⟩
  else none
```

:::leanPillCaption "send second ciphertext component and tag"
:::

```anchor CtSender_sendCt2 (project := ".") (module := SecureMessaging.SCKA.SPQR.Unchunked)
/-- Run encapsulation stage two and return the successor state, ciphertext, and tag. -/
def sendCt2 (inc : kem.IncrementalStructure)
    (auth : RatchetedAuthenticator InitKey EpochKey AuthState inc.PKheader (inc.C₁ × inc.C₂) Mac)
    (st : Ct1SentEkReceived inc AuthState) : m (Ct2Sent AuthState × inc.C₂ × Mac) := do
  let c2 ← inc.encaps2 st.encapsSt st.hdr st.vec
  pure (⟨st.ep, st.authSt⟩, c2, auth.macCiphertext st.authSt st.ep (st.c1, c2))
```

:::leanPillCaption "advance to the next epoch"
:::

```anchor CtSender_recvNextEpoch (project := ".") (module := SecureMessaging.SCKA.SPQR.Unchunked)
/-- Return the encapsulation-key-sender state exactly when `t` is the successor epoch. -/
def recvNextEpoch (st : Ct2Sent AuthState) (t : ℕ) : Option (EkSender.KeysUnsampled AuthState) :=
  if t = st.ep + 1 then some ⟨st.ep + 1, st.authSt⟩ else none
```

{usesLabel}`uses` {uses "incremental_kem_scheme"}[] · {githubLabel}`github` {githubIssue 252}[]
::::

:::group "spqr_chunked"
Chunked SPQR.
:::

:::defTitle "spqr_chunked_spec" "SPQR chunked protocol"
:::

::::definition "spqr_chunked_spec" (parent := "spqr_chunked") (lean := "SPQR.Chunked.Payload, SPQR.Chunked.Message, SPQR.Chunked.Message.Deserializable, SPQR.Chunked.PartyState, SPQR.Chunked.Error, SPQR.Chunked.SendResult, SPQR.Chunked.RecvResult, SPQR.Chunked.initA, SPQR.Chunked.initB, SPQR.Chunked.send, SPQR.Chunked.completeCt2, SPQR.Chunked.recv")
$`\todo`

:::leanPillCaption "wire payload"
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

:::leanPillCaption "wire message"
:::

```anchor Chunked_Message (project := ".") (module := SecureMessaging.SCKA.SPQR.Chunked)
structure Message (Sym : Type) where
  /-- The epoch being negotiated. -/
  epoch : ℕ
  /-- The typed payload. -/
  payload : Payload Sym
```

:::leanPillCaption "deserializable message"
:::

```anchor Chunked_Message_Deserializable (project := ".") (module := SecureMessaging.SCKA.SPQR.Chunked)
def Message.Deserializable {Sym : Type} (msg : Message Sym) : Prop :=
  0 < msg.epoch ∧ msg.epoch < 2 ^ 64 ∧
    match msg.payload with
    | .hdr chunk | .ek chunk | .ekCt1Ack chunk | .ct1 chunk | .ct2 chunk => chunk.1 < 2 ^ 16
    | .none | .ct1Ack => True
```

:::leanPillCaption "party state"
:::

```anchor Chunked_PartyState (project := ".") (module := SecureMessaging.SCKA.SPQR.Chunked)
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
```

:::leanPillCaption "receive errors"
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

:::leanPillCaption "send result"
:::

```anchor Chunked_SendResult (project := ".") (module := SecureMessaging.SCKA.SPQR.Chunked)
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
```

:::leanPillCaption "receive result"
:::

```anchor Chunked_RecvResult (project := ".") (module := SecureMessaging.SCKA.SPQR.Chunked)
structure RecvResult (P : MLKEMBraid.Parameters m) (AuthState : Type) where
  /-- The incoming message epoch minus one. -/
  receivingEpoch : ℕ
  /-- The epoch key derived by this receive, if any. -/
  outputKey : Option (ℕ × P.EpochKey)
  /-- The state after the receive. -/
  state : PartyState P AuthState
```

:::leanPillCaption "initial encapsulation-key sender"
:::

```anchor Chunked_initA (project := ".") (module := SecureMessaging.SCKA.SPQR.Chunked)
def initA (P : MLKEMBraid.Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (ik : InitKey) : PartyState P AuthState
```

:::leanPillCaption "initial ciphertext sender"
:::

```anchor Chunked_initB (project := ".") (module := SecureMessaging.SCKA.SPQR.Chunked)
def initB (P : MLKEMBraid.Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (ik : InitKey) : PartyState P AuthState
```

:::leanPillCaption "send transition"
:::

```anchor Chunked_send (project := ".") (module := SecureMessaging.SCKA.SPQR.Chunked)
def send (P : MLKEMBraid.Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : PartyState P AuthState) : m (SendResult P AuthState)
```

:::leanPillCaption "complete incremental encapsulation stage two"
:::

```anchor Chunked_completeCt2 (project := ".") (module := SecureMessaging.SCKA.SPQR.Chunked)
def completeCt2 (P : MLKEMBraid.Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (core : CtSender.Ct1SentEkReceived P.inc AuthState) : PartyState P AuthState :=
  let c2 := P.hEnc2.encaps2Det core.encapsSt core.hdr core.vec
  let tag := auth.macCiphertext core.authSt core.ep (core.c1, c2)
  .ct2Sampled ⟨core.ep, core.authSt⟩ (EncoderState.init P.ecpCt2 (c2, tag))
```

:::leanPillCaption "receive transition"
:::

```anchor Chunked_recv (project := ".") (module := SecureMessaging.SCKA.SPQR.Chunked)
def recv (P : MLKEMBraid.Parameters m) [DecidableEq P.Sym]
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : PartyState P AuthState) (msg : Message P.Sym) :
    Except Error (RecvResult P AuthState)
```

{usesLabel}`uses` {uses "scka_scheme"}[] · {uses "spqr_unchunked_ek_sender"}[] · {uses "spqr_unchunked_ct_sender"}[] · {uses "erasure_code_payload"}[] · {uses "erasure_code_streaming"}[] · {uses "mlkem_braid_protocol_parameters"}[] · {githubLabel}`github` {githubIssue 263}[]
::::

:::defTitle "spqr_chunked_scheme" "SPQR chunked protocol as an SCKA scheme"
:::

::::definition "spqr_chunked_scheme" (parent := "spqr_chunked") (lean := "SPQR.scheme")

:::leanPillCaption "send with disclosed randomness"
:::

```anchor SPQR_sendRleak (project := ".") (module := SecureMessaging.SCKA.SPQR.Construction)
def sendRleak (P : MLKEMBraid.Parameters m) (irl : P.kem.IncrementalRandLeak P.inc)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : PartyState P AuthState) :
    m (SendResult P AuthState × SendRand irl.KeygenRand irl.Encaps1Rand)
```

:::leanPillCaption "receive adapted to SCKA: an error refuses the delivery"
:::

```anchor SPQR_recvSCKA (project := ".") (module := SecureMessaging.SCKA.SPQR.Construction)
def recvSCKA (P : MLKEMBraid.Parameters m) [DecidableEq P.Sym]
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : PartyState P AuthState) (msg : Message P.Sym) :
    Option (Option (ℕ × P.EpochKey) × ℕ × PartyState P AuthState)
```

:::leanPillCaption "the SCKA scheme"
:::

```anchor SPQR_scheme (project := ".") (module := SecureMessaging.SCKA.SPQR.Construction)
def scheme (P : MLKEMBraid.Parameters m) [DecidableEq P.Sym]
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc) (sampleInitKey : m InitKey) :
    SCKAScheme m InitKey (PartyState P AuthState) (PartyState P AuthState)
      P.EpochKey (Message P.Sym) (SendRand irl.KeygenRand irl.Encaps1Rand) :=
  let sendSCKA (st : PartyState P AuthState) := do
    let r ← send P auth st
    pure (some (r.outputKey, r.msg, r.sendingEpoch, r.state))
  let sendRleakSCKA (st : PartyState P AuthState) := do
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

{usesLabel}`uses` {uses "scka_scheme"}[] · {uses "spqr_chunked_spec"}[] · {uses "incremental_kem_rand_leak"}[] · {githubLabel}`github` {githubIssue 263}[]
::::

:::defTitle "spqr_chunked_to_mlkem_braid" "Translation of the SPQR chunked protocol into ML-KEM Braid"
:::

::::definition "spqr_chunked_to_mlkem_braid" (parent := "spqr_chunked") (lean := "SPQR.Chunked.Message.toMLKEMBraid, SPQR.Chunked.PartyState.toMLKEMBraid, SPQR.Chunked.SendResult.toMLKEMBraid")

:::leanPillCaption "wire message"
:::

```anchor Correspondence_Message_toMLKEMBraid (project := ".") (module := SecureMessaging.SCKA.SPQR.Correspondence)
def Message.toMLKEMBraid {Sym : Type} (msg : Message Sym) : MLKEMBraid.Message Sym :=
  match msg.payload with
  | .none => ⟨msg.epoch, .none, none⟩
  | .hdr chunk => ⟨msg.epoch, .hdr, some chunk⟩
  | .ek chunk => ⟨msg.epoch, .ek, some chunk⟩
  | .ekCt1Ack chunk => ⟨msg.epoch, .ekCt1Ack, some chunk⟩
  | .ct1Ack => ⟨msg.epoch, .ct1Ack, none⟩
  | .ct1 chunk => ⟨msg.epoch, .ct1, some chunk⟩
  | .ct2 chunk => ⟨msg.epoch, .ct2, some chunk⟩
```

:::leanPillCaption "party state"
:::

```anchor Correspondence_PartyState_toMLKEMBraid (project := ".") (module := SecureMessaging.SCKA.SPQR.Correspondence)
def PartyState.toMLKEMBraid : PartyState P AuthState → MLKEMBraid.State P AuthState
  | .keysUnsampled core => .keysUnsampled core.ep core.authSt
  | .keysSampled core enc =>
      .keysSampled core.ep core.authSt core.sk (P.inc.toVector core.pk) enc
  | .headerSent core enc dec => .headerSent core.ep core.authSt core.sk dec enc
  | .ct1Received core enc => .ct1Received core.ep core.authSt core.sk core.c1 enc
  | .ekSentCt1Received core dec => .ekSentCt1Received core.ep core.authSt core.sk core.c1 dec
  | .noHeaderReceived core dec => .noHeaderReceived core.ep core.authSt dec
  | .headerReceived core dec => .headerReceived core.ep core.authSt core.hdr dec
  | .ct1Sampled core enc dec =>
      .ct1Sampled core.ep core.authSt core.hdr core.encapsSt core.c1 enc dec
  | .ekReceivedCt1Sampled core enc =>
      .ekReceivedCt1Sampled core.ep core.authSt core.encapsSt core.c1 core.hdr core.vec enc
  | .ct1Acknowledged core dec =>
      .ct1Acknowledged core.ep core.authSt core.hdr core.encapsSt core.c1 dec
  | .ct2Sampled core enc => .ct2Sampled core.ep core.authSt enc
```

:::leanPillCaption "send result"
:::

```anchor Correspondence_SendResult_toMLKEMBraid (project := ".") (module := SecureMessaging.SCKA.SPQR.Correspondence)
def SendResult.toMLKEMBraid (r : SendResult P AuthState) : MLKEMBraid.SendResult P AuthState :=
  ⟨r.msg.toMLKEMBraid, r.sendingEpoch, r.outputKey, r.state.toMLKEMBraid⟩
```

{usesLabel}`uses` {uses "spqr_chunked_spec"}[] · {uses "mlkem_braid_protocol_messages"}[] · {uses "mlkem_braid_protocol_states"}[] · {githubLabel}`github` {githubIssue 263}[]
::::

:::defTitle "spqr_chunked_correspondence" "Agreement of the SPQR chunked protocol with ML-KEM Braid"
:::

::::theorem "spqr_chunked_correspondence" (parent := "spqr_chunked") (lean := "SPQR.Chunked.toMLKEMBraid_initA, SPQR.Chunked.toMLKEMBraid_initB, SPQR.Chunked.send_toMLKEMBraid, SPQR.Chunked.send_ekSentCt1Received_toMLKEMBraid, SPQR.recvSCKA_toMLKEMBraid")

:::leanPillCaption "initialisation"
:::

```anchor Correspondence_toMLKEMBraid_initA (project := ".") (module := SecureMessaging.SCKA.SPQR.Correspondence)
theorem toMLKEMBraid_initA (P : MLKEMBraid.Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac) (ik : InitKey) :
    (initA P auth ik).toMLKEMBraid = MLKEMBraid.initA P auth ik
```

```anchor Correspondence_toMLKEMBraid_initB (project := ".") (module := SecureMessaging.SCKA.SPQR.Correspondence)
theorem toMLKEMBraid_initB (P : MLKEMBraid.Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac) (ik : InitKey) :
    (initB P auth ik).toMLKEMBraid = MLKEMBraid.initB P auth ik
```

:::leanPillCaption "send outside `ekSentCt1Received`"
:::

```anchor Correspondence_send_toMLKEMBraid (project := ".") (module := SecureMessaging.SCKA.SPQR.Correspondence)
theorem send_toMLKEMBraid [LawfulMonad m] (P : MLKEMBraid.Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : PartyState P AuthState) (h : ∀ core dec, st ≠ .ekSentCt1Received core dec) :
    SendResult.toMLKEMBraid <$> send P auth st = MLKEMBraid.send P auth st.toMLKEMBraid
```

:::leanPillCaption "send in `ekSentCt1Received`"
:::

```anchor Correspondence_send_ekSentCt1Received_toMLKEMBraid (project := ".") (module := SecureMessaging.SCKA.SPQR.Correspondence)
theorem send_ekSentCt1Received_toMLKEMBraid [LawfulMonad m]
    (P : MLKEMBraid.Parameters m)
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (core : EkSender.EkSentCt1Received P.inc AuthState)
    (dec : DecoderState (P.inc.C₂ × P.Mac) P.Sym) :
    SendResult.toMLKEMBraid <$> send P auth (.ekSentCt1Received core dec) =
      (fun r => { r with msg := ⟨r.msg.epoch, .ct1Ack, r.msg.data⟩ }) <$>
        MLKEMBraid.send P auth (PartyState.toMLKEMBraid (.ekSentCt1Received core dec))
```

:::leanPillCaption "receive at the SCKA level"
:::

```anchor Correspondence_recvSCKA_toMLKEMBraid (project := ".") (module := SecureMessaging.SCKA.SPQR.Correspondence)
theorem recvSCKA_toMLKEMBraid (P : MLKEMBraid.Parameters m) [DecidableEq P.Sym]
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : PartyState P AuthState) (msg : Message P.Sym)
    (h : MLKEMBraid.receive P auth st.toMLKEMBraid msg.toMLKEMBraid ≠
      .ok ⟨st.toMLKEMBraid.epoch - 1, none, st.toMLKEMBraid⟩) :
    (recvSCKA P auth st msg).map (fun r => (r.1, r.2.1, r.2.2.toMLKEMBraid)) =
      MLKEMBraid.recvSCKA P auth st.toMLKEMBraid msg.toMLKEMBraid
```

{usesLabel}`uses` {uses "spqr_chunked_to_mlkem_braid"}[] · {uses "spqr_chunked_scheme"}[] · {uses "mlkem_braid_protocol_transitions"}[] · {uses "mlkem_braid_protocol_init"}[] · {uses "mlkem_braid_spec"}[] · {githubLabel}`github` {githubIssue 263}[]
::::

:::defTitle "spqr_protocol_spec" "SPQR protocol"
:::

::::definition "spqr_protocol_spec" (parent := "cka_protocols_spqr") (lean := "SPQR.v1Incremental, SPQR.v1ErasureCodePayload, SPQR.v1Parameters, SPQR.v1Scheme")
$`\todo`

:::leanPillCaption "incremental ML-KEM-768"
:::

```anchor SPQR_v1Incremental (project := ".") (module := SecureMessaging.SCKA.SPQR.Instances)
abbrev v1Incremental : MLKEM.mlkem768Scheme.IncrementalStructure :=
  MLKEM.mlkemIncremental .MLKEM768 MLKEM.Concrete.concreteNTTRingOps
    MLKEM.Concrete.mlkem768Primitives
```

:::leanPillCaption "SPQR Reed-Solomon payload code"
:::

```anchor SPQR_v1ErasureCodePayload (project := ".") (module := SecureMessaging.SCKA.SPQR.Instances)
noncomputable def v1ErasureCodePayload {M : Type} (k : ℕ) (hk : k ≤ 2 ^ 16) (hk_pos : 0 < k)
    (serialize : M → Fin k → Chunk GF16) (parse : (Fin k → Chunk GF16) → Option M)
    (parse_serialize : ∀ payload, parse (serialize payload) = some payload) :
    ErasureCodePayload M (Chunk GF16) :=
  { ec := erasureCode k hk hk_pos, serialize, parse, parse_serialize }
```

:::leanPillCaption "SPQR v1 parameters"
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
    MLKEMBraid.Parameters ProbComp :=
  MLKEMBraid.mlkemBraidParameters .MLKEM768 MLKEM.Concrete.concreteNTTRingOps
    MLKEM.Concrete.mlkem768Primitives kdfOK
    (v1ErasureCodePayload 3 (by norm_num) (by norm_num) serializeHdr parseHdr
      parseHdr_serializeHdr)
    (v1ErasureCodePayload 36 (by norm_num) (by norm_num) serializeEk parseEk
      parseEk_serializeEk)
    (v1ErasureCodePayload 30 (by norm_num) (by norm_num) serializeCt1 parseCt1
      parseCt1_serializeCt1)
    (v1ErasureCodePayload 5 (by norm_num) (by norm_num) serializeCt2 parseCt2
      parseCt2_serializeCt2)
```

:::leanPillCaption "SPQR v1 SCKA scheme"
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
      (SendRand (MLKEM.mlkemIncrementalRandLeak .MLKEM768 MLKEM.Concrete.concreteNTTRingOps
          MLKEM.Concrete.mlkem768Primitives).KeygenRand
        (MLKEM.mlkemIncrementalRandLeak .MLKEM768 MLKEM.Concrete.concreteNTTRingOps
          MLKEM.Concrete.mlkem768Primitives).Encaps1Rand)
```

{usesLabel}`uses` {uses "scka_scheme"}[] · {uses "spqr_unchunked_ek_sender"}[] · {uses "spqr_unchunked_ct_sender"}[] · {uses "spqr_chunked_spec"}[] · {uses "erasure_code_scheme"}[] · {uses "spqr_chunked_scheme"}[] · {uses "spqr_reed_solomon_code"}[] · {uses "incremental_kem_rand_leak"}[] · {githubLabel}`github` {githubIssue 268}[]
::::

:::defTitle "spqr_protocol_correctness" "SPQR protocol correctness"
:::

::::theorem "spqr_protocol_correctness" (parent := "cka_protocols_spqr")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "spqr_protocol_spec"}[] · {uses "scka_correctness"}[] · {uses "erasure_code_correctness"}[] · {githubLabel}`github` {githubIssue 269}[]
::::

:::defTitle "spqr_protocol_security" "SPQR protocol security"
:::

::::theorem "spqr_protocol_security" (parent := "cka_protocols_spqr")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "spqr_protocol_spec"}[] · {uses "scka_security"}[] · {uses "erasure_code_scheme"}[] · {githubLabel}`github` {githubIssue 270}[]
::::
