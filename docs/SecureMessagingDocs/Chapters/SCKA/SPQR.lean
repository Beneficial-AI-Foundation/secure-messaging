import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessaging.SCKA.SPQR.Unchunked

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

::::definition "spqr_chunked_spec" (parent := "spqr_chunked")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "scka_scheme"}[] · {uses "spqr_unchunked_ek_sender"}[] · {uses "spqr_unchunked_ct_sender"}[] · {uses "erasure_code_payload"}[] · {uses "erasure_code_streaming"}[] · {githubLabel}`github` {githubIssue 263}[]
::::

:::defTitle "spqr_protocol_spec" "SPQR protocol"
:::

::::definition "spqr_protocol_spec" (parent := "cka_protocols_spqr")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "scka_scheme"}[] · {uses "spqr_unchunked_ek_sender"}[] · {uses "spqr_unchunked_ct_sender"}[] · {uses "spqr_chunked_spec"}[] · {uses "erasure_code_scheme"}[] · {githubLabel}`github` {githubIssue 268}[]
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
