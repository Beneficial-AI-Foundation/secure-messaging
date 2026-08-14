import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessaging.SCKA.MLKEMBraid.Authenticator
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

:::group "cka_protocols_mlkem_braid"
ML-KEM Braid.
:::

:::defTitle "mlkem_braid_ratcheted_authenticator" "Ratcheted authenticator"
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

:::group "mlkem_braid_unchunked_core"
Unchunked ML-KEM Braid core.
:::

:::defTitle "mlkem_braid_unchunked_derive_epoch_key" "Epoch-key derivation boundary"
:::

::::definition "mlkem_braid_unchunked_derive_epoch_key" (parent := "mlkem_braid_unchunked_core") (lean := "MLKEMBraid.EpochKeyDerivation")
$`\todo`

:::leanPillCaption "abstract epoch-key derivation"
:::

```anchor EpochKeyDerivation (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Unchunked)
abbrev EpochKeyDerivation (K EpochKey : Type) : Type := K → ℕ → EpochKey
```

{githubLabel}`github` {githubIssue 252}[]
::::

:::defTitle "mlkem_braid_unchunked_ek_sender" "Unchunked encapsulation-key sender"
:::

::::definition "mlkem_braid_unchunked_ek_sender" (parent := "mlkem_braid_unchunked_core") (lean := "MLKEMBraid.EkSender.KeysUnsampled, MLKEMBraid.EkSender.HeaderSent, MLKEMBraid.EkSender.EkSent, MLKEMBraid.EkSender.EkSentCt1Received, MLKEMBraid.EkSender.sendHeader, MLKEMBraid.EkSender.sendVector, MLKEMBraid.EkSender.recvCt1, MLKEMBraid.EkSender.recvCt2")
$`\todo`

:::leanPillCaption "send authenticated encapsulation-key header"
:::

```anchor EkSender_sendHeader (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Unchunked)
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

```anchor EkSender_sendVector (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Unchunked)
/-- Return the successor state and the vector component of the stored encapsulation key. -/
def sendVector (inc : kem.IncrementalStructure) (st : HeaderSent inc AuthState) :
    EkSent inc AuthState × inc.PKvector :=
  (⟨st.ep, st.authSt, st.sk⟩, inc.toVector st.pk)
```

:::leanPillCaption "receive first ciphertext component"
:::

```anchor EkSender_recvCt1 (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Unchunked)
/-- Store the first ciphertext component. -/
def recvCt1 (inc : kem.IncrementalStructure) (st : EkSent inc AuthState)
    (c1 : inc.C₁) : EkSentCt1Received inc AuthState :=
  ⟨st.ep, st.authSt, st.sk, c1⟩
```

:::leanPillCaption "receive second ciphertext component and tag"
:::

```anchor EkSender_recvCt2 (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Unchunked)
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

{usesLabel}`uses` {uses "incremental_kem_scheme"}[] · {uses "mlkem_braid_ratcheted_authenticator"}[] · {uses "mlkem_braid_unchunked_derive_epoch_key"}[] · {githubLabel}`github` {githubIssue 252}[]
::::

:::defTitle "mlkem_braid_unchunked_ct_sender" "Unchunked ciphertext sender"
:::

::::definition "mlkem_braid_unchunked_ct_sender" (parent := "mlkem_braid_unchunked_core") (lean := "MLKEMBraid.CtSender.NoHeaderReceived, MLKEMBraid.CtSender.HeaderReceived, MLKEMBraid.CtSender.Ct1Sent, MLKEMBraid.CtSender.Ct1SentEkReceived, MLKEMBraid.CtSender.Ct2Sent, MLKEMBraid.CtSender.recvHeader, MLKEMBraid.CtSender.sendCt1, MLKEMBraid.CtSender.recvVector, MLKEMBraid.CtSender.sendCt2, MLKEMBraid.CtSender.recvNextEpoch")
$`\todo`

:::leanPillCaption "receive authenticated encapsulation-key header"
:::

```anchor CtSender_recvHeader (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Unchunked)
/-- Verify the header tag and return the successor state on success. -/
def recvHeader (inc : kem.IncrementalStructure)
    (auth : RatchetedAuthenticator InitKey EpochKey AuthState inc.PKheader (inc.C₁ × inc.C₂) Mac)
    (st : NoHeaderReceived AuthState) (hdr : inc.PKheader) (tag : Mac) :
    Option (HeaderReceived inc AuthState) :=
  if auth.verifyHeader st.authSt st.ep hdr tag then some ⟨st.ep, st.authSt, hdr⟩ else none
```

:::leanPillCaption "send first ciphertext component"
:::

```anchor CtSender_sendCt1 (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Unchunked)
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

```anchor CtSender_recvVector (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Unchunked)
/-- Validate the encapsulation-key vector and return the successor state on success. -/
def recvVector (inc : kem.IncrementalStructure) (st : Ct1Sent inc AuthState)
    (vec : inc.PKvector) : Option (Ct1SentEkReceived inc AuthState) :=
  if inc.validPK st.hdr vec then
    some ⟨st.ep, st.authSt, st.hdr, st.encapsSt, st.c1, vec⟩
  else none
```

:::leanPillCaption "send second ciphertext component and tag"
:::

```anchor CtSender_sendCt2 (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Unchunked)
/-- Run encapsulation stage two and return the successor state, ciphertext, and tag. -/
def sendCt2 (inc : kem.IncrementalStructure)
    (auth : RatchetedAuthenticator InitKey EpochKey AuthState inc.PKheader (inc.C₁ × inc.C₂) Mac)
    (st : Ct1SentEkReceived inc AuthState) : m (Ct2Sent AuthState × inc.C₂ × Mac) := do
  let c2 ← inc.encaps2 st.encapsSt st.hdr st.vec
  pure (⟨st.ep, st.authSt⟩, c2, auth.macCiphertext st.authSt st.ep (st.c1, c2))
```

:::leanPillCaption "advance to the next epoch"
:::

```anchor CtSender_recvNextEpoch (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Unchunked)
/-- Return the encapsulation-key-sender state exactly when `t` is the successor epoch. -/
def recvNextEpoch (st : Ct2Sent AuthState) (t : ℕ) : Option (EkSender.KeysUnsampled AuthState) :=
  if t = st.ep + 1 then some ⟨st.ep + 1, st.authSt⟩ else none
```

{usesLabel}`uses` {uses "incremental_kem_scheme"}[] · {uses "mlkem_braid_ratcheted_authenticator"}[] · {uses "mlkem_braid_unchunked_derive_epoch_key"}[] · {githubLabel}`github` {githubIssue 252}[]
::::
