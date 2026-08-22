import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessaging.SCKA.MLKEMBraid.Authenticator
import SecureMessagingDocs.Bibliography

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
