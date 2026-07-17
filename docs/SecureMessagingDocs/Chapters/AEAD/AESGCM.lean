import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessaging.AEAD.AESGCM.Construction

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

#doc (Manual) "AES-GCM" =>

*References:*

- {Informal.citet NIST_GCM}[]

:::group "aead_aes_gcm"
AES-GCM.
:::

:::defTitle "aead_aes_gcm_spec" "AEAD-AES-GCM construction"
:::

::::definition "aead_aes_gcm_spec" (parent := "aead_aes_gcm") (lean := "aesGcmAEAD")
$`\todo`

```anchor aesGcmAEAD (project := ".") (module := SecureMessaging.AEAD.AESGCM.Construction)
def aesGcmAEAD (cipher : AES K) :
    AEADScheme ProbComp (Vector (BitVec 128) n) (List (BitVec 128))
      (K × BitVec 96) (Vector (BitVec 128) n × BitVec 128) where
  keygen := do
    let k ← cipher.keygen
    let nonce ← $ᵗ (BitVec 96)
    return (k, nonce)
  encrypt := fun (k, nonce) ad m => gcmEncrypt (cipher.perm k) nonce ad m
  decrypt := fun (k, nonce) ad c => gcmDecrypt (cipher.perm k) nonce ad c
```

{usesLabel}`uses` {uses "aead"}[] · {githubLabel}`github` {githubIssue 21}[]
::::

:::defTitle "aead_aes_gcm_correctness" "AEAD-AES-GCM correctness"
:::

::::theorem "aead_aes_gcm_correctness" (parent := "aead_aes_gcm")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "aead_aes_gcm_spec"}[] · {uses "aead_correctness"}[] · {githubLabel}`github` {githubIssue 22}[]
::::

:::defTitle "aead_aes_gcm_security" "AEAD-AES-GCM security"
:::

::::theorem "aead_aes_gcm_security" (parent := "aead_aes_gcm")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "aead_aes_gcm_spec"}[] · {uses "aead_security_exp"}[] · {githubLabel}`github` {githubIssue 23}[]
::::
