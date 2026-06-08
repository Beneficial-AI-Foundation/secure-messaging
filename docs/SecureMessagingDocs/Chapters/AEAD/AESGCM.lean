import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill

open Verso.Genre Manual
open Informal

set_option doc.verso true

#doc (Manual) "AES-GCM" =>

*References:*

- {Informal.citet NIST_GCM}[]

:::group "aead_aes_gcm"
AES-GCM.
:::

:::defTitle "aead_aes_gcm_spec" "AEAD-AES-GCM construction"
:::

::::definition "aead_aes_gcm_spec" (parent := "aead_aes_gcm")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "aead"}[] · {githubLabel}`github` {githubIssue 21}[]
::::

:::defTitle "aead_aes_gcm_correctness" "AEAD-AES-GCM correctness"
:::

::::theorem "aead_aes_gcm_correctness" (parent := "aead_aes_gcm")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "aead_aes_gcm_spec"}[] · {uses "aead_correct"}[] · {githubLabel}`github` {githubIssue 22}[]
::::

:::defTitle "aead_aes_gcm_security" "AEAD-AES-GCM security"
:::

::::theorem "aead_aes_gcm_security" (parent := "aead_aes_gcm")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "aead_aes_gcm_spec"}[] · {uses "aead_security_exp"}[] · {githubLabel}`github` {githubIssue 23}[]
::::
