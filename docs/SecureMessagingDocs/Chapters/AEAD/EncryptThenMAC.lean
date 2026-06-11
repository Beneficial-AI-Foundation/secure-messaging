import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill

open Verso.Genre Manual
open Informal

set_option doc.verso true

#doc (Manual) "Encrypt-then-MAC" =>

*References:*

- {Informal.citet BN00}[]
- {Informal.citet Rog02}[]

:::group "aead_encrypt_then_mac"
Encrypt-then-MAC.
:::

:::defTitle "aead_etm_spec" "AEAD encrypt-then-MAC construction"
:::

::::definition "aead_etm_spec" (parent := "aead_encrypt_then_mac")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "aead"}[] · {githubLabel}`github` {githubIssue 24}[]
::::

:::defTitle "aead_etm_correctness" "AEAD encrypt-then-MAC correctness"
:::

::::theorem "aead_etm_correctness" (parent := "aead_encrypt_then_mac")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "aead_etm_spec"}[] · {uses "aead_correct"}[] · {githubLabel}`github` {githubIssue 25}[]
::::

:::defTitle "aead_etm_security" "AEAD encrypt-then-MAC security"
:::

::::theorem "aead_etm_security" (parent := "aead_encrypt_then_mac")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "aead_etm_spec"}[] · {uses "aead_security_exp"}[] · {githubLabel}`github` {githubIssue 26}[]
::::
