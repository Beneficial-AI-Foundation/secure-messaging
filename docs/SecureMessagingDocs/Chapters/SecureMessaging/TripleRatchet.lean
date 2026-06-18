import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Triple Ratchet SM" =>

*References:*

- {Informal.citet TR25}[]

:::group "secure_messaging_triple_ratchet"
Triple Ratchet SM.
:::

:::defTitle "secure_messaging_triple_ratchet_scheme" "Secure messaging scheme (Triple Ratchet)"
:::

::::definition "secure_messaging_triple_ratchet_scheme" (parent := "secure_messaging_triple_ratchet")
$`\todo`

:::leanPill "missing"
:::

{githubLabel}`github` {githubIssue 171}[]
::::

:::defTitle "secure_messaging_triple_ratchet_spec" "Triple Ratchet protocol"
:::

::::definition "secure_messaging_triple_ratchet_spec" (parent := "secure_messaging_triple_ratchet")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "secure_messaging_triple_ratchet_scheme"}[] · {uses "erasure_code_scheme"}[] · {uses "rkem_scheme"}[] · {uses "fs_aead_scheme"}[] · {uses "prf_prng_scheme"}[] · {githubLabel}`github` {githubIssue 136}[]
::::

:::defTitle "secure_messaging_triple_ratchet_correctness" "Triple Ratchet correctness"
:::

::::theorem "secure_messaging_triple_ratchet_correctness" (parent := "secure_messaging_triple_ratchet")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "secure_messaging_triple_ratchet_spec"}[] · {githubLabel}`github` {githubIssue 137}[]
::::

:::defTitle "secure_messaging_triple_ratchet_authenticity" "Triple Ratchet authenticity"
:::

::::theorem "secure_messaging_triple_ratchet_authenticity" (parent := "secure_messaging_triple_ratchet")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "secure_messaging_triple_ratchet_spec"}[] · {githubLabel}`github` {githubIssue 138}[]
::::

:::defTitle "secure_messaging_triple_ratchet_privacy" "Triple Ratchet privacy"
:::

::::theorem "secure_messaging_triple_ratchet_privacy" (parent := "secure_messaging_triple_ratchet")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "secure_messaging_triple_ratchet_spec"}[] · {githubLabel}`github` {githubIssue 139}[]
::::

:::defTitle "secure_messaging_triple_ratchet_security" "Triple Ratchet security"
:::

::::theorem "secure_messaging_triple_ratchet_security" (parent := "secure_messaging_triple_ratchet")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "secure_messaging_triple_ratchet_spec"}[] · {uses "secure_messaging_triple_ratchet_correctness"}[] · {uses "secure_messaging_triple_ratchet_authenticity"}[] · {uses "secure_messaging_triple_ratchet_privacy"}[] · {githubLabel}`github` {githubIssue 140}[]
::::
