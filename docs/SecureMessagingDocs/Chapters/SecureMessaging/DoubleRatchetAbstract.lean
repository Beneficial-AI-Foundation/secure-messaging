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

#doc (Manual) "Abstract Protocol (Double Ratchet)" =>

*References:*

- {Informal.citet ACD19}[]

:::group "secure_messaging_abstract_protocol_double_ratchet"
Abstract Protocol (Double Ratchet).
:::

:::defTitle "secure_messaging_abstract_double_ratchet_spec" "Abstract Double Ratchet protocol"
:::

::::definition "secure_messaging_abstract_double_ratchet_spec" (parent := "secure_messaging_abstract_protocol_double_ratchet")
$`\todo`

:::leanPill "missing" "Lean formalization pending"
:::

{usesLabel}`uses` {uses "fs_aead_scheme"}[] · {uses "prf_prng_scheme"}[] · {githubLabel}`github` {githubIssue 124}[]
::::

:::defTitle "secure_messaging_abstract_double_ratchet_correctness" "Abstract Double Ratchet correctness"
:::

::::theorem "secure_messaging_abstract_double_ratchet_correctness" (parent := "secure_messaging_abstract_protocol_double_ratchet")
$`\todo`

:::leanPill "missing" "Lean proof pending"
:::

{usesLabel}`uses` {uses "secure_messaging_abstract_double_ratchet_spec"}[] · {githubLabel}`github` {githubIssue 125}[]
::::

:::defTitle "secure_messaging_abstract_double_ratchet_authenticity" "Abstract Double Ratchet authenticity"
:::

::::theorem "secure_messaging_abstract_double_ratchet_authenticity" (parent := "secure_messaging_abstract_protocol_double_ratchet")
$`\todo`

:::leanPill "missing" "Lean proof pending"
:::

{usesLabel}`uses` {uses "secure_messaging_abstract_double_ratchet_spec"}[] · {githubLabel}`github` {githubIssue 126}[]
::::

:::defTitle "secure_messaging_abstract_double_ratchet_privacy" "Abstract Double Ratchet privacy"
:::

::::theorem "secure_messaging_abstract_double_ratchet_privacy" (parent := "secure_messaging_abstract_protocol_double_ratchet")
$`\todo`

:::leanPill "missing" "Lean proof pending"
:::

{usesLabel}`uses` {uses "secure_messaging_abstract_double_ratchet_spec"}[] · {githubLabel}`github` {githubIssue 127}[]
::::

:::defTitle "secure_messaging_abstract_double_ratchet_security" "Abstract Double Ratchet security"
:::

::::theorem "secure_messaging_abstract_double_ratchet_security" (parent := "secure_messaging_abstract_protocol_double_ratchet")
$`\todo`

:::leanPill "missing" "Lean proof pending"
:::

{usesLabel}`uses` {uses "secure_messaging_abstract_double_ratchet_spec"}[] · {githubLabel}`github` {githubIssue 128}[]
::::
