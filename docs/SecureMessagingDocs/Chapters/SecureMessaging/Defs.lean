import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Chapters.SecureMessaging.DoubleRatchetAbstract
import SecureMessagingDocs.Chapters.SecureMessaging.DoubleRatchetSignal

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Double Ratchet SM" =>

*References:*

- {Informal.citet ACD19}[]
- {Informal.citet TR25}[]
- {Informal.citet SCKA25}[]

:::group "secure_messaging"
Secure Messaging protocols.
:::

:::group "secure_messaging_double_ratchet"
Double Ratchet.
:::

:::defTitle "secure_messaging_double_ratchet_scheme" "Secure messaging scheme (Double Ratchet)"
:::

::::definition "secure_messaging_double_ratchet_scheme" (parent := "secure_messaging_double_ratchet")
$`\todo`

:::leanPill "missing"
:::

{githubLabel}`github` {githubIssue 161}[]
::::

:::defTitle "secure_messaging_double_ratchet_correctness" "Double Ratchet correctness"
:::

::::definition "secure_messaging_double_ratchet_correctness" (parent := "secure_messaging_double_ratchet")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "secure_messaging_double_ratchet_scheme"}[] · {githubLabel}`github` {githubIssue 162}[]
::::

:::defTitle "secure_messaging_double_ratchet_authenticity" "Double Ratchet authenticity"
:::

::::definition "secure_messaging_double_ratchet_authenticity" (parent := "secure_messaging_double_ratchet")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "secure_messaging_double_ratchet_scheme"}[] · {githubLabel}`github` {githubIssue 163}[]
::::

:::defTitle "secure_messaging_double_ratchet_privacy" "Double Ratchet privacy"
:::

::::definition "secure_messaging_double_ratchet_privacy" (parent := "secure_messaging_double_ratchet")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "secure_messaging_double_ratchet_scheme"}[] · {githubLabel}`github` {githubIssue 164}[]
::::

:::defTitle "secure_messaging_double_ratchet_security" "Double Ratchet security"
:::

::::definition "secure_messaging_double_ratchet_security" (parent := "secure_messaging_double_ratchet")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "secure_messaging_double_ratchet_scheme"}[] · {uses "secure_messaging_double_ratchet_correctness"}[] · {uses "secure_messaging_double_ratchet_authenticity"}[] · {uses "secure_messaging_double_ratchet_privacy"}[] · {githubLabel}`github` {githubIssue 165}[]
::::

{include 1 SecureMessagingDocs.Chapters.SecureMessaging.DoubleRatchetAbstract}

{include 1 SecureMessagingDocs.Chapters.SecureMessaging.DoubleRatchetSignal}
