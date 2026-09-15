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

#doc (Manual) "SCKA SM" =>

*References:*

- {Informal.citet SCKA25}[]

:::group "secure_messaging_scka"
SCKA SM.
:::

:::defTitle "secure_messaging_scka_scheme" "Secure messaging scheme (SCKA)"
:::

::::definition "secure_messaging_scka_scheme" (parent := "secure_messaging_scka") (tags := "gh-166")
$`\todo`

:::leanPill "missing"
:::

::::

:::defTitle "secure_messaging_scka_spec" "Secure messaging protocol (SCKA)"
:::

::::definition "secure_messaging_scka_spec" (parent := "secure_messaging_scka") (tags := "gh-144")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "secure_messaging_scka_scheme"}[] · {uses "scka_scheme"}[] · {uses "fs_aead_scheme"}[] · {uses "prf_prng_scheme"}[]
::::

:::defTitle "secure_messaging_scka_correctness" "SCKA secure messaging correctness"
:::

::::theorem "secure_messaging_scka_correctness" (parent := "secure_messaging_scka") (tags := "gh-145")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "secure_messaging_scka_spec"}[]
::::

:::defTitle "secure_messaging_scka_authenticity" "SCKA secure messaging authenticity"
:::

::::theorem "secure_messaging_scka_authenticity" (parent := "secure_messaging_scka") (tags := "gh-146")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "secure_messaging_scka_spec"}[]
::::

:::defTitle "secure_messaging_scka_privacy" "SCKA secure messaging privacy"
:::

::::theorem "secure_messaging_scka_privacy" (parent := "secure_messaging_scka") (tags := "gh-147")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "secure_messaging_scka_spec"}[]
::::

:::defTitle "secure_messaging_scka_security" "SCKA secure messaging security"
:::

::::theorem "secure_messaging_scka_security" (parent := "secure_messaging_scka") (tags := "gh-148")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "secure_messaging_scka_spec"}[] · {uses "secure_messaging_scka_correctness"}[] · {uses "secure_messaging_scka_authenticity"}[] · {uses "secure_messaging_scka_privacy"}[]
::::
