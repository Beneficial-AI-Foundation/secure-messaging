import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Double Ratchet SM - Signal" =>

:::group "secure_messaging_signal_protocol_double_ratchet"
Double Ratchet SM - Signal.
:::

:::defTitle "secure_messaging_signal_double_ratchet_spec" "Signal Double Ratchet protocol"
:::

::::definition "secure_messaging_signal_double_ratchet_spec" (parent := "secure_messaging_signal_protocol_double_ratchet") (tags := "gh-129")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "secure_messaging_abstract_double_ratchet_spec"}[] · {uses "cka"}[] · {uses "fs_aead_scheme"}[] · {uses "prf_prng_scheme"}[]
::::

:::defTitle "secure_messaging_signal_double_ratchet_correctness" "Signal Double Ratchet correctness"
:::

::::theorem "secure_messaging_signal_double_ratchet_correctness" (parent := "secure_messaging_signal_protocol_double_ratchet") (tags := "gh-130")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "secure_messaging_signal_double_ratchet_spec"}[] · {uses "secure_messaging_abstract_double_ratchet_correctness"}[]
::::

:::defTitle "secure_messaging_signal_double_ratchet_authenticity" "Signal Double Ratchet authenticity"
:::

::::theorem "secure_messaging_signal_double_ratchet_authenticity" (parent := "secure_messaging_signal_protocol_double_ratchet") (tags := "gh-131")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "secure_messaging_signal_double_ratchet_spec"}[] · {uses "secure_messaging_abstract_double_ratchet_authenticity"}[]
::::

:::defTitle "secure_messaging_signal_double_ratchet_privacy" "Signal Double Ratchet privacy"
:::

::::theorem "secure_messaging_signal_double_ratchet_privacy" (parent := "secure_messaging_signal_protocol_double_ratchet") (tags := "gh-132")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "secure_messaging_signal_double_ratchet_spec"}[] · {uses "secure_messaging_abstract_double_ratchet_privacy"}[]
::::

:::defTitle "secure_messaging_signal_double_ratchet_security" "Signal Double Ratchet security"
:::

::::theorem "secure_messaging_signal_double_ratchet_security" (parent := "secure_messaging_signal_protocol_double_ratchet") (tags := "gh-133")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "secure_messaging_signal_double_ratchet_spec"}[] · {uses "secure_messaging_signal_double_ratchet_correctness"}[] · {uses "secure_messaging_signal_double_ratchet_authenticity"}[] · {uses "secure_messaging_signal_double_ratchet_privacy"}[]
::::
