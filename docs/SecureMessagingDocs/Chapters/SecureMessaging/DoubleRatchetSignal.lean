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

::::definition "secure_messaging_signal_double_ratchet_spec" (parent := "secure_messaging_signal_protocol_double_ratchet") (tags := "gh-129") (uses := "secure_messaging_abstract_double_ratchet_spec, cka, fs_aead_scheme, prf_prng_scheme")
$`\todo`

:::leanPill "missing"
:::
::::

:::defTitle "secure_messaging_signal_double_ratchet_correctness" "Signal Double Ratchet correctness"
:::

::::theorem "secure_messaging_signal_double_ratchet_correctness" (parent := "secure_messaging_signal_protocol_double_ratchet") (tags := "gh-130") (uses := "secure_messaging_signal_double_ratchet_spec, secure_messaging_abstract_double_ratchet_correctness")
$`\todo`

:::leanPill "missing"
:::
::::

:::defTitle "secure_messaging_signal_double_ratchet_authenticity" "Signal Double Ratchet authenticity"
:::

::::theorem "secure_messaging_signal_double_ratchet_authenticity" (parent := "secure_messaging_signal_protocol_double_ratchet") (tags := "gh-131") (uses := "secure_messaging_signal_double_ratchet_spec, secure_messaging_abstract_double_ratchet_authenticity")
$`\todo`

:::leanPill "missing"
:::
::::

:::defTitle "secure_messaging_signal_double_ratchet_privacy" "Signal Double Ratchet privacy"
:::

::::theorem "secure_messaging_signal_double_ratchet_privacy" (parent := "secure_messaging_signal_protocol_double_ratchet") (tags := "gh-132") (uses := "secure_messaging_signal_double_ratchet_spec, secure_messaging_abstract_double_ratchet_privacy")
$`\todo`

:::leanPill "missing"
:::
::::

:::defTitle "secure_messaging_signal_double_ratchet_security" "Signal Double Ratchet security"
:::

::::theorem "secure_messaging_signal_double_ratchet_security" (parent := "secure_messaging_signal_protocol_double_ratchet") (tags := "gh-133") (uses := "secure_messaging_signal_double_ratchet_spec, secure_messaging_signal_double_ratchet_correctness, secure_messaging_signal_double_ratchet_authenticity, secure_messaging_signal_double_ratchet_privacy")
$`\todo`

:::leanPill "missing"
:::
::::
