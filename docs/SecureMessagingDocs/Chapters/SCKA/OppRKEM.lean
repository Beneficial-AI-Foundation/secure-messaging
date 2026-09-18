import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Opp-RKEM-CKA" =>

:::group "cka_protocols_opp_rkem_cka"
Opp-RKEM-CKA.
:::

:::defTitle "opp_rkem_cka_spec" "Opp-RKEM-CKA protocol"
:::

::::definition "opp_rkem_cka_spec" (parent := "cka_protocols_opp_rkem_cka") (tags := "gh-112") (uses := "scka_scheme, erasure_code_scheme, rkem_scheme")
$`\todo`

:::leanPill "missing"
:::
::::

:::defTitle "opp_rkem_cka_correctness" "Opp-RKEM-CKA correctness"
:::

::::theorem "opp_rkem_cka_correctness" (parent := "cka_protocols_opp_rkem_cka") (tags := "gh-113") (uses := "opp_rkem_cka_spec, scka_correctness, erasure_code_correctness, rkem_correctness")
$`\todo`

:::leanPill "missing"
:::
::::

:::defTitle "opp_rkem_cka_security" "Opp-RKEM-CKA security"
:::

::::theorem "opp_rkem_cka_security" (parent := "cka_protocols_opp_rkem_cka") (tags := "gh-114") (uses := "opp_rkem_cka_spec, scka_security, erasure_code_scheme, rkem_forward_security, rkem_ratchet_sim")
$`\todo`

:::leanPill "missing"
:::
::::
