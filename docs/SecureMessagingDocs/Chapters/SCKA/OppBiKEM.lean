import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Opp-BiKEM-CKA" =>

:::group "cka_protocols_opp_bikem_cka"
Opp-BiKEM-CKA.
:::

:::defTitle "opp_bikem_cka_spec" "Opp-BiKEM-CKA protocol"
:::

::::definition "opp_bikem_cka_spec" (parent := "cka_protocols_opp_bikem_cka") (tags := "gh-109") (uses := "scka_scheme, erasure_code_scheme")
$`\todo`

:::leanPill "missing"
:::
::::

:::defTitle "opp_bikem_cka_correctness" "Opp-BiKEM-CKA correctness"
:::

::::theorem "opp_bikem_cka_correctness" (parent := "cka_protocols_opp_bikem_cka") (tags := "gh-110") (uses := "opp_bikem_cka_spec, scka_correctness, erasure_code_correctness")
$`\todo`

:::leanPill "missing"
:::
::::

:::defTitle "opp_bikem_cka_security" "Opp-BiKEM-CKA security"
:::

::::theorem "opp_bikem_cka_security" (parent := "cka_protocols_opp_bikem_cka") (tags := "gh-111") (uses := "opp_bikem_cka_spec, scka_security, erasure_code_scheme")
$`\todo`

:::leanPill "missing"
:::
::::
