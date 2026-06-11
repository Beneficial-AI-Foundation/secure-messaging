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

::::definition "opp_rkem_cka_spec" (parent := "cka_protocols_opp_rkem_cka")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "scka_scheme"}[] · {uses "erasure_code_scheme"}[] · {uses "rkem_scheme"}[] · {githubLabel}`github` {githubIssue 112}[]
::::

:::defTitle "opp_rkem_cka_correctness" "Opp-RKEM-CKA correctness"
:::

::::theorem "opp_rkem_cka_correctness" (parent := "cka_protocols_opp_rkem_cka")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "opp_rkem_cka_spec"}[] · {uses "scka_correctness"}[] · {uses "erasure_code_correctness"}[] · {uses "rkem_correctness"}[] · {githubLabel}`github` {githubIssue 113}[]
::::

:::defTitle "opp_rkem_cka_security" "Opp-RKEM-CKA security"
:::

::::theorem "opp_rkem_cka_security" (parent := "cka_protocols_opp_rkem_cka")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "opp_rkem_cka_spec"}[] · {uses "scka_security"}[] · {uses "erasure_code_scheme"}[] · {uses "rkem_forward_security"}[] · {uses "rkem_ratchet_sim"}[] · {githubLabel}`github` {githubIssue 114}[]
::::
