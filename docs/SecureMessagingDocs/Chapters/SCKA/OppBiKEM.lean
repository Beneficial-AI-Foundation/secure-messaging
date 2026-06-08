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

::::definition "opp_bikem_cka_spec" (parent := "cka_protocols_opp_bikem_cka")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "scka_scheme"}[] · {uses "erasure_code_scheme"}[] · {githubLabel}`github` {githubIssue 109}[]
::::

:::defTitle "opp_bikem_cka_correctness" "Opp-BiKEM-CKA correctness"
:::

::::theorem "opp_bikem_cka_correctness" (parent := "cka_protocols_opp_bikem_cka")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "opp_bikem_cka_spec"}[] · {uses "scka_correctness"}[] · {uses "erasure_code_correctness"}[] · {githubLabel}`github` {githubIssue 110}[]
::::

:::defTitle "opp_bikem_cka_security" "Opp-BiKEM-CKA security"
:::

::::theorem "opp_bikem_cka_security" (parent := "cka_protocols_opp_bikem_cka")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "opp_bikem_cka_spec"}[] · {uses "scka_security"}[] · {uses "erasure_code_scheme"}[] · {githubLabel}`github` {githubIssue 111}[]
::::
