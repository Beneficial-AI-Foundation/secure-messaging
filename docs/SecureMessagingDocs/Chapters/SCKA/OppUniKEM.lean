import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Opp-UniKEM-CKA" =>

:::group "cka_protocols_opp_unikem_cka"
Opp-UniKEM-CKA.
:::

:::defTitle "opp_unikem_cka_spec" "Opp-UniKEM-CKA protocol"
:::

::::definition "opp_unikem_cka_spec" (parent := "cka_protocols_opp_unikem_cka")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "scka_scheme"}[] · {uses "erasure_code_scheme"}[] · {uses "on_off_kem_scheme"}[] · {githubLabel}`github` {githubIssue 106}[]
::::

:::defTitle "opp_unikem_cka_correctness" "Opp-UniKEM-CKA correctness"
:::

::::theorem "opp_unikem_cka_correctness" (parent := "cka_protocols_opp_unikem_cka")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "opp_unikem_cka_spec"}[] · {uses "scka_correctness"}[] · {uses "erasure_code_correctness"}[] · {uses "on_off_kem_correctness"}[] · {githubLabel}`github` {githubIssue 107}[]
::::

:::defTitle "opp_unikem_cka_security" "Opp-UniKEM-CKA security"
:::

::::theorem "opp_unikem_cka_security" (parent := "cka_protocols_opp_unikem_cka")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "opp_unikem_cka_spec"}[] · {uses "scka_security"}[] · {uses "erasure_code_scheme"}[] · {uses "on_off_kem_security"}[] · {githubLabel}`github` {githubIssue 108}[]
::::
