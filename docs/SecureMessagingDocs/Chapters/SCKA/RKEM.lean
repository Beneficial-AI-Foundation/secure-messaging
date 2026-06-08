import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "RKEM-CKA" =>

:::group "cka_protocols_rkem_cka"
RKEM-CKA.
:::

:::defTitle "rkem_cka_spec" "RKEM-CKA protocol"
:::

::::definition "rkem_cka_spec" (parent := "cka_protocols_rkem_cka")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "scka_scheme"}[] · {uses "erasure_code_scheme"}[] · {uses "rkem_scheme"}[] · {githubLabel}`github` {githubIssue 103}[]
::::

:::defTitle "rkem_cka_correctness" "RKEM-CKA correctness"
:::

::::theorem "rkem_cka_correctness" (parent := "cka_protocols_rkem_cka")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "rkem_cka_spec"}[] · {uses "scka_correctness"}[] · {uses "erasure_code_correctness"}[] · {uses "rkem_correctness"}[] · {githubLabel}`github` {githubIssue 104}[]
::::

:::defTitle "rkem_cka_security" "RKEM-CKA security"
:::

::::theorem "rkem_cka_security" (parent := "cka_protocols_rkem_cka")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "rkem_cka_spec"}[] · {uses "scka_security"}[] · {uses "erasure_code_scheme"}[] · {uses "rkem_forward_security"}[] · {uses "rkem_ratchet_sim"}[] · {githubLabel}`github` {githubIssue 105}[]
::::
