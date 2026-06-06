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

:::leanPill "missing" "Lean formalization pending"
:::

{usesLabel}`uses` {uses "on_off_kem_scheme"}[] · {githubLabel}`github` {githubIssue 103}[]
::::

:::defTitle "rkem_cka_correctness" "RKEM-CKA correctness"
:::

::::theorem "rkem_cka_correctness" (parent := "cka_protocols_rkem_cka")
$`\todo`

:::leanPill "missing" "Lean proof pending"
:::

{usesLabel}`uses` {uses "rkem_cka_spec"}[] · {githubLabel}`github` {githubIssue 104}[]
::::

:::defTitle "rkem_cka_security" "RKEM-CKA security"
:::

::::theorem "rkem_cka_security" (parent := "cka_protocols_rkem_cka")
$`\todo`

:::leanPill "missing" "Lean proof pending"
:::

{usesLabel}`uses` {uses "rkem_cka_spec"}[] · {githubLabel}`github` {githubIssue 105}[]
::::
