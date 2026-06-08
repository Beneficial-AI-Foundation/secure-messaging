import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "BiKEM-CKA" =>

:::group "cka_protocols_bikem_cka"
BiKEM-CKA.
:::

:::defTitle "bikem_cka_spec" "BiKEM-CKA protocol"
:::

::::definition "bikem_cka_spec" (parent := "cka_protocols_bikem_cka")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "scka_scheme"}[] · {uses "erasure_code_scheme"}[] · {githubLabel}`github` {githubIssue 100}[]
::::

:::defTitle "bikem_cka_correctness" "BiKEM-CKA correctness"
:::

::::theorem "bikem_cka_correctness" (parent := "cka_protocols_bikem_cka")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "bikem_cka_spec"}[] · {uses "scka_correctness"}[] · {uses "erasure_code_correctness"}[] · {githubLabel}`github` {githubIssue 101}[]
::::

:::defTitle "bikem_cka_security" "BiKEM-CKA security"
:::

::::theorem "bikem_cka_security" (parent := "cka_protocols_bikem_cka")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "bikem_cka_spec"}[] · {uses "scka_security"}[] · {uses "erasure_code_scheme"}[] · {githubLabel}`github` {githubIssue 102}[]
::::
