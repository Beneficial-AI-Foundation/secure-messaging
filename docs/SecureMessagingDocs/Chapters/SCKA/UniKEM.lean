import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "UniKEM-CKA" =>

:::group "cka_protocols_unikem_cka"
UniKEM-CKA.
:::

:::defTitle "unikem_cka_spec" "UniKEM-CKA protocol"
:::

::::definition "unikem_cka_spec" (parent := "cka_protocols_unikem_cka")
$`\todo`

:::leanPill "missing" "Lean formalization pending"
:::

{usesLabel}`uses` {uses "on_off_kem_scheme"}[] · {githubLabel}`github` {githubIssue 97}[]
::::

:::defTitle "unikem_cka_correctness" "UniKEM-CKA correctness"
:::

::::theorem "unikem_cka_correctness" (parent := "cka_protocols_unikem_cka")
$`\todo`

:::leanPill "missing" "Lean proof pending"
:::

{usesLabel}`uses` {uses "unikem_cka_spec"}[] · {githubLabel}`github` {githubIssue 98}[]
::::

:::defTitle "unikem_cka_security" "UniKEM-CKA security"
:::

::::theorem "unikem_cka_security" (parent := "cka_protocols_unikem_cka")
$`\todo`

:::leanPill "missing" "Lean proof pending"
:::

{usesLabel}`uses` {uses "unikem_cka_spec"}[] · {githubLabel}`github` {githubIssue 99}[]
::::
