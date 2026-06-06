import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill

open Verso.Genre Manual
open Informal

set_option doc.verso true

#doc (Manual) "CKA from KEM" =>

*References:*

- {Informal.citet ACD19}[]

:::group "cka_cka_from_kem"
CKA from KEM.
:::

:::defTitle "cka_from_kem_spec" "CKA from KEM construction"
:::

::::definition "cka_from_kem_spec" (parent := "cka_cka_from_kem")
$`\todo`

:::leanPill "missing" "Lean formalization pending"
:::

{githubLabel}`github` {githubIssue 3}[]
::::

:::defTitle "cka_from_kem_correctness" "CKA from KEM correctness"
:::

::::theorem "cka_from_kem_correctness" (parent := "cka_cka_from_kem")
$`\todo`

:::leanPill "missing" "Lean proof pending"
:::

{usesLabel}`uses` {uses "cka_from_kem_spec"}[] · {githubLabel}`github` {githubIssue 4}[]
::::

:::defTitle "cka_from_kem_security" "CKA from KEM security"
:::

::::theorem "cka_from_kem_security" (parent := "cka_cka_from_kem")
$`\todo`

:::leanPill "missing" "Lean proof pending"
:::

{usesLabel}`uses` {uses "cka_from_kem_spec"}[] · {githubLabel}`github` {githubIssue 5}[]
::::