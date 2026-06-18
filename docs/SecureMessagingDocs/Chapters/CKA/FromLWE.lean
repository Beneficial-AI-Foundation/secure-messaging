import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill

open Verso.Genre Manual
open Informal

set_option doc.verso true

#doc (Manual) "CKA from LWE" =>

*References:*

- {Informal.citet ACD19}[]

:::group "cka_cka_from_lwe"
CKA from LWE.
:::

:::defTitle "cka_from_lwe_spec" "CKA from LWE construction"
:::

::::definition "cka_from_lwe_spec" (parent := "cka_cka_from_lwe")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "cka"}[] · {githubLabel}`github` {githubIssue 12}[]
::::

:::defTitle "cka_from_lwe_correctness" "CKA from LWE correctness"
:::

::::theorem "cka_from_lwe_correctness" (parent := "cka_cka_from_lwe")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "cka_from_lwe_spec"}[] · {uses "cka_correctness"}[] · {githubLabel}`github` {githubIssue 13}[]
::::

:::defTitle "cka_from_lwe_security" "CKA from LWE security"
:::

::::theorem "cka_from_lwe_security" (parent := "cka_cka_from_lwe")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "cka_from_lwe_spec"}[] · {uses "cka_security"}[] · {githubLabel}`github` {githubIssue 14}[]
::::
