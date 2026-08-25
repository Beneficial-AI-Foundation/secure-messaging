import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill

open Verso.Genre Manual
open Informal

set_option doc.verso true

#doc (Manual) "FrodoKEM" =>

*References:*

- {Informal.citet FrodoKEM}[]

:::group "frodo_kem"
FrodoKEM, a Learning-With-Errors key encapsulation mechanism
({Informal.citet FrodoKEM}[]).
:::

:::defTitle "frodo_kem_scheme" "FrodoKEM scheme"
:::

::::definition "frodo_kem_scheme" (parent := "frodo_kem")
$`\todo`

:::leanPill "missing"
:::

{githubLabel}`github` {githubIssue 259}[]
::::

:::defTitle "frodo_kem_correctness" "FrodoKEM correctness"
:::

::::theorem "frodo_kem_correctness" (parent := "frodo_kem")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "frodo_kem_scheme"}[] · {githubLabel}`github` {githubIssue 260}[]
::::

:::defTitle "frodo_kem_security" "FrodoKEM security"
:::

::::theorem "frodo_kem_security" (parent := "frodo_kem")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "frodo_kem_scheme"}[] · {githubLabel}`github` {githubIssue 261}[]
::::
