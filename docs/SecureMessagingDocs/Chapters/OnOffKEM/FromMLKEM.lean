import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "On-Off KEM from ML-KEM" =>

:::group "on_off_kem_on_off_kem_from_ml_kem"
On-Off KEM from ML-KEM.
:::

:::defTitle "on_off_kem_from_ml_kem_spec" "On-Off KEM from ML-KEM construction"
:::

::::definition "on_off_kem_from_ml_kem_spec" (parent := "on_off_kem_on_off_kem_from_ml_kem")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "on_off_kem_scheme"}[] · {githubLabel}`github` {githubIssue 200}[]
::::

:::defTitle "on_off_kem_from_ml_kem_correctness" "On-Off KEM from ML-KEM correctness"
:::

::::theorem "on_off_kem_from_ml_kem_correctness" (parent := "on_off_kem_on_off_kem_from_ml_kem")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "on_off_kem_from_ml_kem_spec"}[] · {uses "on_off_kem_correctness"}[] · {githubLabel}`github` {githubIssue 201}[]
::::

:::defTitle "on_off_kem_from_ml_kem_security" "On-Off KEM from ML-KEM security"
:::

::::theorem "on_off_kem_from_ml_kem_security" (parent := "on_off_kem_on_off_kem_from_ml_kem")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "on_off_kem_from_ml_kem_spec"}[] · {uses "on_off_kem_scheme"}[] · {uses "on_off_kem_security"}[] · {githubLabel}`github` {githubIssue 42}[]
::::
