import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "ML-KEM" =>

:::group "ml_kem"
Module-Lattice Key Encapsulation Mechanism (ML-KEM, FIPS 203).
:::

:::defTitle "ml_kem_scheme" "ML-KEM scheme"
:::

::::definition "ml_kem_scheme" (parent := "ml_kem")
$`\todo`

:::leanPill "missing"
:::

{githubLabel}`github` {githubIssue 215}[]
::::

:::defTitle "ml_kem_correctness" "ML-KEM correctness"
:::

::::definition "ml_kem_correctness" (parent := "ml_kem")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "ml_kem_scheme"}[] · {githubLabel}`github` {githubIssue 215}[]
::::

:::defTitle "ml_kem_security" "ML-KEM security"
:::

::::definition "ml_kem_security" (parent := "ml_kem")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "ml_kem_scheme"}[] · {githubLabel}`github` {githubIssue 216}[]
::::
