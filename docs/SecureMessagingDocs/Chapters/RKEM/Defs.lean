import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "RKEM Definitions" =>

:::group "rkem"
Ratcheting Key Encapsulation Mechanism (RKEM).
:::

:::defTitle "rkem_scheme" "RKEM scheme"
:::

::::definition "rkem_scheme" (parent := "rkem")
$`\todo`

:::leanPill "missing"
:::

{githubLabel}`github` {githubIssue 176}[]
::::

:::defTitle "rkem_ratchet_sim" "RKEM ratchet simulatability"
:::

::::definition "rkem_ratchet_sim" (parent := "rkem")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "rkem_scheme"}[] · {githubLabel}`github` {githubIssue 179}[]
::::

:::defTitle "rkem_forward_security" "RKEM forward security"
:::

::::definition "rkem_forward_security" (parent := "rkem")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "rkem_scheme"}[] · {githubLabel}`github` {githubIssue 178}[]
::::

:::defTitle "rkem_correctness" "RKEM correctness"
:::

::::definition "rkem_correctness" (parent := "rkem")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "rkem_scheme"}[] · {githubLabel}`github` {githubIssue 177}[]
::::
