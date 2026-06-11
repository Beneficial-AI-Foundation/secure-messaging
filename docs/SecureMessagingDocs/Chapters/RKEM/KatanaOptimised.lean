import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Katana RKEM (optimised)" =>

:::group "rkem_katana_rkem_optimised"
Katana RKEM (optimised).
:::

:::defTitle "optimised_katana_rkem_spec" "Optimised Katana RKEM construction"
:::

::::definition "optimised_katana_rkem_spec" (parent := "rkem_katana_rkem_optimised")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "rkem_scheme"}[] · {githubLabel}`github` {githubIssue 85}[]
::::

:::defTitle "optimised_katana_rkem_correctness" "Optimised Katana RKEM correctness"
:::

::::theorem "optimised_katana_rkem_correctness" (parent := "rkem_katana_rkem_optimised")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "optimised_katana_rkem_spec"}[] · {uses "rkem_scheme"}[] · {uses "rkem_correctness"}[] · {githubLabel}`github` {githubIssue 86}[]
::::

:::defTitle "optimised_katana_rkem_forward_security" "Optimised Katana RKEM forward security"
:::

::::theorem "optimised_katana_rkem_forward_security" (parent := "rkem_katana_rkem_optimised")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "optimised_katana_rkem_spec"}[] · {uses "rkem_scheme"}[] · {uses "rkem_forward_security"}[] · {githubLabel}`github` {githubIssue 87}[]
::::

:::defTitle "optimised_katana_rkem_ratchet_sim" "Optimised Katana RKEM ratchet simulatability"
:::

::::theorem "optimised_katana_rkem_ratchet_sim" (parent := "rkem_katana_rkem_optimised")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "optimised_katana_rkem_spec"}[] · {uses "rkem_scheme"}[] · {uses "rkem_ratchet_sim"}[] · {githubLabel}`github` {githubIssue 88}[]
::::
