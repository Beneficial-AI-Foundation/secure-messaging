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

::::definition "optimised_katana_rkem_spec" (parent := "rkem_katana_rkem_optimised") (tags := "gh-85")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "rkem_scheme"}[]
::::

:::defTitle "optimised_katana_rkem_correctness" "Optimised Katana RKEM correctness"
:::

::::theorem "optimised_katana_rkem_correctness" (parent := "rkem_katana_rkem_optimised") (tags := "gh-86")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "optimised_katana_rkem_spec"}[] · {uses "rkem_scheme"}[] · {uses "rkem_correctness"}[]
::::

:::defTitle "optimised_katana_rkem_forward_security" "Optimised Katana RKEM forward security"
:::

::::theorem "optimised_katana_rkem_forward_security" (parent := "rkem_katana_rkem_optimised") (tags := "gh-87")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "optimised_katana_rkem_spec"}[] · {uses "rkem_scheme"}[] · {uses "rkem_forward_security"}[]
::::

:::defTitle "optimised_katana_rkem_ratchet_sim" "Optimised Katana RKEM ratchet simulatability"
:::

::::theorem "optimised_katana_rkem_ratchet_sim" (parent := "rkem_katana_rkem_optimised") (tags := "gh-88")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "optimised_katana_rkem_spec"}[] · {uses "rkem_scheme"}[] · {uses "rkem_ratchet_sim"}[]
::::
