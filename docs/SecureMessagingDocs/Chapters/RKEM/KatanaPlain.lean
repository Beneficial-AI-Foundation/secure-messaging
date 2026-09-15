import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Katana RKEM (plain)" =>

:::group "rkem_katana_rkem_plain"
Katana RKEM (plain).
:::

:::defTitle "plain_katana_rkem_spec" "Plain Katana RKEM construction"
:::

::::definition "plain_katana_rkem_spec" (parent := "rkem_katana_rkem_plain") (tags := "gh-81")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "rkem_scheme"}[]
::::

:::defTitle "plain_katana_rkem_correctness" "Plain Katana RKEM correctness"
:::

::::theorem "plain_katana_rkem_correctness" (parent := "rkem_katana_rkem_plain") (tags := "gh-82")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "plain_katana_rkem_spec"}[] · {uses "rkem_scheme"}[] · {uses "rkem_correctness"}[]
::::

:::defTitle "plain_katana_rkem_forward_security" "Plain Katana RKEM forward security"
:::

::::theorem "plain_katana_rkem_forward_security" (parent := "rkem_katana_rkem_plain") (tags := "gh-83")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "plain_katana_rkem_spec"}[] · {uses "rkem_scheme"}[] · {uses "rkem_forward_security"}[]
::::

:::defTitle "plain_katana_rkem_ratchet_sim" "Plain Katana RKEM ratchet simulatability"
:::

::::theorem "plain_katana_rkem_ratchet_sim" (parent := "rkem_katana_rkem_plain") (tags := "gh-84")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "plain_katana_rkem_spec"}[] · {uses "rkem_scheme"}[] · {uses "rkem_ratchet_sim"}[]
::::
