import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "RKEM from DDH (FS)" =>

:::group "rkem_rkem_from_ddh_fs"
RKEM from DDH (FS).
:::

:::defTitle "rkem_from_ddh_fs_spec" "RKEM from DDH FS construction"
:::

::::definition "rkem_from_ddh_fs_spec" (parent := "rkem_rkem_from_ddh_fs")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "rkem_scheme"}[] · {githubLabel}`github` {githubIssue 70}[]
::::

:::defTitle "rkem_from_ddh_fs_correctness" "RKEM from DDH FS correctness"
:::

::::theorem "rkem_from_ddh_fs_correctness" (parent := "rkem_rkem_from_ddh_fs")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "rkem_from_ddh_fs_spec"}[] · {uses "rkem_scheme"}[] · {uses "rkem_correctness"}[] · {githubLabel}`github` {githubIssue 71}[]
::::

:::defTitle "rkem_from_ddh_fs_forward_security" "RKEM from DDH FS forward security"
:::

::::theorem "rkem_from_ddh_fs_forward_security" (parent := "rkem_rkem_from_ddh_fs")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "rkem_from_ddh_fs_spec"}[] · {uses "rkem_scheme"}[] · {uses "rkem_forward_security"}[] · {githubLabel}`github` {githubIssue 72}[]
::::

:::defTitle "rkem_from_ddh_fs_ratchet_sim" "RKEM from DDH FS ratchet simulatability"
:::

::::theorem "rkem_from_ddh_fs_ratchet_sim" (parent := "rkem_rkem_from_ddh_fs")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "rkem_from_ddh_fs_spec"}[] · {uses "rkem_scheme"}[] · {uses "rkem_ratchet_sim"}[] · {githubLabel}`github` {githubIssue 73}[]
::::
