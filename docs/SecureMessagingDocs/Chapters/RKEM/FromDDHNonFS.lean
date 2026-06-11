import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "RKEM from DDH (non-FS)" =>

:::group "rkem_rkem_from_ddh_non_fs"
RKEM from DDH (non-FS).
:::

:::defTitle "rkem_from_ddh_nonfs_spec" "RKEM from DDH non-FS construction"
:::

::::definition "rkem_from_ddh_nonfs_spec" (parent := "rkem_rkem_from_ddh_non_fs")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "rkem_scheme"}[] · {githubLabel}`github` {githubIssue 66}[]
::::

:::defTitle "rkem_from_ddh_nonfs_correctness" "RKEM from DDH non-FS correctness"
:::

::::theorem "rkem_from_ddh_nonfs_correctness" (parent := "rkem_rkem_from_ddh_non_fs")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "rkem_from_ddh_nonfs_spec"}[] · {uses "rkem_scheme"}[] · {uses "rkem_correctness"}[] · {githubLabel}`github` {githubIssue 67}[]
::::

:::defTitle "rkem_from_ddh_nonfs_ratchet_sim" "RKEM from DDH non-FS ratchet simulatability"
:::

::::theorem "rkem_from_ddh_nonfs_ratchet_sim" (parent := "rkem_rkem_from_ddh_non_fs")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "rkem_from_ddh_nonfs_spec"}[] · {uses "rkem_scheme"}[] · {uses "rkem_ratchet_sim"}[] · {githubLabel}`github` {githubIssue 68}[]
::::
