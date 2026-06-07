import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Chapters.CKA.Defs
import SecureMessaging.CKA.FromDDH.Construction
import SecureMessaging.CKA.FromDDH.Correctness

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option verso.docstring.allowMissing true

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open Informal

set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "CKA from DDH" =>

:::group "cka_cka_from_ddh"
CKA from DDH.
:::

:::defTitle "cka_from_ddh" "CKA from DDH"
:::

:::definition "cka_from_ddh" (parent := "cka_cka_from_ddh") (lean := "ddhCKA")
$`\todo`


{usesLabel}`uses` {uses "cka"}[] · {githubLabel}`github` {githubIssue 10}[]
:::

:::defTitle "cka_from_ddh_correctness" "CKA from DDH correctness"
:::

:::theorem "cka_from_ddh_correctness" (parent := "cka_cka_from_ddh") (lean := "ddhCKA.correctness")
$`\todo`

$$`\Pr[\,\textsf{correctnessExp} = \mathsf{true}\,] = 1`


{usesLabel}`uses` {uses "cka_from_ddh"}[] · {uses "cka_correct"}[]
:::

:::defTitle "cka_from_ddh_security" "CKA from DDH security"
:::

::::theorem "cka_from_ddh_security" (parent := "cka_cka_from_ddh")
$`\todo`

:::leanPill "missing" "Lean security proof pending"
:::

{usesLabel}`uses` {uses "cka_from_ddh"}[] · {uses "cka_security"}[] · {githubLabel}`github` {githubIssue 10}[]
::::