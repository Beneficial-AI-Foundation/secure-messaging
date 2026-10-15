import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Chapters.CKA.Defs
import SecureMessaging.CKA.FromLWE.Construction

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

#doc (Manual) "CKA from LWE" =>

*References:*

- {Informal.citet ACD19}[]
- {Informal.citet BCDMNNRS16}[]

:::group "cka_cka_from_lwe"
CKA from LWE.
:::

:::defTitle "cka_from_lwe_spec" "CKA from LWE construction"
:::

::::definition "cka_from_lwe_spec" (parent := "cka_cka_from_lwe") (lean := "lweCKA.scheme") (tags := "gh-12") (uses := "cka")
For well-formed parameters and a noise distribution, `lweCKA.scheme` defines the CKA construction
of {Informal.citet ACD19}[], §4.1.2, using reconciliation from the original Frodo key-exchange
paper {Informal.citet BCDMNNRS16}[], §3.2. Party labels are swapped relative to
{Informal.citet ACD19}[] so that A sends first, following the repository convention.

```anchor scheme (project := ".") (module := SecureMessaging.CKA.FromLWE.Construction)
def scheme (p : Params) (_h : p.WellFormed) (χ : ProbComp (Scalar p)) :
    CKAScheme ProbComp (InitKey p) (State p) (Key p) (Message p) (Rand p) where
  initKeyGen := initKeyGen p χ
  initA := fun ik => pure (initA ik)
  initB := fun ik => pure (initB ik)
  sendA := fun st => eraseCoins <$> sendArleak χ st
  sendArleak := sendArleak χ
  recvA := recvA
  sendB := fun st => eraseCoins <$> sendBrleak χ st
  sendBrleak := sendBrleak χ
  recvB := recvB
```

Correctness and security are tracked separately in #13 and #14.
::::

:::defTitle "cka_from_lwe_correctness" "CKA from LWE correctness"
:::

::::theorem "cka_from_lwe_correctness" (parent := "cka_cka_from_lwe") (tags := "gh-13") (uses := "cka_from_lwe_spec, cka_correctness")
$`\todo`

:::leanPill "missing"
:::
::::

:::defTitle "cka_from_lwe_security" "CKA from LWE security"
:::

::::theorem "cka_from_lwe_security" (parent := "cka_cka_from_lwe") (tags := "gh-14") (uses := "cka_from_lwe_spec, cka_security")
$`\todo`

:::leanPill "missing"
:::
::::
