import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessaging.RKEM.FromKEM.Construction
import SecureMessaging.RKEM.FromKEM.Correctness

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option verso.docstring.allowMissing true

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open Informal

set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "RKEM from KEM" =>

:::group "rkem_rkem_from_kem"
RKEM from KEM.
:::

:::defTitle "rkem_from_kem_spec" "RKEM from KEM construction"
:::

:::definition "rkem_from_kem_spec" (parent := "rkem_rkem_from_kem") (lean := "kemRKEM.scheme")
$`\todo`

```anchor scheme (project := ".") (module := SecureMessaging.RKEM.FromKEM.Construction)
def scheme {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C) : RKEMScheme m Unit PK SK (PK × C) K where
  rsetup := pure ()
  rkeygenAFresh := rkeygen kem
  rkeygenAUpdated := rkeygen kem
  rkeygenBFresh := rkeygen kem
  rkeygenBUpdated := rkeygen kem
  rencA := renc kem
  rdecA := rdec kem
  rencB := renc kem
  rdecB := rdec kem
```
{usesLabel}`uses` {uses "rkem_scheme"}[] · {githubLabel}`github` {githubIssue 75}[]
:::

:::defTitle "rkem_from_kem_correctness" "RKEM from KEM correctness"
:::

:::theorem "rkem_from_kem_correctness" (parent := "rkem_rkem_from_kem") (lean := "kemRKEM.deltaCorrect")
$`\todo`

```anchor deltaCorrect (project := ".") (module := SecureMessaging.RKEM.FromKEM.Correctness)
theorem deltaCorrect [DecidableEq K] (kem : KEMScheme ProbComp K PK SK C)
    (δ : ℝ≥0∞) (hkem : kem.deltaCorrect ProbCompRuntime.probComp δ) :
    RKEMScheme.deltaCorrect (scheme kem) ProbCompRuntime.probComp δ δ
```

{usesLabel}`uses` {uses "rkem_from_kem_spec"}[] · {uses "rkem_scheme"}[] · {uses "rkem_correctness"}[] · {githubLabel}`github` {githubIssue 76}[]
:::

:::defTitle "rkem_from_kem_forward_security" "RKEM from KEM forward security"
:::

::::theorem "rkem_from_kem_forward_security" (parent := "rkem_rkem_from_kem")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "rkem_from_kem_spec"}[] · {uses "rkem_scheme"}[] · {uses "rkem_forward_security"}[] · {githubLabel}`github` {githubIssue 77}[]
::::

:::defTitle "rkem_from_kem_ratchet_sim" "RKEM from KEM ratchet simulatability"
:::

::::theorem "rkem_from_kem_ratchet_sim" (parent := "rkem_rkem_from_kem")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "rkem_from_kem_spec"}[] · {uses "rkem_scheme"}[] · {uses "rkem_ratchet_sim"}[] · {githubLabel}`github` {githubIssue 78}[]
::::
