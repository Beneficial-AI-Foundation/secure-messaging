import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Chapters.CKA.Defs
import SecureMessaging.CKA.FromKEM.Construction
import SecureMessaging.CKA.FromKEM.Correctness
import SecureMessaging.CKA.FromKEM.Security

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

#doc (Manual) "CKA from KEM" =>

*References:*

- {Informal.citet ACD19}[]

:::group "cka_cka_from_kem"
CKA from KEM.
:::

:::defTitle "cka_from_kem_spec" "CKA from KEM construction"
:::

::::definition "cka_from_kem_spec" (parent := "cka_cka_from_kem") (lean := "kemCKA.scheme")
$`\todo`

```anchor scheme (project := ".") (module := SecureMessaging.CKA.FromKEM.Construction)
def scheme {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem) :
    CKAScheme m (InitKey PK SK) (State PK SK) K (Message C PK) leak.Rand where
  initKeyGen := kem.keygen
  initA := fun ik => return initA ik
  initB := fun ik => return initB ik
  sendA := send kem
  sendA_rleak := send_rleak kem leak
  recvA := recv hDet
  sendB := send kem
  sendB_rleak := send_rleak kem leak
  recvB := recv hDet
```

{usesLabel}`uses` {uses "cka"}[] · {githubLabel}`github` {githubIssue 3}[]
::::

:::defTitle "cka_from_kem_correctness" "CKA from KEM correctness"
:::

::::theorem "cka_from_kem_correctness" (parent := "cka_cka_from_kem") (lean := "kemCKA.correctness")
$`\todo`

```anchor correctness (project := ".") (module := SecureMessaging.CKA.FromKEM.Correctness)
theorem correctness [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (adv : CKAScheme.CKACorrectnessAdversary (Message C PK) K) :
    Pr[= true | CKAScheme.correctnessExp (scheme kem hDet leak) adv] = 1
```

{usesLabel}`uses` {uses "cka_from_kem_spec"}[] · {uses "cka_correct"}[] · {githubLabel}`github` {githubIssue 4}[]
::::

:::defTitle "cka_from_kem_security" "CKA from KEM security"
:::

::::theorem "cka_from_kem_security" (parent := "cka_cka_from_kem") (lean := "kemCKA.security")
$`\todo`

```anchor security (project := ".") (module := SecureMessaging.CKA.FromKEM.Security)
theorem security [SampleableType K] [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : DeterministicDecaps kem)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (leak : RandLeak kem)
    (adv : Adversary (kem := kem) leak)
    (gp : CKAScheme.GameParams)
    (hgp : AdmissibleParams gp) :
    CKAScheme.ckaDistAdvantage (scheme kem hDet leak) adv gp ≤
      KEMScheme.IND_CPA_Advantage (kem := kem) ProbCompRuntime.probComp
        (ckaToINDCPAReduction kem hDet leak adv gp)
```

{usesLabel}`uses` {uses "cka_from_kem_spec"}[] · {uses "cka_security"}[] · {githubLabel}`github` {githubIssue 5}[]
::::
