import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Chapters.CKA.Defs
import SecureMessaging.CKA.FromLWE.Construction
import SecureMessaging.CKA.FromLWE.Correctness

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

:::group "cka_cka_from_lwe"
CKA from LWE.

We formalize the optimized Frodo/LWE CKA of {Informal.citet ACD19}[], Section 4.1.2. The
paper sends from B first; the repository's game is A-first, so the parties are exchanged,
giving the paper's protocol up to renaming.

`Frodo.CKAParams` abstracts the protocol; `lweCKA.scheme` and `lweCKA.correctness` are
proved against it. `Frodo.MatrixParams` is the concrete model over `ZMod q`, with public
key `B = A * S + E`, fresh key `B' = S' * A + E'`, and shared value
`V' = S' * B + Etilde'`. `Frodo.concreteCKAParams` instantiates the abstraction, so
`lweCKA.frodoScheme` and `lweCKA.frodoCorrectness` specialize the abstract results, and
`Frodo.kem` is the Appendix C.2 KEM. Correctness of reconciliation is assumed
(`rec_sendA_correct`, `rec_sendB_correct`); security (ACD19 Theorem 4, `Delta_CKA = 1`)
is future work.
:::

:::defTitle "cka_from_lwe_spec" "CKA from LWE construction"
:::

::::definition "cka_from_lwe_spec" (parent := "cka_cka_from_lwe") (lean := "lweCKA.frodoScheme")
$`\todo`

```anchor frodoScheme (project := ".") (module := SecureMessaging.CKA.FromLWE.Construction)
def frodoScheme (p : Frodo.MatrixParams) :
    CKAScheme ProbComp (InitKey (Frodo.concreteCKAParams p))
      (State (Frodo.concreteCKAParams p)) p.Key
      (Message (Frodo.concreteCKAParams p)) (Rand (Frodo.concreteCKAParams p)) :=
  scheme (Frodo.concreteCKAParams p)
```

{usesLabel}`uses` {uses "cka"}[] · {githubLabel}`github` {githubIssue 12}[]
::::

:::defTitle "cka_from_lwe_correctness" "CKA from LWE correctness"
:::

::::theorem "cka_from_lwe_correctness" (parent := "cka_cka_from_lwe") (lean := "lweCKA.frodoCorrectness")
$`\todo`

```anchor frodoCorrectness (project := ".") (module := SecureMessaging.CKA.FromLWE.Correctness)
theorem frodoCorrectness (p : Frodo.MatrixParams) [DecidableEq p.Key]
    (adv : CKAScheme.CKACorrectnessAdversary (Message (Frodo.concreteCKAParams p)) p.Key) :
    Pr[= true | CKAScheme.correctnessExp (frodoScheme p) adv] = 1
```

{usesLabel}`uses` {uses "cka_from_lwe_spec"}[] · {uses "cka_correctness"}[] · {githubLabel}`github` {githubIssue 13}[]
::::

:::defTitle "cka_from_lwe_security" "CKA from LWE security"
:::

::::theorem "cka_from_lwe_security" (parent := "cka_cka_from_lwe")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "cka_from_lwe_spec"}[] · {uses "cka_security"}[] · {githubLabel}`github` {githubIssue 14}[]
::::
