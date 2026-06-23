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

We formalize the optimized Frodo/LWE CKA of {Informal.citet ACD19}[], Section 4.1.2.
The construction works as follows: `Frodo.MatrixParams` (in
`SecureMessaging.CKA.FromLWE.Basic`) fixes the concrete matrix spaces, samplers,
reconciliation maps, and reconciliation correctness assumptions; `lweCKA.frodoScheme`
turns those matrix parameters into a `CKAScheme`, and `lweCKA.frodoCorrectness`
proves correctness for that concrete scheme.

`Frodo.MatrixParams` has public key `B = A * S + E`, fresh key `B' = S' * A + E'`,
and shared value `V' = S' * B + Etilde'`. Its `RecInfo` type is the paper's
reconciliation information `C'`; `recInfo V'` is the paper's `<V'>_{2B}`,
`key V'` is the paper's key extraction, and `reconcile` is the paper's `rec`.

The repository CKA game starts from a `sendA` state. In ACD19's LWE
initialization, the first displayed half-round is paper-B sending from
`(A, B := A * S + E)` to paper-A, who receives using `(A, S)`. We align that
half-round with the repository's initial `sendA`/`recvB` transition: Lean
`sendA`/`recvB` implement paper `CKA-S-B`/`CKA-R-A`, and Lean `sendB`/`recvA`
implement paper `CKA-S-A`/`CKA-R-B`.

Correctness of reconciliation is assumed (`rec_sendA_correct`, `rec_sendB_correct`);
security is future work, where ACD19 Theorem 4 reduces the optimized CKA to the CPA
security of the Frodo KEM (Appendix C.2).
:::

:::defTitle "cka_from_lwe_spec" "CKA from LWE construction"
:::

::::definition "cka_from_lwe_spec" (parent := "cka_cka_from_lwe") (lean := "lweCKA.frodoScheme")
$`\todo`

```anchor frodoScheme (project := ".") (module := SecureMessaging.CKA.FromLWE.Construction)
def frodoScheme (p : Frodo.MatrixParams) :
    CKAScheme ProbComp (InitKey p) (State p) p.Key (Message p) (Rand p) where
  initKeyGen := p.init
  initA := fun ik => return initA p ik
  initB := fun ik => return initB p ik
  sendA := sendA p
  sendA_rleak := sendA_rleak p
  recvA := recvA p
  sendB := sendB p
  sendB_rleak := sendB_rleak p
  recvB := recvB p
```

{usesLabel}`uses` {uses "cka"}[] · {githubLabel}`github` {githubIssue 12}[]
::::

:::defTitle "cka_from_lwe_correctness" "CKA from LWE correctness"
:::

::::theorem "cka_from_lwe_correctness" (parent := "cka_cka_from_lwe") (lean := "lweCKA.frodoCorrectness")
$`\todo`

```anchor frodoCorrectness (project := ".") (module := SecureMessaging.CKA.FromLWE.Correctness)
theorem frodoCorrectness (p : Frodo.MatrixParams) [DecidableEq p.Key]
    (adv : CKAScheme.CKACorrectnessAdversary (Message p) p.Key) :
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
