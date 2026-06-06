import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Chapters.CKA.Defs
import SecureMessaging.CKA.FromDDH.Construction
import SecureMessaging.CKA.FromDDH.Correctness

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

```anchor ddhCKA (project := ".") (module := SecureMessaging.CKA.FromDDH.Construction)
def ddhCKA (F G : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    [AddCommGroup G] [Module F G] [SampleableType G]
    (gen : G) : CKAScheme ProbComp (G × F) (F ⊕ G) G G F where
  initKeyGen := do
    let x ← $ᵗ F
    return (x • gen, x)
  initA := fun (h, _) => return .inr h
  initB := fun (_, x) => return .inl x
  sendA := ddhCKA.send gen
  sendA_rleak := ddhCKA.send_rleak gen
  sendB := ddhCKA.send gen
  sendB_rleak := ddhCKA.send_rleak gen
  recvA := ddhCKA.recv
  recvB := ddhCKA.recv
```

{usesLabel}`uses` {uses "cka"}[] · {githubLabel}`github` {githubIssue 10}[]
:::

:::defTitle "cka_from_ddh_correctness" "CKA from DDH correctness"
:::

:::theorem "cka_from_ddh_correctness" (parent := "cka_cka_from_ddh") (lean := "ddhCKA.correctness")
$`\todo`

$$`\Pr[\,\textsf{correctnessExp} = \mathsf{true}\,] = 1`

```anchor correctness (project := ".") (module := SecureMessaging.CKA.FromDDH.Correctness)
theorem correctness [DecidableEq G] (adv : CKACorrectnessAdversary G G) :
    Pr[= true | correctnessExp (ddhCKA F G gen) adv] = 1
```

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