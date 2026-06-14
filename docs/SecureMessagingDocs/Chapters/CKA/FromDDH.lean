import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Chapters.CKA.Defs
import SecureMessaging.CKA.FromDDH.Construction
import SecureMessaging.CKA.FromDDH.Correctness
import SecureMessaging.CKA.FromDDH.Security

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

:::defTitle "cka_from_ddh_state" "CKA from DDH state"
:::

:::definition "cka_from_ddh_state" (parent := "cka_cka_from_ddh") (lean := "CKAState")
$`\todo`

```anchor CKAState (project := ".") (module := SecureMessaging.CKA.FromDDH.Construction)
inductive CKAState (F G : Type) where
  /-- Holds the peer's current DH public value and is ready to send. -/
  | sendReady : G → CKAState F G
  /-- Holds the party's sampled scalar and is ready to receive. -/
  | recvReady : F → CKAState F G
  deriving DecidableEq, Fintype, Repr
```

{usesLabel}`uses` {uses "cka"}[] · {githubLabel}`github` {githubIssue 10}[]
:::

:::defTitle "cka_from_ddh" "CKA from DDH"
:::

:::definition "cka_from_ddh" (parent := "cka_cka_from_ddh") (lean := "ddhCKA")
$`\todo`

```anchor ddhCKA (project := ".") (module := SecureMessaging.CKA.FromDDH.Construction)
def ddhCKA (F G : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    [AddCommGroup G] [Module F G] [SampleableType G]
  (gen : G) : CKAScheme ProbComp (G × F) (CKAState F G) G G F where
  initKeyGen := do
    let x ← $ᵗ F
    return (x • gen, x)
  initA := fun (h, _) => return .sendReady h
  initB := fun (_, x) => return .recvReady x
  sendA := send gen
  sendA_rleak := send_rleak gen
  sendB := send gen
  sendB_rleak := send_rleak gen
  recvA := recv
  recvB := recv
```

{usesLabel}`uses` {uses "cka"}[] · {uses "cka_from_ddh_state"}[] · {githubLabel}`github` {githubIssue 10}[]
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

::::theorem "cka_from_ddh_security" (parent := "cka_cka_from_ddh") (lean := "ddhCKA.security")
$`\todo`

```anchor security (project := ".") (module := SecureMessaging.CKA.FromDDH.Security)
theorem security (gp : GameParams)
  (hΔFS : gp.ΔFS = 1) (hΔPCS : gp.ΔPCS = 2)
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : CKAAdversary (CKAState F G) G G F) :
    ckaGuessAdvantage (ddhCKA F G gen) adversary gp ≤
      ddhGuessAdvantage gen (securityReduction gp adversary)
```

{usesLabel}`uses` {uses "cka_from_ddh"}[] · {uses "cka_security"}[] · {githubLabel}`github` {githubIssue 10}[]
::::
