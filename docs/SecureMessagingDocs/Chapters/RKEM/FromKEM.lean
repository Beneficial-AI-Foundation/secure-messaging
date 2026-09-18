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

::::definition "rkem_from_kem_spec" (parent := "rkem_rkem_from_kem") (lean := "kemRKEM.scheme") (tags := "gh-75") (uses := "rkem_scheme")
$`\todo`

:::leanPillCaption "fresh/updated ratcheting key generation"
:::

```anchor rkeygen (project := ".") (module := SecureMessaging.RKEM.FromKEM.Construction)
def rkeygen {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C) : Unit → m (PK × SK) :=
  fun _ => kem.keygen
```

:::leanPillCaption "encapsulation"
:::

```anchor renc (project := ".") (module := SecureMessaging.RKEM.FromKEM.Construction)
def renc {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C) (_par : Unit) (ekPeer : PK) (_dkSelf : SK) :
    m ((PK × C) × K × SK) := do
  let (ct, key) ← kem.encaps ekPeer
  let (ekSelfHat, dkSelfHat) ← kem.keygen
  return ((ekSelfHat, ct), key, dkSelfHat)
```

:::leanPillCaption "decapsulation"
:::

```anchor rdec (project := ".") (module := SecureMessaging.RKEM.FromKEM.Construction)
def rdec {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C) (total : TotalDecaps kem)
    (_par : Unit) (dkSelfHat : SK) (ctSelf : PK × C) (_ekPeer : PK) :
    m (K × PK) := do
  let (ekPeerHat, ct) := ctSelf
  let res ← kem.decaps dkSelfHat ct
  match res with
  | none => let key ← total.decapsTotal dkSelfHat ct
            return (key, ekPeerHat)
  | some key => return (key, ekPeerHat)
```

:::leanPillCaption "generic RKEM scheme"
:::

```anchor scheme (project := ".") (module := SecureMessaging.RKEM.FromKEM.Construction)
def scheme {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C) (total : TotalDecaps kem) :
    RKEMScheme m Unit PK SK (PK × C) K where
  rsetup := pure ()
  rkeygenAFresh := rkeygen kem
  rkeygenAUpdated := rkeygen kem
  rkeygenBFresh := rkeygen kem
  rkeygenBUpdated := rkeygen kem
  rencA := renc kem
  rdecA := rdec kem total
  rencB := renc kem
  rdecB := rdec kem total
```
::::

:::defTitle "rkem_from_kem_correctness" "RKEM from KEM correctness"
:::

:::theorem "rkem_from_kem_correctness" (parent := "rkem_rkem_from_kem") (lean := "kemRKEM.deltaCorrect") (tags := "gh-76") (uses := "rkem_from_kem_spec, rkem_scheme, rkem_correctness")
$`\todo`

```anchor deltaCorrect (project := ".") (module := SecureMessaging.RKEM.FromKEM.Correctness)
theorem deltaCorrect [DecidableEq K] (kem : KEMScheme ProbComp K PK SK C)
    (total : TotalDecaps kem) (δ : ℝ≥0∞) (hkem : kem.deltaCorrect ProbCompRuntime.probComp δ) :
    RKEMScheme.deltaCorrect (scheme kem total) ProbCompRuntime.probComp δ 0
```
:::

:::defTitle "rkem_from_kem_forward_security" "RKEM from KEM forward security"
:::

::::theorem "rkem_from_kem_forward_security" (parent := "rkem_rkem_from_kem") (tags := "gh-77") (uses := "rkem_from_kem_spec, rkem_scheme, rkem_forward_security")
$`\todo`

:::leanPill "missing"
:::
::::

:::defTitle "rkem_from_kem_ratchet_sim" "RKEM from KEM ratchet simulatability"
:::

::::theorem "rkem_from_kem_ratchet_sim" (parent := "rkem_rkem_from_kem") (tags := "gh-78") (uses := "rkem_from_kem_spec, rkem_scheme, rkem_ratchet_sim")
$`\todo`

:::leanPill "missing"
:::
::::
