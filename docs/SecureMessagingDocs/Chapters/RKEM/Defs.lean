import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessaging.RKEM.Defs

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

#doc (Manual) "RKEM Definitions" =>

:::group "rkem"
Ratcheting Key Encapsulation Mechanism (RKEM).
:::

:::defTitle "rkem_scheme" "RKEM scheme"
:::

:::definition "rkem_scheme" (parent := "rkem") (lean := "RKEMScheme")
$`\todo`

```anchor RKEMScheme (project := ".") (module := SecureMessaging.RKEM.Defs)
structure RKEMScheme (m : Type → Type u) [Monad m] (Par EK DK CT K : Type) where
  /-- `RSetup(1^λ) → par`: samples the public parameter shared by both parties. -/
  rsetup : m Par
  /-- `RKeyGen-A(par, ⊥) → (ekA, dkA)`: samples a fresh key pair for `A`. -/
  rkeygenAFresh : Par → m (EK × DK)
  /-- `RKeyGen-A(par, updated) → (ekA, dkA)`: samples an updated-distribution
  key pair for `A`. -/
  rkeygenAUpdated : Par → m (EK × DK)
  /-- `RKeyGen-B(par, ⊥) → (ekB, dkB)`: samples a fresh key pair for `B`. -/
  rkeygenBFresh : Par → m (EK × DK)
  /-- `RKeyGen-B(par, updated) → (ekB, dkB)`: samples an updated-distribution
  key pair for `B`. -/
  rkeygenBUpdated : Par → m (EK × DK)
  /-- `REnc-A(par, ekB, dkA) → (ctB, K, dk̂A)`: encapsulates towards `B`'s
  encapsulation key using `A`'s decapsulation key, producing a ciphertext for
  `B`, the shared key, and `A`'s updated decapsulation key. -/
  rencA : Par → EK → DK → m (CT × K × DK)
  /-- `RDec-A(par, dkA, ctA, ekB) → (K, ek̂B)`: decapsulates using `A`'s
  decapsulation key and `B`'s encapsulation key, producing the shared key and
  `B`'s updated encapsulation key. -/
  rdecA : Par → DK → CT → EK → m (Option (K × EK))
  /-- `REnc-B(par, ekA, dkB) → (ctA, K, dk̂B)`: as `rencA`, with the roles of
  `A` and `B` swapped. -/
  rencB : Par → EK → DK → m (CT × K × DK)
  /-- `RDec-B(par, dkB, ctB, ekA) → (K, ek̂A)`: as `rdecA`, with the roles of
  `A` and `B` swapped. -/
  rdecB : Par → DK → CT → EK → m (Option (K × EK))
```

{githubLabel}`github` {githubIssue 176}[]
:::

:::defTitle "rkem_ratchet_sim" "RKEM ratchet simulatability"
:::

::::definition "rkem_ratchet_sim" (parent := "rkem")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "rkem_scheme"}[] · {githubLabel}`github` {githubIssue 179}[]
::::

:::defTitle "rkem_security_experiment" "RKEM Security Experiment"
:::

:::definition "rkem_security_experiment" (parent := "rkem") (lean := "RKEMScheme.securityExpA")
$`\todo`

```anchor securityExpA (project := ".") (module := SecureMessaging.RKEM.Defs)
def securityExpA (rkem : RKEMScheme ProbComp Par EK DK CT K)
    (adversary : FSINDCPAAdversary EK DK CT K) [SampleableType K] : ProbComp Bool := do
  let b ← $ᵗ Bool
  let k1 ← $ᵗ K
  let par ← rkem.rsetup
  let (ekA, dkA) ← rkem.rkeygenAFresh par
  let (ekBHat, dkBHat) ← rkem.rkeygenBUpdated par
  let (ctB, k0, dkAHat) ← rkem.rencA par ekBHat dkA
  let res ← rkem.rdecB par dkBHat ctB ekA
  match res with
  | none =>
    -- Decapsulation failed in this case, we return a fresh random boolean
    let b' ← $ᵗ Bool
    return b'
  | some (_, ekAHat) =>
    let b' ← adversary ekA ekAHat ekBHat ctB dkAHat (if b then k1 else k0)
    return b == b'
```

{usesLabel}`uses` {uses "rkem_scheme"}[]
:::

:::defTitle "rkem_guess_advantageA" "RKEM Guess Advantage"
:::

:::definition "rkem_guess_advantageA" (parent := "rkem") (lean := "RKEMScheme.fsIndCpaAdvantageA")
$`\todo`

```anchor fsIndCpaAdvantageA (project := ".") (module := SecureMessaging.RKEM.Defs)
noncomputable def fsIndCpaAdvantageA (rkem : RKEMScheme ProbComp Par EK DK CT K)
    (adversary : FSINDCPAAdversary EK DK CT K) [SampleableType K] : ℝ :=
  |(Pr[= true | rkem.securityExpA adversary]).toReal - 1 / 2|
```

{usesLabel}`uses` {uses "rkem_security_experiment"}[]
:::

:::defTitle "rkem_guess_advantage" "RKEM Guess Advantage"
:::

:::definition "rkem_guess_advantage" (parent := "rkem") (lean := "RKEMScheme.fsIndCpaAdvantage")
$`\todo`

```anchor fsIndCpaAdvantage (project := ".") (module := SecureMessaging.RKEM.Defs)
noncomputable def fsIndCpaAdvantage (rkem : RKEMScheme ProbComp Par EK DK CT K)
    (adversaryA adversaryB : FSINDCPAAdversary EK DK CT K) [SampleableType K] : ℝ :=
  max (rkem.fsIndCpaAdvantageA adversaryA) (rkem.fsIndCpaAdvantageB adversaryB)
```

{usesLabel}`uses` {uses "rkem_guess_advantageA"}[]
:::

:::defTitle "rkem_forward_security" "RKEM forward security"
:::

:::definition "rkem_forward_security" (parent := "rkem") (lean := "RKEMScheme.FSINDCPASecure")
$`\todo`

```anchor FSINDCPASecure (project := ".") (module := SecureMessaging.RKEM.Defs)
def FSINDCPASecure (rkem : RKEMScheme ProbComp Par EK DK CT K)
    (adversaryA adversaryB : FSINDCPAAdversary EK DK CT K) (epsilon : ℝ) [SampleableType K] :
    Prop :=
  rkem.fsIndCpaAdvantage adversaryA adversaryB ≤ epsilon
```

{usesLabel}`uses` {uses "rkem_guess_advantage"}[] · {githubLabel}`github` {githubIssue 178}[]
:::

:::defTitle "rkem_correctness" "RKEM correctness"
:::

:::definition "rkem_correctness" (parent := "rkem") (lean := "RKEMScheme.deltaCorrect")
$`\todo`

```anchor deltaCorrect (project := ".") (module := SecureMessaging.RKEM.Defs)
def deltaCorrect (rkem : RKEMScheme m Par EK DK CT K) (runtime : ProbCompRuntime m)
    (deltaCorr : ℝ≥0∞) (deltaDist : ℝ≥0∞) [DecidableEq K] : Prop :=
  rkem.deltaCorrectUpdatedKeys runtime deltaCorr ∧ rkem.deltaCloseUpdateKeyDist runtime deltaDist
```

{usesLabel}`uses` {uses "rkem_scheme"}[] · {githubLabel}`github` {githubIssue 177}[]
:::
