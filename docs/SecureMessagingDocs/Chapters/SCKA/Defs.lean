import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessaging.SCKA.Defs

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

#doc (Manual) "SCKA Definitions" =>

:::group "cka_protocols"
SCKA protocol constructions.
:::

:::group "cka_protocols_scka"
SCKA.
:::

:::defTitle "scka_scheme" "SCKA protocol scheme"
:::

::::definition "scka_scheme" (parent := "cka_protocols_scka") (lean := "SCKAScheme")
$`\todo`

```anchor SCKAScheme (project := ".") (module := SecureMessaging.SCKA.Defs)
structure SCKAScheme (m : Type → Type u) [Monad m] (IK StA StB I Rho Rand : Type) where
  /-- Samples initial shared key material. -/
  initKeyGen : m IK
  /-- Initializes A's local state from the initial key. -/
  initA : IK → m StA
  /-- Initializes B's local state from the initial key. -/
  initB : IK → m StB
  /-- Party A's send: returns an optional (epoch,key) pair, the message sent to B,
  the sending epoch, and A's next state. -/
  sendA : StA → m (Option (Option (ℕ × I) × Rho × ℕ × StA))
  /-- Party A's randomness-leaking send: also returns the randomness used for the send. -/
  sendArleak : StA → m (Option (Option (ℕ × I) × Rho × ℕ × StA × Rand))
  /-- Party A's receive: returns the optional derived (epoch,key) pair, the receiving
  epoch, and A's next state. -/
  recvA : StA → Rho → Option (Option (ℕ × I) × ℕ × StA)
  /-- Party B's send: returns an optional (epoch,key) pair, the message sent to A,
  the sending epoch, and B's next state. -/
  sendB : StB → m (Option (Option (ℕ × I) × Rho × ℕ × StB))
  /-- Party B's randomness-leaking send: also returns the randomness used for the send. -/
  sendBrleak : StB → m (Option (Option (ℕ × I) × Rho × ℕ × StB × Rand))
  /-- Party B's receive: returns the optional derived (epoch,key) pair, the receiving
  epoch, and B's next state. -/
  recvB : StB → Rho → Option (Option (ℕ × I) × ℕ × StB)
```

{githubLabel}`github` {githubIssue 183}[]
::::

:::defTitle "scka_correctness" "SCKA protocol correctness"
:::

:::::::definition "scka_correctness" (parent := "cka_protocols_scka") (lean := "SCKAScheme.GameState, SCKAScheme.sckaCorrectnessSpec, SCKAScheme.sckaCorrectnessImpl, SCKAScheme.SCKACorrectnessAdversary, SCKAScheme.correctnessExp")
$`\todo`

*Game state*

```anchor SCKAGameState (project := ".") (module := SecureMessaging.SCKA.Defs)
structure GameState (StA StB I Rho : Type) where
  /-- Local protocol state for party A. -/
  stA : StA
  /-- Local protocol state for party B. -/
  stB : StB
  /-- Key table for A: `Key[A, t]`. -/
  keyA : ℕ → Option I
  /-- Key table for B: `Key[B, t]`. -/
  keyB : ℕ → Option I
  /-- Transit array for A's messages: `Msg[A, n] = (ρ, t^snd)`. -/
  msgA : ℕ → Option (Rho × ℕ)
  /-- Transit array for B's messages: `Msg[B, n] = (ρ, t^snd)`. -/
  msgB : ℕ → Option (Rho × ℕ)
  /-- Number of messages A has sent. -/
  nA : ℕ
  /-- Number of messages B has sent. -/
  nB : ℕ
  /-- A's current epoch `t^cur_A`. -/
  tcurA : ℕ
  /-- B's current epoch `t^cur_B`. -/
  tcurB : ℕ
  /-- Epochs exposed through corruption or randomness leakage. -/
  exposed : Finset ℕ
  /-- Epochs already challenged. -/
  challenged : Finset ℕ
  /-- Whether all correctness asserts have held so far. -/
  correct : Bool
```

:::leanPillCaption "specification for the correctness-game oracle interfaces"
:::

```anchor sckaCorrectnessSpec (project := ".") (module := SecureMessaging.SCKA.Defs)
def sckaCorrectnessSpec (Rho : Type) :=
  unifSpec                                  -- Uniform randomness
  + (Unit →ₒ Option (ℕ × Option ℕ × Rho))       -- O-Send-A
  + (Unit →ₒ Option (ℕ × Option ℕ × Rho))       -- O-Send-B
  + (ℕ →ₒ Option (ℕ × Option ℕ))                -- O-Recv-A
  + (ℕ →ₒ Option (ℕ × Option ℕ))                -- O-Recv-B
```

:::leanPillCaption "oracle set for the correctness game"
:::

```anchor sckaCorrectnessImpl (project := ".") (module := SecureMessaging.SCKA.Defs)
def sckaCorrectnessImpl [DecidableEq I] (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) :
    QueryImpl (sckaCorrectnessSpec Rho)
      (StateT (GameState StA StB I Rho) ProbComp) :=
  oracleUnif StA StB I Rho
    + oracleSendA scka + oracleSendB scka
    + oracleRecvA scka + oracleRecvB scka
```

:::leanPillCaption "type of correctness-game adversaries"
:::

```anchor SCKACorrectnessAdversary (project := ".") (module := SecureMessaging.SCKA.Defs)
abbrev SCKACorrectnessAdversary (Rho : Type) :=
  OracleComp (sckaCorrectnessSpec Rho) Bool
```

```anchor correctnessExp (project := ".") (module := SecureMessaging.SCKA.Defs)
def correctnessExp [DecidableEq I]
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (adversary : SCKACorrectnessAdversary Rho) : ProbComp Bool := do
  let ik ← scka.initKeyGen
  let stA ← scka.initA ik
  let stB ← scka.initB ik
  let (_, state) ← (simulateQ (sckaCorrectnessImpl scka) adversary).run
    (initGameState stA stB)
  return state.correct
```

{usesLabel}`uses` {uses "scka_scheme"}[] · {githubLabel}`github` {githubIssue 184}[]
:::::::

:::defTitle "scka_security" "SCKA protocol security"
:::

:::::::definition "scka_security" (parent := "cka_protocols_scka") (lean := "SCKAScheme.sckaSecuritySpec, SCKAScheme.sckaSecurityImpl, SCKAScheme.SCKAAdversary, SCKAScheme.securityExp, SCKAScheme.sckaGuessAdvantage")
$`\todo`

:::leanPillCaption "specification for the security-game oracle interfaces"
:::

```anchor sckaSecuritySpec (project := ".") (module := SecureMessaging.SCKA.Defs)
def sckaSecuritySpec (StA StB I Rho Rand : Type) :=
  sckaCorrectnessSpec Rho
  + (Unit →ₒ Option (ℕ × Option ℕ × Rho × Rand))    -- O-Send-A-rleak
  + (Unit →ₒ Option (ℕ × Option ℕ × Rho × Rand))    -- O-Send-B-rleak
  + (ℕ →ₒ Option I)                                  -- O-Chall t
  + (Unit →ₒ Option StA)                             -- O-Corrupt-A
  + (Unit →ₒ Option StB)                             -- O-Corrupt-B
```

:::leanPillCaption "oracle set for the security game"
:::

```anchor sckaSecurityImpl (project := ".") (module := SecureMessaging.SCKA.Defs)
def sckaSecurityImpl (isRandom : Bool) (vulnA : StA → Finset ℕ) (vulnB : StB → Finset ℕ)
    [SampleableType I] [DecidableEq I] (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) :
    QueryImpl (sckaSecuritySpec StA StB I Rho Rand)
      (StateT (GameState StA StB I Rho) ProbComp) :=
  sckaCorrectnessImpl scka
    + oracleSendArleak vulnA scka + oracleSendBrleak vulnB scka
    + oracleChall isRandom StA StB I Rho
    + oracleCorruptA vulnA StB I Rho + oracleCorruptB vulnB StA I Rho
```

:::leanPillCaption "type of security-game adversaries"
:::

```anchor SCKAAdversary (project := ".") (module := SecureMessaging.SCKA.Defs)
abbrev SCKAAdversary (StA StB I Rho Rand : Type) :=
  OracleComp (sckaSecuritySpec StA StB I Rho Rand) Bool
```

```anchor securityExp (project := ".") (module := SecureMessaging.SCKA.Defs)
def securityExp [SampleableType I] [DecidableEq I]
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (adversary : SCKAAdversary StA StB I Rho Rand)
    (vulnA : StA → Finset ℕ) (vulnB : StB → Finset ℕ) : ProbComp Bool := do
  let ik ← scka.initKeyGen
  let stA ← scka.initA ik
  let stB ← scka.initB ik
  let b ← $ᵗ Bool
  let (b', _) ← (simulateQ (sckaSecurityImpl b vulnA vulnB scka) adversary).run
    (initGameState stA stB)
  return (b == b')
```

:::leanPillCaption "guess advantage $`\\bigl|\\Pr[b' = b] - \\tfrac12\\bigr|`"
:::

```anchor sckaGuessAdvantage (project := ".") (module := SecureMessaging.SCKA.Defs)
noncomputable def sckaGuessAdvantage [SampleableType I] [DecidableEq I]
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (adversary : SCKAAdversary StA StB I Rho Rand)
    (vulnA : StA → Finset ℕ) (vulnB : StB → Finset ℕ) : ℝ :=
  |(Pr[= true | securityExp scka adversary vulnA vulnB]).toReal - 1 / 2|
```

{usesLabel}`uses` {uses "scka_scheme"}[] · {githubLabel}`github` {githubIssue 185}[]
:::::::
