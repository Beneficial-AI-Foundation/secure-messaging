import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessaging.CKA.Defs

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

#doc (Manual) "CKA Definitions" =>


:::defTitle "cka" "(Continuous Key Agreement - CKA scheme)"
:::

:::definition "cka" (lean := "CKAScheme")
$`\todo`

```anchor CKAScheme (project := ".") (module := SecureMessaging.CKA.Defs)
structure CKAScheme (m : Type → Type u) [Monad m] (IK St I Rho Rand : Type) where
  /-- samples initial shared key -/
  initKeyGen : m IK
  /-- initializes A's local state from the initial key -/
  initA : IK → m St
  /-- initializes B's local state from the initial key -/
  initB : IK → m St
  /-- Party A's send: returns the fresh epoch key, message sent to B, and A's next state. -/
  sendA : St → m (Option (I × Rho × St))
  /-- Party A's randomness-leaking send: also returns the randomness used for the send. -/
  sendA_rleak : St → m (Option (I × Rho × St × Rand))
  /-- Party A's receive: returns the derived epoch key and A's next state. -/
  recvA : St → Rho → Option (I × St)
  /-- Party B's send: returns the fresh epoch key, message sent to A, and B's next state. -/
  sendB : St → m (Option (I × Rho × St))
  /-- Party B's randomness-leaking send: also returns the randomness used for the send. -/
  sendB_rleak : St → m (Option (I × Rho × St × Rand))
  /-- Party B's receive: returns the derived epoch key and B's next state. -/
  recvB : St → Rho → Option (I × St)
```

{githubLabel}`github` {githubIssue 195}[]
:::



:::defTitle "cka_oracles" "CKA game oracles"
:::

:::::::definition "cka_oracles" (lean := "CKAScheme.GameState, CKAScheme.GameParams, CKAScheme.isChallengeEpoch,
CKAScheme.allowCorrPCS, CKAScheme.allowCorrFS, CKAScheme.allowCorr, CKAScheme.oracleSendA, CKAScheme.oracleSendB,
CKAScheme.oracleSendA_rleak, CKAScheme.oracleSendB_rleak, CKAScheme.oracleRecvA, CKAScheme.oracleRecvB,
CKAScheme.oracleChallA, CKAScheme.oracleChallB, CKAScheme.oracleCorruptA, CKAScheme.oracleCorruptB")
$`\todo`

*Game state* $`(\stA, \stB, \rho_\mathsf{A}, \rho_\mathsf{B}, K_\mathsf{A}, K_\mathsf{B}, \mathsf{correct}, \mathsf{last}, t_\mathsf{A}, t_\mathsf{B})`

- $`\stA`, $`\stB`: local protocol states for parties A and B.
- $`\rho_\mathsf{A}`, $`\rho_\mathsf{B}`: pending messages sent by A and B.
- $`K_\mathsf{A}`, $`K_\mathsf{B}`: sender keys associated with pending sent messages.
- $`\mathsf{correct}`: records whether all delivered epoch keys have matched so far.
- $`\mathsf{last}`: the last oracle action, used to enforce alternating communication.
- $`t_\mathsf{A}`, $`t_\mathsf{B}`: per-party epoch counters.

```anchor GameState (project := ".") (module := SecureMessaging.CKA.Defs)
structure GameState (St I Rho : Type) where
  /-- Local protocol state for party A. -/
  stA : St
  /-- Local protocol state for party B. -/
  stB : St
  /-- Latest undelivered message sent from A to B. -/
  rhoA : Option Rho
  /-- Latest undelivered message sent from B to A. -/
  rhoB : Option Rho
  /-- Sender key corresponding to `rhoA`. -/
  keyA : Option I
  /-- Sender key corresponding to `rhoB`. -/
  keyB : Option I
  /-- Whether delivered epoch keys have agreed so far. -/
  correct : Bool
  /-- Last oracle action, used to enforce alternating communication. -/
  lastAction : Option CKAAction
  /-- Epoch counter for A, incremented on A-side send, challenge, or receive. -/
  tA : ℕ
  /-- Epoch counter for B, incremented on B-side send, challenge, or receive. -/
  tB : ℕ
```

*Game parameters* $`(t^*, \Delta_\mathsf{FS}, \Delta_\mathsf{PCS}, \mathsf{chall})`

- $`t^*`: challenge epoch selected for the security experiment.
- $`\Delta_\mathsf{FS}`: forward-secrecy delay after which post-challenge corruption is allowed.
- $`\Delta_\mathsf{PCS}`: post-compromise-security delay before the challenge during which corruption is disallowed.
- $`\mathsf{chall}`: party selected for the challenge oracle.

```anchor GameParams (project := ".") (module := SecureMessaging.CKA.Defs)
structure GameParams where
  /-- Epoch challenged by the adversary. -/
  challengeEpoch : ℕ
  /-- Forward-secrecy delay after which state corruption is allowed. -/
  ΔFS : ℕ
  /-- Post-compromise-security delay before the challenge during which corruption is disallowed. -/
  ΔPCS : ℕ
  /-- Party selected for the challenge oracle. -/
  challengedParty : CKAParty
```

*Predicates*

$`\allow(t_\mathsf{A},t_\mathsf{B},t^*,\Delta_\mathsf{FS},\Delta_\mathsf{PCS},P) \;\Leftrightarrow\; \max(t_\mathsf{A},t_\mathsf{B})+\Delta_\mathsf{PCS}\leq t^* \;\vee\; t^*+\Delta_\mathsf{FS}\leq t_P`

```anchor allowCorrPCS (project := ".") (module := SecureMessaging.CKA.Defs)
def allowCorrPCS (gp : GameParams) (state : GameState St I Rho) : Bool :=
  (max state.tA state.tB) + gp.ΔPCS ≤ gp.challengeEpoch
```

```anchor allowCorrFS (project := ".") (module := SecureMessaging.CKA.Defs)
abbrev allowCorrFS (gp : GameParams) (state : GameState St I Rho) : CKAParty → Bool
  | .A => gp.challengeEpoch + gp.ΔFS ≤ state.tA
  | .B => gp.challengeEpoch + gp.ΔFS ≤ state.tB
```

```anchor allowCorr (project := ".") (module := SecureMessaging.CKA.Defs)
def allowCorr (gp : GameParams) (state : GameState St I Rho) : CKAParty → Bool
  | p => allowCorrPCS gp state || allowCorrFS gp state p
```

::::::gameGrid
:::::gameCell "\\OSendA" (kind := "oracle")
$`t_\mathsf{A}\gets t_\mathsf{A}+1;\quad (K_\mathsf{A},\rho_\mathsf{A},\stA) \sample \SendA(\stA);\quad \Return(\rho_\mathsf{A},K_\mathsf{A})`

```anchor oracleSendA (project := ".") (module := SecureMessaging.CKA.Defs)
def oracleSendA (cka : CKAScheme ProbComp IK St I Rho Rand) :
    QueryImpl (Unit →ₒ Option (Rho × I)) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    -- Only allow A to send if it is A's turn in alternating communication.
    if validStep state.lastAction .sendA then
      -- Increment A's epoch counter.
      let state := { state with tA := state.tA + 1 }
      -- Run A's send algorithm on the current A-state.
      match ← liftM (cka.sendA state.stA) with
      | none => pure none
      | some (key, ρ, stA') =>
        -- Update game state.
        set { state with
          stA := stA', rhoA := some ρ, keyA := some key,
          lastAction := some .sendA }
        -- Return the message and key to the adversary.
        return some (ρ, key)
    else pure none
```
:::::

:::::gameCell "\\OSendB" (kind := "oracle")
$`t_\mathsf{B}\gets t_\mathsf{B}+1;\quad (K_\mathsf{B},\rho_\mathsf{B},\stB) \sample \SendB(\stB);\quad \Return(\rho_\mathsf{B},K_\mathsf{B})`

```anchor oracleSendB (project := ".") (module := SecureMessaging.CKA.Defs)
def oracleSendB (cka : CKAScheme ProbComp IK St I Rho Rand) :
    QueryImpl (Unit →ₒ Option (Rho × I)) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    -- Only allow B to send if it is B's turn in alternating communication.
    if validStep state.lastAction .sendB then
      -- Increment B's epoch counter.
      let state := { state with tB := state.tB + 1 }
      -- Run B's send algorithm on the current B-state.
      match ← liftM (cka.sendB state.stB) with
      | none => pure none
      | some (key, ρ, stB') =>
        -- Update game state.
        set { state with
          stB := stB', rhoB := some ρ, keyB := some key,
          lastAction := some .sendB }
        -- Return the message and key to the adversary.
        return some (ρ, key)
    else pure none
```
:::::


:::::gameCell "\\OSendARLeak" (kind := "oracle")
$`\req\;\max(t_\mathsf{A}+1,t_\mathsf{B})+\Delta_\mathsf{PCS}\leq t^*;\quad (K_\mathsf{A},\rho_\mathsf{A},\stA,r) \sample \SendARLeak(\stA);\quad t_\mathsf{A}\gets t_\mathsf{A}+1;\quad \Return(\rho_\mathsf{A},K_\mathsf{A},r)`

```anchor oracleSendA_rleak (project := ".") (module := SecureMessaging.CKA.Defs)
def oracleSendA_rleak (gp : GameParams) (cka : CKAScheme ProbComp IK St I Rho Rand) :
    QueryImpl (Unit →ₒ Option (Rho × I × Rand)) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .sendA then
      let state := { state with tA := state.tA + 1 }
      if allowCorrPCS gp state then
        match ← liftM (cka.sendA_rleak state.stA) with
        | none => pure none
        | some (key, ρ, stA', rand) =>
          set { state with
            stA := stA', rhoA := some ρ, keyA := some key,
            lastAction := some .sendA }
          return some (ρ, key, rand)
      else pure none
    else pure none
```
:::::

:::::gameCell "\\OSendBRLeak" (kind := "oracle")
$`\req\;\max(t_\mathsf{A},t_\mathsf{B}+1)+\Delta_\mathsf{PCS}\leq t^*;\quad (K_\mathsf{B},\rho_\mathsf{B},\stB,r) \sample \SendBRLeak(\stB);\quad t_\mathsf{B}\gets t_\mathsf{B}+1;\quad \Return(\rho_\mathsf{B},K_\mathsf{B},r)`

```anchor oracleSendB_rleak (project := ".") (module := SecureMessaging.CKA.Defs)
def oracleSendB_rleak (gp : GameParams) (cka : CKAScheme ProbComp IK St I Rho Rand) :
    QueryImpl (Unit →ₒ Option (Rho × I × Rand)) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .sendB then
      let state := { state with tB := state.tB + 1 }
      if allowCorrPCS gp state then
        match ← liftM (cka.sendB_rleak state.stB) with
        | none => pure none
        | some (key, ρ, stB', rand) =>
          set { state with
            stB := stB', rhoB := some ρ, keyB := some key,
            lastAction := some .sendB }
          return some (ρ, key, rand)
      else pure none
    else pure none
```
:::::

:::::gameCell "\\ORecA" (kind := "oracle")
$`t_\mathsf{A}\gets t_\mathsf{A}+1;\quad (K,\stA) \getsval \RecA(\stA,\rho_\mathsf{B});\quad \mathsf{correct} \gets \mathsf{correct}\wedge(K_\mathsf{B}{=}K)`

```anchor oracleRecvA (project := ".") (module := SecureMessaging.CKA.Defs)
def oracleRecvA [DecidableEq I] (cka : CKAScheme ProbComp IK St I Rho Rand) :
    QueryImpl (Unit →ₒ Unit) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    -- Only allow A to receive if it is A's turn in alternating communication.
    if validStep state.lastAction .recvA then
      -- Increment A's epoch counter.
      let state := { state with tA := state.tA + 1 }
      match state.rhoB with
      | none => pure () -- No pending message.
      | some ρ =>
        -- Run A's receive algorithm on the current A-state and B's message.
        match cka.recvA state.stA ρ with
        | none =>
          set { state with
            rhoB := none, keyB := none,
            correct := false, lastAction := some .recvA }
        | some (keyA, stA') =>
          let ok := state.keyB == some keyA
          set { state with
            -- Update game state.
            stA := stA', rhoB := none, keyB := none,
            -- Update correctness flag.
            correct := state.correct && ok, lastAction := some .recvA }
    else pure ()
```
:::::

:::::gameCell "\\ORecB" (kind := "oracle")
$`t_\mathsf{B}\gets t_\mathsf{B}+1;\quad (K,\stB) \getsval \RecB(\stB,\rho_\mathsf{A});\quad \mathsf{correct} \gets \mathsf{correct}\wedge(K_\mathsf{A}{=}K)`

```anchor oracleRecvB (project := ".") (module := SecureMessaging.CKA.Defs)
def oracleRecvB [DecidableEq I] (cka : CKAScheme ProbComp IK St I Rho Rand) :
    QueryImpl (Unit →ₒ Unit) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    -- Only allow B to receive if it is B's turn in alternating communication.
    if validStep state.lastAction .recvB then
      -- Increment B's epoch counter.
      let state := { state with tB := state.tB + 1 }
      match state.rhoA with
      | none => pure () -- No pending message.
      | some ρ =>
        -- Run B's receive algorithm on the current B-state and A's message.
        match cka.recvB state.stB ρ with
        | none =>
          set { state with
            rhoA := none, keyA := none,
            correct := false, lastAction := some .recvB }
        | some (keyB, stB') =>
          let ok := state.keyA == some keyB
          set { state with
            -- Update game state.
            stB := stB', rhoA := none, keyA := none,
            -- Update correctness flag.
            correct := state.correct && ok, lastAction := some .recvB }
    else pure ()
```
:::::

:::::gameCell "\\OChallA" (kind := "oracle")
$`t_\mathsf{A}\gets t_\mathsf{A}+1;\quad \req\;\mathsf{chall}{=}\mathsf{A}\wedge t_\mathsf{A}=t^*;\quad (K_\mathsf{A},\rho_\mathsf{A},\stA) \sample \SendA(\stA)`

$`\mathsf{if}\;b\;\mathsf{then}\;K \sample \mathcal K\;\mathsf{else}\;K \gets K_\mathsf{A};\quad \Return(\rho_\mathsf{A},K)`

```anchor oracleChallA (project := ".") (module := SecureMessaging.CKA.Defs)
def oracleChallA (gp : GameParams) (isRandom : Bool) [SampleableType I]
    (cka : CKAScheme ProbComp IK St I Rho Rand) :
    QueryImpl (Unit →ₒ Option (Rho × I)) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .challA then
    -- Increment A's epoch counter.
      let state := { state with tA := state.tA + 1 }
    -- Enforce correct challenge party and epoch.
      if gp.challengedParty == .A && isChallengeEpoch gp state then
        -- Run A's send algorithm on the current A-state.
        match ← liftM (cka.sendA state.stA) with
        | none => pure none
        | some (key, ρ, stA') =>
          -- Real or random key for the adversary.
          let outKey ← if isRandom then liftM ($ᵗ I : ProbComp I) else pure key
          -- Update game state.
          set { state with
            stA := stA', rhoA := some ρ, keyA := some key,
            lastAction := some .challA }
          -- Return the message and key to the adversary.
          return some (ρ, outKey)
      else pure none
    else pure none
```
:::::

:::::gameCell "\\OChallB" (kind := "oracle")
$`t_\mathsf{B}\gets t_\mathsf{B}+1;\quad \req\;\mathsf{chall}{=}\mathsf{B}\wedge t_\mathsf{B}=t^*;\quad (K_\mathsf{B},\rho_\mathsf{B},\stB) \sample \SendB(\stB)`

$`\mathsf{if}\;b\;\mathsf{then}\;K \sample \mathcal K\;\mathsf{else}\;K \gets K_\mathsf{B};\quad \Return(\rho_\mathsf{B},K)`

```anchor oracleChallB (project := ".") (module := SecureMessaging.CKA.Defs)
def oracleChallB (gp : GameParams) (isRandom : Bool) [SampleableType I]
    (cka : CKAScheme ProbComp IK St I Rho Rand) :
    QueryImpl (Unit →ₒ Option (Rho × I)) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .challB then
      -- Increment B's epoch counter.
      let state := { state with tB := state.tB + 1 }
      -- Enforce correct challenge party and epoch.
      if gp.challengedParty == .B && isChallengeEpoch gp state then
        -- Run B's send algorithm on the current B-state.
        match ← liftM (cka.sendB state.stB) with
        | none => pure none
        | some (key, ρ, stB') =>
          let outKey ← if isRandom then liftM ($ᵗ I : ProbComp I) else pure key
          -- Update game state.
          set { state with
            stB := stB', rhoB := some ρ, keyB := some key,
            lastAction := some .challB }
          -- Return the message and key to the adversary.
          return some (ρ, outKey)
      else pure none
    else pure none
```
:::::

:::::gameCell "\\OCorrA" (kind := "oracle")
$`\req\;\allow(t_\mathsf{A},t_\mathsf{B},t^*,\Delta_\mathsf{FS},\Delta_\mathsf{PCS},\mathsf{A});\quad \Return\stA`

```anchor oracleCorruptA (project := ".") (module := SecureMessaging.CKA.Defs)
def oracleCorruptA (gp : GameParams) (St I Rho : Type) :
    QueryImpl (Unit →ₒ Option St) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    if allowCorr gp state .A then return some state.stA
    else return none
```
:::::

:::::gameCell "\\OCorrB" (kind := "oracle")
$`\req\;\allow(t_\mathsf{A},t_\mathsf{B},t^*,\Delta_\mathsf{FS},\Delta_\mathsf{PCS},\mathsf{B});\quad \Return\stB`

```anchor oracleCorruptB (project := ".") (module := SecureMessaging.CKA.Defs)
def oracleCorruptB (gp : GameParams) (St I Rho : Type) :
    QueryImpl (Unit →ₒ Option St) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    if allowCorr gp state .B then return some state.stB
    else return none
```
:::::
::::::

{usesLabel}`uses` {uses "cka"}[]
:::::::


:::defTitle "cka_correctness" "CKA correctness"
:::

:::::::definition "cka_correctness" (lean := "CKAScheme.correctnessExp, CKAScheme.ckaCorrectnessImpl, CKAScheme.CKACorrectnessAdversary")
$`\todo`

Let $`\O = \{\OSendA, \ORecA, \OSendB, \ORecB\}`.

:::leanPillCaption "specification for oracle interfaces"
:::

```anchor ckaCorrectnessSpec (project := ".") (module := SecureMessaging.CKA.Defs)
def ckaCorrectnessSpec (Rho I : Type) :=
  unifSpec                        -- Uniform randomness
  + (Unit →ₒ Option (Rho × I))   -- O-Send-A (outputs message and key)
  + (Unit →ₒ Unit)               -- O-Recv-A (no adversary I/O; delivers the pending sent message)
  + (Unit →ₒ Option (Rho × I))   -- O-Send-B (outputs message and key)
  + (Unit →ₒ Unit)               -- O-Recv-B (no adversary I/O; delivers the pending sent message)
```

:::leanPillCaption "oracle set $`\\O`"
:::

```anchor ckaCorrectnessImpl (project := ".") (module := SecureMessaging.CKA.Defs)
def ckaCorrectnessImpl [DecidableEq I] (cka : CKAScheme ProbComp IK St I Rho Rand) :
    QueryImpl (ckaCorrectnessSpec Rho I) (StateT (GameState St I Rho) ProbComp) :=
  oracleUnif St I Rho
    + oracleSendA cka + oracleRecvA cka
    + oracleSendB cka + oracleRecvB cka
```

:::leanPillCaption "type of adversaries with oracle access to $`\\O`"
:::

```anchor CKACorrectnessAdversary (project := ".") (module := SecureMessaging.CKA.Defs)
abbrev CKACorrectnessAdversary (Rho I : Type) := OracleComp (ckaCorrectnessSpec Rho I) Bool
```

::::::gameGrid
:::::gameCell "\\Exp{\\textsf{cor}}{\\textsf{CKA}}(\\adv)" (kind := "game")
$`\lcka \sample \mathsf{Init\text{-}KeyGen}(1^\lambda);\quad \stA \getsval \InitA(\lcka);\quad \stB \getsval \InitB(\lcka)`

$`b' \getsval \adv^{\O};\quad \Return \mathsf{correct}`
:::::
::::::

```anchor correctnessExp (project := ".") (module := SecureMessaging.CKA.Defs)
def correctnessExp [DecidableEq I] (cka : CKAScheme ProbComp IK St I Rho Rand)
    (adversary : CKACorrectnessAdversary Rho I) : ProbComp Bool := do
  let ik ← cka.initKeyGen
  let stA ← cka.initA ik
  let stB ← cka.initB ik
  let (_, state) ←
    (simulateQ (ckaCorrectnessImpl cka) adversary).run (initGameState stA stB)
  return state.correct
```

{usesLabel}`uses` {uses "cka"}[] · {uses "cka_oracles"}[] · {githubLabel}`github` {githubIssue 196}[]
:::::::

:::defTitle "cka_security" "CKA security experiment"
:::

:::::::definition "cka_security" (lean := "CKAScheme.securityExp, CKAScheme.ckaSecurityImpl, CKAScheme.CKAAdversary")
$`\todo`

Let $`\O = \{\OSendA, \ORecA, \OChallA, \OCorrA, \OSendARLeak, \OSendB, \ORecB, \OChallB, \OCorrB, \OSendBRLeak\}`.

:::leanPillCaption "specification for oracle interfaces"
:::

```anchor ckaSecuritySpec (project := ".") (module := SecureMessaging.CKA.Defs)
def ckaSecuritySpec (St Rho I Rand : Type) :=
  ckaCorrectnessSpec Rho I
  + (Unit →ₒ Option (Rho × I))   -- O-Chall-A (outputs message and key)
  + (Unit →ₒ Option (Rho × I))   -- O-Chall-B (outputs message and key)
  + (Unit →ₒ Option St)           -- O-Corrupt-A (outputs party state)
  + (Unit →ₒ Option St)           -- O-Corrupt-B (outputs party state)
  + (Unit →ₒ Option (Rho × I × Rand)) -- O-Send-A-rleak
  + (Unit →ₒ Option (Rho × I × Rand)) -- O-Send-B-rleak
```

:::leanPillCaption "oracle set $`\\O`"
:::

```anchor ckaSecurityImpl (project := ".") (module := SecureMessaging.CKA.Defs)
def ckaSecurityImpl (gp : GameParams) (isRandom : Bool) [SampleableType I] [DecidableEq I]
    (cka : CKAScheme ProbComp IK St I Rho Rand) :
    QueryImpl (ckaSecuritySpec St Rho I Rand) (StateT (GameState St I Rho) ProbComp) :=
  ckaCorrectnessImpl cka
    + oracleChallA gp isRandom cka + oracleChallB gp isRandom cka
    + oracleCorruptA gp St I Rho + oracleCorruptB gp St I Rho
    + oracleSendA_rleak gp cka + oracleSendB_rleak gp cka
```

:::leanPillCaption "type of adversaries with oracle access to $`\\O`"
:::

```anchor CKAAdversary (project := ".") (module := SecureMessaging.CKA.Defs)
abbrev CKAAdversary (St Rho I Rand : Type) := OracleComp (ckaSecuritySpec St Rho I Rand) Bool
```

::::::gameGrid
:::::gameCell "\\Exp{\\textsf{sec}}{\\textsf{CKA}}(\\adv)" (kind := "game")
$`\lcka \sample \mathsf{Init\text{-}KeyGen}(1^\lambda);\quad \stA \getsval \InitA(\lcka);\quad \stB \getsval \InitB(\lcka);\quad t_\mathsf{A},t_\mathsf{B} \getsval 0;\quad b \sample \{0,1\}`

$`b' \getsval \adv^{\O};\quad \Return[b'=b]`
:::::
::::::

```anchor securityExp (project := ".") (module := SecureMessaging.CKA.Defs)
def securityExp [SampleableType I] [DecidableEq I] (cka : CKAScheme ProbComp IK St I Rho Rand)
  (adversary : CKAAdversary St Rho I Rand)
    (gp : GameParams) : ProbComp Bool := do
  let ik ← cka.initKeyGen
  let stA ← cka.initA ik
  let stB ← cka.initB ik
  let b ← $ᵗ Bool
  let (b', _) ← (simulateQ (ckaSecurityImpl gp b cka) adversary).run (initGameState stA stB)
  return (b == b')
```

{usesLabel}`uses` {uses "cka"}[] · {uses "cka_oracles"}[] · {githubLabel}`github` {githubIssue 197}[]
:::::::


:::defTitle "cka_advantage" "CKA guess advantage"
:::

:::definition "cka_advantage" (lean := "CKAScheme.ckaGuessAdvantage")
$`\todo`

$$`\Adv{\textsf{guess}}(\adv, gp)
  \;=\; \Bigl|\, \Pr\bigl[\,\Exp{\textsf{sec}}{\textsf{CKA}}(\adv,gp) = 1\,\bigr] - \tfrac12 \,\Bigr|
  \;=\; \Bigl|\, \Pr[\,b' = b\,] - \tfrac12 \,\Bigr|`

```anchor ckaGuessAdvantage (project := ".") (module := SecureMessaging.CKA.Defs)
noncomputable def ckaGuessAdvantage [SampleableType I] [DecidableEq I]
    (cka : CKAScheme ProbComp IK St I Rho Rand) (adversary : CKAAdversary St Rho I Rand)
    (gp : GameParams) : ℝ :=
  |(Pr[= true | securityExp cka adversary gp]).toReal - 1 / 2|
```

{usesLabel}`uses` {uses "cka_security"}[]
:::
