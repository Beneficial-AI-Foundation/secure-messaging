import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Visuals.SCKAAdversary
import SecureMessagingDocs.Bibliography
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

:::::::definition "scka_scheme" (parent := "cka_protocols_scka") (lean := "SCKAScheme") (tags := "gh-183")
{Informal.citet SCKA25}[], Definition 3.1.

An SCKA scheme is defined by the parameters and algorithms described below.

::::::gameGrid
:::::gameCell "\\textsf{Notation}" (kind := "scheme-notation")
::::table -header
*
  *
    * $`\lambda`: security parameter.
    * $`\mathcal{I}_{\mathsf{CKA}}`: initial key space.
    * $`\mathcal{I}`: derived key space.
    * $`\stA`, $`\stB`: local states of A and B.
    * $`\rho`: protocol message.
  *
    * $`(t,I)\in(\mathbb{N}\times\mathcal{I})\cup\{(\bot,\bot)\}`:
      an epoch and its derived key, or $`(\bot,\bot)` if no key is derived.
    * $`t_\A^\mathsf{snd},t_\B^\mathsf{snd}\in\mathbb{N}`: key epochs safe for sending messages.
    * $`t_\A^\mathsf{rcv},t_\B^\mathsf{rcv}\in\mathbb{N}`: sending epochs of received messages.
::::
:::::

:::::gameCell "\\textsf{Algorithms}" (kind := "scheme-algorithms")
$`\Init\text{-}\KeyGen(1^\lambda) \to I_{\mathsf{CKA}}\in\mathcal{I}_{\mathsf{CKA}}`: On input the security parameter $`1^\lambda`, output an initial key $`I_{\mathsf{CKA}}\in\mathcal{I}_{\mathsf{CKA}}`.

::::table -header
*
  * *Party A*

    $`\InitA(I_{\mathsf{CKA}})\to\stA`: On input an initial key $`I_{\mathsf{CKA}}\in\mathcal{I}_{\mathsf{CKA}}`, output an initial state $`\stA` for party A.

    $`\SendA(\stA)\to((t_{I_\A},I_\A),\rho,t^\mathsf{snd}_\A,\stA')`: On input a state $`\stA` of party A, output a pair $`(t_{I_\A},I_\A)\in(\mathbb{N}\times\mathcal{I})\cup\{(\bot,\bot)\}` of epoch counter and key, a message $`\rho`, a sending epoch $`t^\mathsf{snd}_\A`, and an updated state $`\stA'`.

    $`\RecA(\stA,\rho)\to((t_{I_\B},I_\B),t^\mathsf{rcv}_\A,\stA')`: On input a state $`\stA` of party A and a message $`\rho`, output a pair $`(t_{I_\B},I_\B)\in(\mathbb{N}\times\mathcal{I})\cup\{(\bot,\bot)\}` of epoch counter and key, a receiving epoch $`t^\mathsf{rcv}_\A`, and an updated state $`\stA'`. This algorithm is deterministic.

  * *Party B*

    $`\InitB(I_{\mathsf{CKA}})\to\stB`: On input an initial key $`I_{\mathsf{CKA}}\in\mathcal{I}_{\mathsf{CKA}}`, output an initial state $`\stB` for party B.

    $`\SendB(\stB)\to((t_{I_\B},I_\B),\rho,t^\mathsf{snd}_\B,\stB')`: On input a state $`\stB` of party B, output a pair $`(t_{I_\B},I_\B)\in(\mathbb{N}\times\mathcal{I})\cup\{(\bot,\bot)\}` of epoch counter and key, a message $`\rho`, a sending epoch $`t^\mathsf{snd}_\B`, and an updated state $`\stB'`.

    $`\RecB(\stB,\rho)\to((t_{I_\A},I_\A),t^\mathsf{rcv}_\B,\stB')`: On input a state $`\stB` of party B and a message $`\rho`, output a pair $`(t_{I_\A},I_\A)\in(\mathbb{N}\times\mathcal{I})\cup\{(\bot,\bot)\}` of epoch counter and key, a receiving epoch $`t^\mathsf{rcv}_\B`, and an updated state $`\stB'`. This algorithm is deterministic.
::::
:::::

::::::

:::leanPillCaption "SCKAScheme"
:::

```anchor SCKAScheme (project := ".") (module := SecureMessaging.SCKA.Defs)
structure SCKAScheme (m : Type → Type u) [Monad m] (IK StA StB I Rho Rand : Type) where
  /-- Samples the initial common value. -/
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

::::::gameGrid
:::::gameCell "\\textsf{Illustration}" (kind := "scheme-diagram")
One possible schedule: either party may send repeatedly without waiting for a reply.

$$`\begin{array}{rcccl}
 & \textsf{Party A} & & \textsf{Party B} & \\
 & \boxed{\InitA} & \xleftarrow{\hspace{1.5em}I\hspace{1.5em}}\boxed{\Init\text{-}\KeyGen}\xrightarrow{\hspace{1.5em}I\hspace{1.5em}} & \boxed{\InitB} & \\
 & \Big\downarrow\mathrlap{\,\scriptstyle\mathsf{st}} & & \Big\downarrow\mathrlap{\,\scriptstyle\mathsf{st}} & \\
 & \boxed{\SendA} & \xrightarrow{\hspace{7em}\rho_1\hspace{7em}} & \boxed{\RecB} & \\
 & \Big\downarrow\mathrlap{\,\scriptstyle\mathsf{st}} & & \Big\downarrow\mathrlap{\,\scriptstyle\mathsf{st}} & \\
 & \boxed{\SendA} & \xrightarrow{\hspace{7em}\rho_2\hspace{7em}} & \boxed{\RecB} & \\
 & \Big\downarrow\mathrlap{\,\scriptstyle\mathsf{st}} & & \Big\downarrow\mathrlap{\,\scriptstyle\mathsf{st}} & \\
 & \boxed{\RecA} & \xleftarrow{\hspace{7em}\rho_3\hspace{7em}} & \boxed{\SendB}\mathrlap{\to(t,I_\B)} & \phantom{\to(t,I_\B)} \\
 & \Big\downarrow\mathrlap{\,\scriptstyle\mathsf{st}} & & \Big\downarrow\mathrlap{\,\scriptstyle\mathsf{st}} & \\
 & \boxed{\RecA} & \xleftarrow{\hspace{7em}\rho_4\hspace{7em}} & \boxed{\SendB} & \\
 & \Big\downarrow\mathrlap{\,\scriptstyle\mathsf{st}} & & \Big\downarrow\mathrlap{\,\scriptstyle\mathsf{st}} & \\
 \phantom{(t,I_\A)\gets} & \mathllap{(t,I_\A)\gets}\boxed{\RecA} & \xleftarrow{\hspace{7em}\rho_5\hspace{7em}} & \boxed{\SendB} & \\
 & & I_\A\overset{?}{=}I_\B & &
\end{array}`
:::::
::::::
:::::::

:::defTitle "scka_oracles" "SCKA game state and oracles"
:::

:::::::definition "scka_oracles" (parent := "cka_protocols_scka") (lean := "SCKAScheme.GameState, SCKAScheme.oracleSendA, SCKAScheme.oracleSendB, SCKAScheme.oracleSendArleak, SCKAScheme.oracleSendBrleak, SCKAScheme.oracleRecvA, SCKAScheme.oracleRecvB, SCKAScheme.oracleChall, SCKAScheme.oracleCorruptA, SCKAScheme.oracleCorruptB, SCKAScheme.sckaCorrectnessSpec, SCKAScheme.sckaCorrectnessImpl, SCKAScheme.SCKACorrectnessAdversary, SCKAScheme.sckaSecuritySpec, SCKAScheme.sckaSecurityImpl, SCKAScheme.SCKAAdversary") (uses := "scka_scheme")
Game state and oracles following {Informal.citet SCKA25}[], Figure 1.

::::::gameGrid
:::::gameCell "\\textsf{Game state}" (kind := "scheme")
The game state consists of:

- $`\stA`, $`\stB`: local protocol states for parties A and B.
- $`\mathsf{Key}[\A,t]`, $`\mathsf{Key}[\B,t]`: keys held by A and B for epoch $`t`.
- $`\mathsf{Msg}[\A,n]`, $`\mathsf{Msg}[\B,n]`: $`n`-th messages sent by A and B, with their sending epochs.
- $`n_\A`, $`n_\B`: numbers of messages sent by A and B.
- $`t^\mathsf{cur}_\A`, $`t^\mathsf{cur}_\B`: current epochs of A and B.
- $`\mathsf{Exposed}\subseteq\mathbb{N}`: epochs exposed by corruption and randomness leakage oracle calls.
- $`\mathsf{Challenged}\subseteq\mathbb{N}`: epochs $`t` for which $`\OChall(t)` has been called.
- $`\mathsf{correct}`: whether all correctness assertions have held.

:::leanPillCaption "SCKAScheme.GameState"
:::

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
:::::

:::::gameCell "\\OSendA" (kind := "compact")
$`\begin{array}{l}
\pcommentline{\text{Send from A to B}} \\
((t_{I_\A},I_\A),\rho,t^\mathsf{snd}_\A,\stA')
  \sample \SendA(\stA); \\
\pcommentline{\text{Correctness: no rollback of current epoch}} \\
\mathsf{assert}\;t^\mathsf{snd}_\A\ge t^\mathsf{cur}_\A; \\
t^\mathsf{cur}_\A\gets t^\mathsf{snd}_\A; \\
\pif\;(t_{I_\A},I_\A)\ne(\bot,\bot)\;\pthen \\
\quad\pcommentline{\text{Correctness: epoch output only once}} \\
\quad\mathsf{assert}\;\mathsf{Key}[\A,t_{I_\A}]=\bot; \\
\quad\pcommentline{\text{Correctness: keys agree when both defined}} \\
\quad\mathsf{assert}\;\mathsf{Key}[\B,t_{I_\A}]\in\{I_\A,\bot\}; \\
\quad\mathsf{Key}[\A,t_{I_\A}]\gets I_\A; \\
\pcommentline{\text{Correctness: keys known through sending epoch}} \\
\mathsf{assert}\;\forall t\in\{1,\ldots,t^\mathsf{snd}_\A\},\;
  \mathsf{Key}[\A,t]\ne\bot; \\
\pcommentline{\text{Record message for delivery}} \\
\mathsf{Msg}[\A,{+}{+}n_\A]\gets(\rho,t^\mathsf{snd}_\A); \\
\Return(t^\mathsf{snd}_\A,t_{I_\A},\rho)
\end{array}`

```anchor oracleSendA (project := ".") (module := SecureMessaging.SCKA.Defs)
def oracleSendA [DecidableEq I] (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) :
    QueryImpl (Unit →ₒ Option (ℕ × Option ℕ × Rho))
      (StateT (GameState StA StB I Rho) ProbComp) :=
  fun () => do
    let state ← get
    match ← liftM (scka.sendA state.stA) with
    | none => pure none
    | some (keyOpt, ρ, tsnd, stA') =>
      let assertMonotonicity := state.tcurA ≤ tsnd
      let assertKnownPrefix (keyA : ℕ → Option I) :=
        (List.range (tsnd + 1)).all (fun t => t = 0 || (keyA t).isSome)
      let nA' := state.nA + 1
      let msgA' := Function.update state.msgA nA' (some (ρ, tsnd))
      match keyOpt with
      | none =>
        set { state with
          stA := stA', tcurA := tsnd, msgA := msgA', nA := nA',
          correct := state.correct && assertMonotonicity && assertKnownPrefix state.keyA }
        return some (tsnd, none, ρ)
      | some (tI, key) =>
        let assertUniqueEpochs := (state.keyA tI).isNone
        let assertConsistentKeys := (state.keyB tI).isNone || state.keyB tI == some key
        let keyA' := Function.update state.keyA tI (some key)
        set { state with
          stA := stA', tcurA := tsnd, keyA := keyA', msgA := msgA', nA := nA',
          correct := state.correct
            && assertMonotonicity && assertUniqueEpochs
            && assertConsistentKeys && assertKnownPrefix keyA' }
        return some (tsnd, some tI, ρ)
```
:::::

:::::gameCell "\\OSendB" (kind := "compact")
$`\begin{array}{l}
\pcommentline{\text{Send from B to A}} \\
((t_{I_\B},I_\B),\rho,t^\mathsf{snd}_\B,\stB')
  \sample \SendB(\stB); \\
\pcommentline{\text{Correctness: no rollback of current epoch}} \\
\mathsf{assert}\;t^\mathsf{snd}_\B\ge t^\mathsf{cur}_\B; \\
t^\mathsf{cur}_\B\gets t^\mathsf{snd}_\B; \\
\pif\;(t_{I_\B},I_\B)\ne(\bot,\bot)\;\pthen \\
\quad\pcommentline{\text{Correctness: epoch output only once}} \\
\quad\mathsf{assert}\;\mathsf{Key}[\B,t_{I_\B}]=\bot; \\
\quad\pcommentline{\text{Correctness: keys agree when both defined}} \\
\quad\mathsf{assert}\;\mathsf{Key}[\A,t_{I_\B}]\in\{I_\B,\bot\}; \\
\quad\mathsf{Key}[\B,t_{I_\B}]\gets I_\B; \\
\pcommentline{\text{Correctness: keys known through sending epoch}} \\
\mathsf{assert}\;\forall t\in\{1,\ldots,t^\mathsf{snd}_\B\},\;
  \mathsf{Key}[\B,t]\ne\bot; \\
\pcommentline{\text{Record message for delivery}} \\
\mathsf{Msg}[\B,{+}{+}n_\B]\gets(\rho,t^\mathsf{snd}_\B); \\
\Return(t^\mathsf{snd}_\B,t_{I_\B},\rho)
\end{array}`

```anchor oracleSendB (project := ".") (module := SecureMessaging.SCKA.Defs)
def oracleSendB [DecidableEq I] (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) :
    QueryImpl (Unit →ₒ Option (ℕ × Option ℕ × Rho))
      (StateT (GameState StA StB I Rho) ProbComp) :=
  fun () => do
    let state ← get
    match ← liftM (scka.sendB state.stB) with
    | none => pure none
    | some (keyOpt, ρ, tsnd, stB') =>
      let assertMonotonicity := state.tcurB ≤ tsnd
      let assertKnownPrefix (keyB : ℕ → Option I) :=
        (List.range (tsnd + 1)).all (fun t => t = 0 || (keyB t).isSome)
      let nB' := state.nB + 1
      let msgB' := Function.update state.msgB nB' (some (ρ, tsnd))
      match keyOpt with
      | none =>
        set { state with
          stB := stB', tcurB := tsnd, msgB := msgB', nB := nB',
          correct := state.correct && assertMonotonicity && assertKnownPrefix state.keyB }
        return some (tsnd, none, ρ)
      | some (tI, key) =>
        let assertUniqueEpochs := (state.keyB tI).isNone
        let assertConsistentKeys := (state.keyA tI).isNone || state.keyA tI == some key
        let keyB' := Function.update state.keyB tI (some key)
        set { state with
          stB := stB', tcurB := tsnd, keyB := keyB', msgB := msgB', nB := nB',
          correct := state.correct
            && assertMonotonicity && assertUniqueEpochs
              && assertConsistentKeys && assertKnownPrefix keyB' }
        return some (tsnd, some tI, ρ)
```
:::::

:::::gameCell "\\OSendARLeak" (kind := "compact")
$`\begin{array}{l}
\pcommentline{\text{Send from A to B; reveal randomness}} \\
V\gets\mathsf{vuln}_\A(\stA); \\
((t_{I_\A},I_\A),\rho,t^\mathsf{snd}_\A,\stA',r)
  \sample \SendARLeak(\stA); \\
\pcommentline{\text{Track newly exposed epochs}} \\
V'\gets\mathsf{vuln}_\A(\stA')\setminus V; \\
\pcommentline{\text{Reject exposure of challenged epochs}} \\
\req\;V'\cap\mathsf{Challenged}=\emptyset; \\
\mathsf{Exposed}\gets\mathsf{Exposed}\cup V'; \\
\pcommentline{\text{Correctness: no rollback of current epoch}} \\
\mathsf{assert}\;t^\mathsf{snd}_\A\ge t^\mathsf{cur}_\A; \\
t^\mathsf{cur}_\A\gets t^\mathsf{snd}_\A; \\
\pif\;(t_{I_\A},I_\A)\ne(\bot,\bot)\;\pthen \\
\quad\pcommentline{\text{Correctness: epoch output only once}} \\
\quad\mathsf{assert}\;\mathsf{Key}[\A,t_{I_\A}]=\bot; \\
\quad\pcommentline{\text{Correctness: keys agree when both defined}} \\
\quad\mathsf{assert}\;\mathsf{Key}[\B,t_{I_\A}]\in\{I_\A,\bot\}; \\
\quad\mathsf{Key}[\A,t_{I_\A}]\gets I_\A; \\
\pcommentline{\text{Correctness: keys known through sending epoch}} \\
\mathsf{assert}\;\forall t\in\{1,\ldots,t^\mathsf{snd}_\A\},\;
  \mathsf{Key}[\A,t]\ne\bot; \\
\pcommentline{\text{Record message for delivery}} \\
\mathsf{Msg}[\A,{+}{+}n_\A]\gets(\rho,t^\mathsf{snd}_\A); \\
\Return(t^\mathsf{snd}_\A,t_{I_\A},\rho,r)
\end{array}`

```anchor oracleSendArleak (project := ".") (module := SecureMessaging.SCKA.Defs)
def oracleSendArleak [DecidableEq I] (vulnA : StA → Finset ℕ)
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) :
    QueryImpl (Unit →ₒ Option (ℕ × Option ℕ × Rho × Rand))
      (StateT (GameState StA StB I Rho) ProbComp) :=
  fun () => do
    let state ← get
    let vulnOld := vulnA state.stA
    match ← liftM (scka.sendArleak state.stA) with
    | none => pure none
    | some (keyOpt, ρ, tsnd, stA', rand) =>
      let vuln' := vulnA stA' \ vulnOld
      -- req vuln' ∩ Challenged = ∅
      if vuln' ∩ state.challenged ≠ ∅ then pure none
      else
        let exposed' := state.exposed ∪ vuln'
        let assertMonotonicity := state.tcurA ≤ tsnd
        let assertKnownPrefix (keyA : ℕ → Option I) :=
          (List.range (tsnd + 1)).all (fun t => t = 0 || (keyA t).isSome)
        let nA' := state.nA + 1
        let msgA' := Function.update state.msgA nA' (some (ρ, tsnd))
        match keyOpt with
        | none =>
          set { state with
            stA := stA', tcurA := tsnd, exposed := exposed',
            msgA := msgA', nA := nA',
            correct := state.correct && assertMonotonicity && assertKnownPrefix state.keyA }
          return some (tsnd, none, ρ, rand)
        | some (tI, key) =>
          let assertUniqueEpochs := (state.keyA tI).isNone
          let assertConsistentKeys := (state.keyB tI).isNone || state.keyB tI == some key
          let keyA' := Function.update state.keyA tI (some key)
          set { state with
            stA := stA', tcurA := tsnd, exposed := exposed', keyA := keyA',
            msgA := msgA', nA := nA',
            correct := state.correct
              && assertMonotonicity && assertUniqueEpochs
              && assertConsistentKeys && assertKnownPrefix keyA' }
          return some (tsnd, some tI, ρ, rand)
```
:::::

:::::gameCell "\\OSendBRLeak" (kind := "compact")
$`\begin{array}{l}
\pcommentline{\text{Send from B to A; reveal randomness}} \\
V\gets\mathsf{vuln}_\B(\stB); \\
((t_{I_\B},I_\B),\rho,t^\mathsf{snd}_\B,\stB',r)
  \sample \SendBRLeak(\stB); \\
\pcommentline{\text{Track newly exposed epochs}} \\
V'\gets\mathsf{vuln}_\B(\stB')\setminus V; \\
\pcommentline{\text{Reject exposure of challenged epochs}} \\
\req\;V'\cap\mathsf{Challenged}=\emptyset; \\
\mathsf{Exposed}\gets\mathsf{Exposed}\cup V'; \\
\pcommentline{\text{Correctness: no rollback of current epoch}} \\
\mathsf{assert}\;t^\mathsf{snd}_\B\ge t^\mathsf{cur}_\B; \\
t^\mathsf{cur}_\B\gets t^\mathsf{snd}_\B; \\
\pif\;(t_{I_\B},I_\B)\ne(\bot,\bot)\;\pthen \\
\quad\pcommentline{\text{Correctness: epoch output only once}} \\
\quad\mathsf{assert}\;\mathsf{Key}[\B,t_{I_\B}]=\bot; \\
\quad\pcommentline{\text{Correctness: keys agree when both defined}} \\
\quad\mathsf{assert}\;\mathsf{Key}[\A,t_{I_\B}]\in\{I_\B,\bot\}; \\
\quad\mathsf{Key}[\B,t_{I_\B}]\gets I_\B; \\
\pcommentline{\text{Correctness: keys known through sending epoch}} \\
\mathsf{assert}\;\forall t\in\{1,\ldots,t^\mathsf{snd}_\B\},\;
  \mathsf{Key}[\B,t]\ne\bot; \\
\pcommentline{\text{Record message for delivery}} \\
\mathsf{Msg}[\B,{+}{+}n_\B]\gets(\rho,t^\mathsf{snd}_\B); \\
\Return(t^\mathsf{snd}_\B,t_{I_\B},\rho,r)
\end{array}`

```anchor oracleSendBrleak (project := ".") (module := SecureMessaging.SCKA.Defs)
def oracleSendBrleak [DecidableEq I] (vulnB : StB → Finset ℕ)
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) :
    QueryImpl (Unit →ₒ Option (ℕ × Option ℕ × Rho × Rand))
      (StateT (GameState StA StB I Rho) ProbComp) :=
  fun () => do
    let state ← get
    let vulnOld := vulnB state.stB
    match ← liftM (scka.sendBrleak state.stB) with
    | none => pure none
    | some (keyOpt, ρ, tsnd, stB', rand) =>
      let vuln' := vulnB stB' \ vulnOld
      if vuln' ∩ state.challenged ≠ ∅ then pure none
      else
        let exposed' := state.exposed ∪ vuln'
        let assertMonotonicity := state.tcurB ≤ tsnd
        let assertKnownPrefix (keyB : ℕ → Option I) :=
          (List.range (tsnd + 1)).all (fun t => t = 0 || (keyB t).isSome)
        let nB' := state.nB + 1
        let msgB' := Function.update state.msgB nB' (some (ρ, tsnd))
        match keyOpt with
        | none =>
          set { state with
            stB := stB', tcurB := tsnd, exposed := exposed',
            msgB := msgB', nB := nB',
            correct := state.correct && assertMonotonicity && assertKnownPrefix state.keyB }
          return some (tsnd, none, ρ, rand)
        | some (tI, key) =>
          let assertUniqueEpochs := (state.keyB tI).isNone
          let assertConsistentKeys := (state.keyA tI).isNone || state.keyA tI == some key
          let keyB' := Function.update state.keyB tI (some key)
          set { state with
            stB := stB', tcurB := tsnd, exposed := exposed', keyB := keyB',
            msgB := msgB', nB := nB',
            correct := state.correct
              && assertMonotonicity && assertUniqueEpochs
              && assertConsistentKeys && assertKnownPrefix keyB' }
          return some (tsnd, some tI, ρ, rand)
```
:::::

:::::gameCell "\\ORecA(n)" (kind := "compact")
$`\begin{array}{l}
\pcommentline{\text{Deliver B's message n to A}} \\
\req\;\mathsf{Msg}[\B,n]\ne\bot; \\
(\rho,t^\mathsf{snd}_\B)\gets\mathsf{Msg}[\B,n]; \\
r\getsval\RecA(\stA,\rho); \\
\pcommentline{\text{Correctness: honest delivery succeeds}} \\
\pif\;r=\bot\;\pthen\;
  \mathsf{correct}\gets\mathsf{false};\;\Return\bot; \\
((t_{I_\B},I_\B),t^\mathsf{rcv}_\A,\stA')\gets r; \\
\pcommentline{\text{Correctness: receive epoch matches sender}} \\
\mathsf{assert}\;t^\mathsf{rcv}_\A=t^\mathsf{snd}_\B; \\
t^\mathsf{cur}_\A\gets
  \max(t^\mathsf{cur}_\A,t^\mathsf{rcv}_\A); \\
\pif\;(t_{I_\B},I_\B)\ne(\bot,\bot)\;\pthen \\
\quad\pcommentline{\text{Correctness: epoch output only once}} \\
\quad\mathsf{assert}\;\mathsf{Key}[\A,t_{I_\B}]=\bot; \\
\quad\pcommentline{\text{Correctness: keys agree when both defined}} \\
\quad\mathsf{assert}\;\mathsf{Key}[\B,t_{I_\B}]\in\{I_\B,\bot\}; \\
\quad\mathsf{Key}[\A,t_{I_\B}]\gets I_\B; \\
\pcommentline{\text{Correctness: keys known through current epoch}} \\
\mathsf{assert}\;\forall t\in\{1,\ldots,t^\mathsf{cur}_\A\},\;
  \mathsf{Key}[\A,t]\ne\bot; \\
\Return(t^\mathsf{rcv}_\A,t_{I_\B})
\end{array}`

```anchor oracleRecvA (project := ".") (module := SecureMessaging.SCKA.Defs)
def oracleRecvA [DecidableEq I] (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) :
    QueryImpl (ℕ →ₒ Option (ℕ × Option ℕ))
      (StateT (GameState StA StB I Rho) ProbComp) :=
  fun (n : ℕ) => do
    let state ← get
    -- req Msg[B, n] ≠ ⊥
    match state.msgB n with
    | none => pure none
    | some (ρ, tsndB) =>
      match scka.recvA state.stA ρ with
      | none =>
        -- honest delivery should succeed; failure is a correctness violation.
        set { state with correct := false }
        return none
      | some (keyOpt, trcv, stA') =>
        let tcurA' := max state.tcurA trcv
        let assertMatchingEpoch := trcv == tsndB
        let assertKnownPrefix (keyA : ℕ → Option I) :=
          (List.range (tcurA' + 1)).all (fun t => t = 0 || (keyA t).isSome)
        match keyOpt with
        | none =>
          set { state with
            stA := stA', tcurA := tcurA',
            correct := state.correct && assertMatchingEpoch && assertKnownPrefix state.keyA }
          return some (trcv, none)
        | some (tI, key) =>
          let assertUniqueEpochs := (state.keyA tI).isNone
          let assertConsistentKeys := (state.keyB tI).isNone || state.keyB tI == some key
          let keyA' := Function.update state.keyA tI (some key)
          set { state with
            stA := stA', tcurA := tcurA', keyA := keyA',
            correct := state.correct
              && assertMatchingEpoch && assertUniqueEpochs
              && assertConsistentKeys && assertKnownPrefix keyA' }
          return some (trcv, some tI)
```
:::::

:::::gameCell "\\ORecB(n)" (kind := "compact")
$`\begin{array}{l}
\pcommentline{\text{Deliver A's message n to B}} \\
\req\;\mathsf{Msg}[\A,n]\ne\bot; \\
(\rho,t^\mathsf{snd}_\A)\gets\mathsf{Msg}[\A,n]; \\
r\getsval\RecB(\stB,\rho); \\
\pcommentline{\text{Correctness: honest delivery succeeds}} \\
\pif\;r=\bot\;\pthen\;
  \mathsf{correct}\gets\mathsf{false};\;\Return\bot; \\
((t_{I_\A},I_\A),t^\mathsf{rcv}_\B,\stB')\gets r; \\
\pcommentline{\text{Correctness: receive epoch matches sender}} \\
\mathsf{assert}\;t^\mathsf{rcv}_\B=t^\mathsf{snd}_\A; \\
t^\mathsf{cur}_\B\gets
  \max(t^\mathsf{cur}_\B,t^\mathsf{rcv}_\B); \\
\pif\;(t_{I_\A},I_\A)\ne(\bot,\bot)\;\pthen \\
\quad\pcommentline{\text{Correctness: epoch output only once}} \\
\quad\mathsf{assert}\;\mathsf{Key}[\B,t_{I_\A}]=\bot; \\
\quad\pcommentline{\text{Correctness: keys agree when both defined}} \\
\quad\mathsf{assert}\;\mathsf{Key}[\A,t_{I_\A}]\in\{I_\A,\bot\}; \\
\quad\mathsf{Key}[\B,t_{I_\A}]\gets I_\A; \\
\pcommentline{\text{Correctness: keys known through current epoch}} \\
\mathsf{assert}\;\forall t\in\{1,\ldots,t^\mathsf{cur}_\B\},\;
  \mathsf{Key}[\B,t]\ne\bot; \\
\Return(t^\mathsf{rcv}_\B,t_{I_\A})
\end{array}`

```anchor oracleRecvB (project := ".") (module := SecureMessaging.SCKA.Defs)
def oracleRecvB [DecidableEq I] (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) :
    QueryImpl (ℕ →ₒ Option (ℕ × Option ℕ))
      (StateT (GameState StA StB I Rho) ProbComp) :=
  fun (n : ℕ) => do
    let state ← get
    match state.msgA n with
    | none => pure none
    | some (ρ, tsndA) =>
      match scka.recvB state.stB ρ with
      | none =>
        set { state with correct := false }
        return none
      | some (keyOpt, trcv, stB') =>
        let tcurB' := max state.tcurB trcv
        let assertMatchingEpoch := trcv == tsndA
        let assertKnownPrefix (keyB : ℕ → Option I) :=
          (List.range (tcurB' + 1)).all (fun t => t = 0 || (keyB t).isSome)
        match keyOpt with
        | none =>
          set { state with
            stB := stB', tcurB := tcurB',
            correct := state.correct && assertMatchingEpoch && assertKnownPrefix state.keyB }
          return some (trcv, none)
        | some (tI, key) =>
          let assertUniqueEpochs := (state.keyB tI).isNone
          let assertConsistentKeys := (state.keyA tI).isNone || state.keyA tI == some key
          let keyB' := Function.update state.keyB tI (some key)
          set { state with
            stB := stB', tcurB := tcurB', keyB := keyB',
            correct := state.correct
              && assertMatchingEpoch && assertUniqueEpochs
              && assertConsistentKeys && assertKnownPrefix keyB' }
          return some (trcv, some tI)
```
:::::

:::::gameCell "\\OChall(t)" (kind := "challenge")
$`\begin{array}{l}
\pcommentline{\text{Return a real or random epoch key}} \\
\pcommentline{\text{Reject exposed or previously challenged epochs}} \\
\req\;t\notin\mathsf{Exposed}\cup\mathsf{Challenged}; \\
\pcommentline{\text{Use either party's derived key}} \\
\pif\;\mathsf{Key}[\A,t]\ne\bot\;\pthen \\
\quad K\gets\mathsf{Key}[\A,t]; \\
\pelse \\
\quad K\gets\mathsf{Key}[\B,t]; \\
\pcommentline{\text{A party must have derived the key}} \\
\req\;K\ne\bot; \\
\pcommentline{\text{Replace the key in the random case}} \\
\pif\;b=1\;\pthen\;K\sample I; \\
\pcommentline{\text{Record this epoch to prevent another challenge}} \\
\mathsf{Challenged}\gets\mathsf{Challenged}\cup\{t\}; \\
\Return K
\end{array}`

```anchor oracleChall (project := ".") (module := SecureMessaging.SCKA.Defs)
def oracleChall (isRandom : Bool) (StA StB I Rho : Type) [SampleableType I] :
    QueryImpl (ℕ →ₒ Option I) (StateT (GameState StA StB I Rho) ProbComp) :=
  fun (t : ℕ) => do
    let state ← get
    -- req t ∉ Exposed ∪ Challenged
    if t ∈ state.exposed ∨ t ∈ state.challenged then pure none
    else
      let key? := match state.keyA t with
        | some k => some k
        | none => state.keyB t
      match key? with
      | none => pure none -- req K ≠ ⊥
      | some k =>
        let outK ← if isRandom then liftM ($ᵗ I : ProbComp I) else pure k
        set { state with challenged := insert t state.challenged }
        return some outK
```
:::::

:::::gameCell "\\OCorrA" (kind := "compact")
$`\begin{array}{l}
\pcommentline{\text{Reveal A's local state}} \\
V\gets\mathsf{vuln}_\A(\stA); \\
\pcommentline{\text{Reject exposure of challenged epochs}} \\
\req\;V\cap\mathsf{Challenged}=\emptyset; \\
\pcommentline{\text{Record exposed epochs}} \\
\mathsf{Exposed}\gets\mathsf{Exposed}\cup V; \\
\Return\stA
\end{array}`

```anchor oracleCorruptA (project := ".") (module := SecureMessaging.SCKA.Defs)
def oracleCorruptA (vulnA : StA → Finset ℕ) (StB I Rho : Type) :
    QueryImpl (Unit →ₒ Option StA) (StateT (GameState StA StB I Rho) ProbComp) :=
  fun () => do
    let state ← get
    let vuln := vulnA state.stA
    if vuln ∩ state.challenged ≠ ∅ then pure none
    else
      set { state with exposed := state.exposed ∪ vuln }
      return some state.stA
```
:::::

:::::gameCell "\\OCorrB" (kind := "compact")
$`\begin{array}{l}
\pcommentline{\text{Reveal B's local state}} \\
V\gets\mathsf{vuln}_\B(\stB); \\
\pcommentline{\text{Reject exposure of challenged epochs}} \\
\req\;V\cap\mathsf{Challenged}=\emptyset; \\
\pcommentline{\text{Record exposed epochs}} \\
\mathsf{Exposed}\gets\mathsf{Exposed}\cup V; \\
\Return\stB
\end{array}`

```anchor oracleCorruptB (project := ".") (module := SecureMessaging.SCKA.Defs)
def oracleCorruptB (vulnB : StB → Finset ℕ) (StA I Rho : Type) :
    QueryImpl (Unit →ₒ Option StB) (StateT (GameState StA StB I Rho) ProbComp) :=
  fun () => do
    let state ← get
    let vuln := vulnB state.stB
    if vuln ∩ state.challenged ≠ ∅ then pure none
    else
      set { state with exposed := state.exposed ∪ vuln }
      return some state.stB
```
:::::

:::::gameCell "\\textsf{Oracle sets for correctness and security}" (kind := "scheme")
$$`\Ocor=\{\mathsf{O\text{-}Unif},\OSendA,\OSendB,
\ORecA(n),\ORecB(n)\}`

$`\begin{array}{ll}
\mathsf{O\text{-}Unif} & \text{Sample uniform randomness.} \\
\OSendA & \text{Trigger A to send a message to B.} \\
\OSendB & \text{Trigger B to send a message to A.} \\
\ORecA(n) & \text{Deliver B's recorded message }n\text{ to A.} \\
\ORecB(n) & \text{Deliver A's recorded message }n\text{ to B.}
\end{array}`
:::leanPillCaption "Correctness oracle interface"
:::

```anchor sckaCorrectnessSpec (project := ".") (module := SecureMessaging.SCKA.Defs)
def sckaCorrectnessSpec (Rho : Type) :=
  unifSpec                                  -- Uniform randomness
  + (Unit →ₒ Option (ℕ × Option ℕ × Rho))       -- O-Send-A
  + (Unit →ₒ Option (ℕ × Option ℕ × Rho))       -- O-Send-B
  + (ℕ →ₒ Option (ℕ × Option ℕ))                -- O-Recv-A
  + (ℕ →ₒ Option (ℕ × Option ℕ))                -- O-Recv-B
```

:::leanPillCaption "Correctness oracle implementation"
:::

```anchor sckaCorrectnessImpl (project := ".") (module := SecureMessaging.SCKA.Defs)
def sckaCorrectnessImpl [DecidableEq I] (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) :
    QueryImpl (sckaCorrectnessSpec Rho)
      (StateT (GameState StA StB I Rho) ProbComp) :=
  oracleUnif StA StB I Rho
    + oracleSendA scka + oracleSendB scka
    + oracleRecvA scka + oracleRecvB scka
```

:::leanPillCaption "Correctness adversary"
:::

```anchor SCKACorrectnessAdversary (project := ".") (module := SecureMessaging.SCKA.Defs)
abbrev SCKACorrectnessAdversary (Rho : Type) :=
  OracleComp (sckaCorrectnessSpec Rho) Bool
```

$$`\Osec=\Ocor\cup
\{\OSendARLeak,\OSendBRLeak,\OChall(t),\OCorrA,\OCorrB\}`

In addition to $`\Ocor`:

$`\begin{array}{ll}
\OSendARLeak & \text{Trigger A to send and reveal the randomness used.} \\
\OSendBRLeak & \text{Trigger B to send and reveal the randomness used.} \\
\OChall(t) & \text{Real or random key challenge for epoch }t\text{.} \\
\OCorrA & \text{Reveal A's current local state.} \\
\OCorrB & \text{Reveal B's current local state.}
\end{array}`

:::leanPillCaption "Security oracle interface"
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

:::leanPillCaption "Security oracle implementation"
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

:::leanPillCaption "Security adversary"
:::

```anchor SCKAAdversary (project := ".") (module := SecureMessaging.SCKA.Defs)
abbrev SCKAAdversary (StA StB I Rho Rand : Type) :=
  OracleComp (sckaSecuritySpec StA StB I Rho Rand) Bool
```

:::::

:::::gameCell "\\textsf{Illustration: adversarial scheduling}" (kind := "scheme")
:::sckaAdversaryIllustration
:::
:::::
::::::
:::::::

:::defTitle "scka_correctness" "SCKA protocol correctness"
:::

:::::::definition "scka_correctness" (parent := "cka_protocols_scka") (lean := "SCKAScheme.correctnessExp") (tags := "gh-184") (uses := "scka_scheme, scka_oracles")

::::::gameGrid
:::::gameCell "\\Exp{\\textsf{cor}}{\\textsf{SCKA}}(\\adv)" (kind := "game")
$`\begin{array}{l}
\pcommentline{\text{Check correctness under adversarial scheduling}} \\
\pcommentline{\text{Initialize both parties with a shared key}} \\
ik\sample\mathsf{InitKeyGen}(); \\
\stA\sample\InitA(ik);\quad\stB\sample\InitB(ik); \\
\pcommentline{\text{Initialize the game records}} \\
\mathsf{Key}[P,t]\gets\bot;\quad\mathsf{Msg}[P,n]\gets\bot; \\
n_\A,n_\B,t^\mathsf{cur}_\A,t^\mathsf{cur}_\B\gets0; \\
\mathsf{Exposed},\mathsf{Challenged}\gets\emptyset;\quad
  \mathsf{correct}\gets\mathsf{true}; \\
\pcommentline{\text{Let the adversary schedule sends and deliveries}} \\
(\_,\mathsf{state})\getsval\adv^{\Ocor}; \\
\pcommentline{\text{Accept iff all correctness conditions held}} \\
\Return\mathsf{state.correct}
\end{array}`
:::leanPillCaption "Correctness experiment"
:::

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
:::::
::::::
:::::::

:::defTitle "scka_security" "SCKA protocol security"
:::

:::::::definition "scka_security" (parent := "cka_protocols_scka") (lean := "SCKAScheme.securityExp, SCKAScheme.sckaGuessAdvantage") (tags := "gh-185") (uses := "scka_scheme, scka_oracles")

::::::gameGrid
:::::gameCell "\\Exp{\\textsf{sec}}{\\textsf{SCKA}}(\\adv)" (kind := "game")
$`\begin{array}{l}
\pcommentline{\text{Distinguish real epoch keys from random keys}} \\
\pcommentline{\text{Initialize both parties with a shared key}} \\
ik\sample\mathsf{InitKeyGen}(); \\
\stA\sample\InitA(ik);\quad\stB\sample\InitB(ik); \\
\pcommentline{\text{Initialize the game records}} \\
\mathsf{Key}[P,t]\gets\bot;\quad\mathsf{Msg}[P,n]\gets\bot; \\
n_\A,n_\B,t^\mathsf{cur}_\A,t^\mathsf{cur}_\B\gets0; \\
\mathsf{Exposed},\mathsf{Challenged}\gets\emptyset;\quad
  \mathsf{correct}\gets\mathsf{true}; \\
\pcommentline{b=0:\text{ real keys; }b=1:\text{ random keys}} \\
b\sample\{0,1\}; \\
\pcommentline{\text{Run the adversary with the security oracles}} \\
(b',\_)\getsval\adv^{\Osec}; \\
\pcommentline{\text{Accept iff the adversary guesses the hidden bit}} \\
\Return[b'=b]
\end{array}`
:::leanPillCaption "Security experiment"
:::

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

$$`\mathsf{Adv}^{\mathsf{guess}}_{\mathsf{SCKA}}(\adv)
  =\left|\Pr\left[\Exp{\mathsf{sec}}{\mathsf{SCKA}}(\adv)=1\right]
    -\frac12\right|
  =\left|\Pr[b'=b]-\frac12\right|`

:::leanPillCaption "Guessing advantage"
:::

```anchor sckaGuessAdvantage (project := ".") (module := SecureMessaging.SCKA.Defs)
noncomputable def sckaGuessAdvantage [SampleableType I] [DecidableEq I]
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (adversary : SCKAAdversary StA StB I Rho Rand)
    (vulnA : StA → Finset ℕ) (vulnB : StB → Finset ℕ) : ℝ :=
  |(Pr[= true | securityExp scka adversary vulnA vulnB]).toReal - 1 / 2|
```
:::::
::::::
:::::::
