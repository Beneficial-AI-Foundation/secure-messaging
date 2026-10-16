import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Visuals.FSAEADAdversary
import SecureMessaging.FSAEAD.Defs

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

#doc (Manual) "Forward-Secure AEAD Definitions" =>

*References:*

- {Informal.citet ACD19}[] — FS-AEAD syntax (Definition 14), security game (Figure 5)
  and security (Definition 15).

The memory-management functions $`\mathsf{FS\text{-}Stop}` and $`\mathsf{FS\text{-}Max}`
of ACD19 §4.2.1 are left out, as ACD19 gives them no formal requirement.

:::group "fs_aead"
Forward-Secure AEAD (FS-AEAD).
:::

:::defTitle "fs_aead_scheme" "FS-AEAD scheme"
:::

::::definition "fs_aead_scheme" (parent := "fs_aead") (lean := "FSAEADScheme") (tags := "gh-186")
{Informal.citet ACD19}[], Definition 14. An FS-AEAD scheme is a tuple of algorithms
$`(\mathsf{FS\text{-}Init\text{-}S}, \mathsf{FS\text{-}Init\text{-}R}, \mathsf{FS\text{-}Send}, \mathsf{FS\text{-}Rcv})`,
where

- $`\mathsf{FS\text{-}Init\text{-}S}` (and similarly $`\mathsf{FS\text{-}Init\text{-}R}`)
  takes a key $`k` and outputs a state $`v_A \gets \mathsf{FS\text{-}Init\text{-}S}(k)`,
- $`\mathsf{FS\text{-}Send}` takes a state $`v`, associated data $`a` and a message $`m`,
  and produces a new state and a ciphertext $`(v', e) \gets \mathsf{FS\text{-}Send}(v, a, m)`,
- $`\mathsf{FS\text{-}Rcv}` takes a state $`v`, associated data $`a` and a ciphertext
  $`e`, and produces a new state, an index and a message
  $`(v', i, m) \gets \mathsf{FS\text{-}Rcv}(v, a, e)`.

All algorithms are deterministic.

Deviation (D1): Definition 14 does not say what $`\mathsf{FS\text{-}Rcv}` returns on
rejection. Here a rejecting $`\mathsf{FS\text{-}Rcv}` returns no state and no index, so
the receiver keeps its old state.

```anchor FSAEADScheme (project := ".") (module := SecureMessaging.FSAEAD.Defs)
structure FSAEADScheme (K SS SR AD M C : Type) where
  /-- `FS-Init-S`: the sender's initial state. -/
  initS : K → SS
  /-- `FS-Init-R`: the receiver's initial state. -/
  initR : K → SR
  /-- `FS-Send(v, a, m) = (v', e)`. -/
  send : SS → AD → M → SS × C
  /-- `FS-Rcv(v, a, e) = (v', i, m)`, or `none` if `e` is rejected.
  Deviation (D1): a rejection produces no new state and no index. -/
  rcv : SR → AD → C → Option (SR × ℕ × M)
```
::::

:::defTitle "fs_aead_security" "FS-AEAD security"
:::

:::::::definition "fs_aead_security" (parent := "fs_aead") (lean := "FSAEADScheme.GameState, FSAEADScheme.GameState.isCompromised, FSAEADScheme.securityExp, FSAEADScheme.fsaeadSecurityImpl, FSAEADScheme.advantage") (tags := "gh-187") (uses := "fs_aead_scheme")
Adapted from {Informal.citet ACD19}[], Figure 5 and Definition 15.

ACD19 Figure 5 is changed in five places. D2 and D4 fix errors. Each change is marked
in the boxes below and in the source:

- (D1) A rejecting $`\mathsf{FS\text{-}Rcv}` returns no state and no index.
- (D2) A rejected $`\mathsf{inject\text{-}B}` deletes no record.
- (D3) A rejected $`\mathsf{deliver\text{-}B}` is a win but leaves the records alone.
- (D4) Once A is corrupted, indices A has not sent yet also count as compromised. If an
  injection consumes such an index, A's later ciphertext for it is not recorded.
  Otherwise B would have to accept both, and no correct scheme meets the game.
- (D5) The advantage is half that of ACD19 §2.1.

::::::gameGrid
:::::gameCell "\\textsf{Game state}" (kind := "scheme-notation")
The game state consists of:

::::table -header
*
  *
    * $`v_\A`, $`v_\B`: the states of A and B.
    * $`i_\A`: the number of messages A has sent.
    * $`\mathsf{corrA}`: whether A has been corrupted.
    * $`\mathsf{won}`: whether a $`\mathsf{win}` instruction was reached.
    * $`\mathsf{ended}`: whether $`\mathsf{end}` was reached.
  *
    * $`\mathsf{trans}`: the records $`(i, a, m, e)` of ciphertexts in transit.
    * $`\mathsf{chall} \subseteq \mathbb N`: the indices of challenge ciphertexts in
      transit.
    * $`\mathsf{comp} \subseteq \mathbb N`: the indices of ciphertexts in transit that A
      sent while corrupted.
    * $`\mathsf{preempted} \subseteq \mathbb N`: (D4) the indices that an injection
      consumed before A sent them.
::::

An index $`i` is compromised if

$$`\mathsf{compromised}(i) :\Leftrightarrow i \in \mathsf{comp} \;\vee\; \boxed{\mathsf{corrA} \wedge i > i_\A \wedge i \notin \mathsf{preempted}}`

where the boxed part is (D4).

:::leanPillCaption "Game state"
:::

```anchor GameState (project := ".") (module := SecureMessaging.FSAEAD.Defs)
structure GameState (SS SR AD M C : Type) where
  /-- Sender state `v_A`. -/
  vA : SS
  /-- Receiver state `v_B`. -/
  vB : SR
  /-- Number of messages sent so far, `i_A`. -/
  iA : ℕ
  /-- Whether A has been corrupted. -/
  corrA : Bool
  /-- Set by `corr-B`, after which every oracle except the uniform-randomness oracle
  returns `none`. -/
  ended : Bool
  /-- Set when a `win` instruction is reached. -/
  won : Bool
  /-- Ciphertexts in transit, as records `(i, a, m, e)`. -/
  trans : List (ℕ × AD × M × C)
  /-- Indices of challenge ciphertexts in transit. -/
  chall : Finset ℕ
  /-- Indices of ciphertexts in transit that A sent while corrupted. -/
  comp : Finset ℕ
  /-- Indices that an injection consumed before A sent them.
  Deviation (D4): not in Figure 5. -/
  preempted : Finset ℕ
```

:::leanPillCaption "Compromised indices"
:::

```anchor gameStateIsCompromised (project := ".") (module := SecureMessaging.FSAEAD.Defs)
def isCompromised (st : GameState SS SR AD M C) (i : ℕ) : Bool :=
  i ∈ st.comp || (st.corrA && st.iA < i && i ∉ st.preempted)
```
:::::
::::::

:::leanPillCaption "specification for oracle types"
:::

```anchor fsaeadSpec (project := ".") (module := SecureMessaging.FSAEAD.Defs)
abbrev fsaeadSpec (SS SR AD M C : Type) :=
  unifSpec
    + (AD × M →ₒ Option C)
    + (AD × M × M →ₒ Option C)
    + (Unit →ₒ Option SS)
    + (Unit →ₒ Option (SS × SR))
    + (AD × C →ₒ Option (ℕ × Option M))
    + (AD × C →ₒ Option (ℕ × M))
```

::::::gameGrid
:::::gameCell "\\mathsf{transmit\\text{-}A}(a, m)" (kind := "compact")
$`\begin{array}{l}
i_\A{+}{+}; \\
(v_\A, e) \gets \mathsf{FS\text{-}Send}(v_\A, a, m); \\
\mathsf{record}(\mathsf{good}, a, m, e); \\
\Return e
\end{array}`

```anchor oracleTransmitA (project := ".") (module := SecureMessaging.FSAEAD.Defs)
def oracleTransmitA (fs : FSAEADScheme K SS SR AD M C) :
    QueryImpl (AD × M →ₒ Option C) (GameM SS SR AD M C) :=
  fun (a, m) => do
    let st ← get
    if st.ended then return none
    let (vA, e) := fs.send st.vA a m
    set ({ st with vA, iA := st.iA + 1 }.record false a m e)
    return some e
```
:::::

:::::gameCell "\\mathsf{deliver\\text{-}B}(a, e)" (kind := "compact")
$`\begin{array}{l}
\req (i, a, m, e) \in \mathsf{trans}\ \text{for some}\ i, m\ \text{(the first such record)}; \\
\pcommentline{\text{(D3) Figure 5 also runs }\mathsf{delete}(i)} \\
\pif\;\mathsf{FS\text{-}Rcv}(v_\B, a, e)\ \text{rejects}\;\pthen\;\mathsf{win}; \Return \bot; \\
(v_\B, i', m') \gets \mathsf{FS\text{-}Rcv}(v_\B, a, e); \\
\pif\;(i', m') \neq (i, m)\;\pthen\;\mathsf{win}; \\
\pif\;i \in \mathsf{chall}\;\pthen\;m' \gets \bot; \\
\mathsf{delete}(i); \\
\Return (i', m')
\end{array}`

```anchor oracleDeliverB (project := ".") (module := SecureMessaging.FSAEAD.Defs)
def oracleDeliverB [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (fs : FSAEADScheme K SS SR AD M C) :
    QueryImpl (AD × C →ₒ Option (ℕ × Option M)) (GameM SS SR AD M C) :=
  fun (a, e) => do
    let st ← get
    if st.ended then return none
    let some (i, _, m, _) := st.findTrans a e | return none
    match fs.rcv st.vB a e with
    | none =>
      set { st with won := true }
      return none
    | some (vB, i', m') =>
      let won := st.won || !(decide (i' = i) && decide (m' = m))
      set ({ st with vB, won }.delete i)
      return some (i', if i ∈ st.chall then none else some m')
```
:::::

:::::gameCell "\\mathsf{chall\\text{-}A}(a, m_0, m_1)" (kind := "compact")
$`\begin{array}{l}
\req \neg\mathsf{corrA} \wedge |m_0| = |m_1|; \\
i_\A{+}{+}; \\
(v_\A, e) \gets \mathsf{FS\text{-}Send}(v_\A, a, m_b); \\
\mathsf{record}(\mathsf{chall}, a, m_b, e); \\
\Return e
\end{array}`

```anchor oracleChallA (project := ".") (module := SecureMessaging.FSAEAD.Defs)
def oracleChallA (fs : FSAEADScheme K SS SR AD M C) (len : M → ℕ) (b : Bool) :
    QueryImpl (AD × M × M →ₒ Option C) (GameM SS SR AD M C) :=
  fun (a, m₀, m₁) => do
    let st ← get
    if st.ended || st.corrA || len m₀ ≠ len m₁ then return none
    let m := if b then m₁ else m₀
    let (vA, e) := fs.send st.vA a m
    set ({ st with vA, iA := st.iA + 1 }.record true a m e)
    return some e
```
:::::

:::::gameCell "\\mathsf{inject\\text{-}B}(a, e)" (kind := "compact")
$`\begin{array}{l}
\req (a, e) \notin \mathsf{trans}; \\
\pcommentline{\text{(D2) Figure 5 runs }\mathsf{delete}(i')} \\
\pif\;\mathsf{FS\text{-}Rcv}(v_\B, a, e)\ \text{rejects}\;\pthen\;\Return \bot; \\
(v_\B, i', m') \gets \mathsf{FS\text{-}Rcv}(v_\B, a, e); \\
\pcommentline{\text{(D4) Figure 5 has }i' \notin \mathsf{comp}} \\
\pif\;\neg\mathsf{compromised}(i')\;\pthen\;\mathsf{win}; \\
\mathsf{delete}(i'); \\
\Return (i', m')
\end{array}`

```anchor oracleInjectB (project := ".") (module := SecureMessaging.FSAEAD.Defs)
def oracleInjectB [DecidableEq AD] [DecidableEq C] (fs : FSAEADScheme K SS SR AD M C) :
    QueryImpl (AD × C →ₒ Option (ℕ × M)) (GameM SS SR AD M C) :=
  fun (a, e) => do
    let st ← get
    if st.ended || (st.findTrans a e).isSome then return none
    let some (vB, i', m') := fs.rcv st.vB a e | return none
    let won := st.won || !st.isCompromised i'
    set ({ st with vB, won }.delete i')
    return some (i', m')
```
:::::

:::::gameCell "\\mathsf{corr\\text{-}A}" (kind := "compact")
$`\begin{array}{l}
\mathsf{corrA} \gets \mathsf{true}; \\
\Return v_\A
\end{array}`

```anchor oracleCorrA (project := ".") (module := SecureMessaging.FSAEAD.Defs)
def oracleCorrA (SS SR AD M C : Type) :
    QueryImpl (Unit →ₒ Option SS) (GameM SS SR AD M C) :=
  fun () => do
    let st ← get
    if st.ended then return none
    set { st with corrA := true }
    return some st.vA
```
:::::

:::::gameCell "\\mathsf{corr\\text{-}B}" (kind := "compact")
$`\begin{array}{l}
\req \mathsf{chall} = \emptyset; \\
\mathsf{end}; \\
\Return (v_\A, v_\B)
\end{array}`

```anchor oracleCorrB (project := ".") (module := SecureMessaging.FSAEAD.Defs)
def oracleCorrB (SS SR AD M C : Type) :
    QueryImpl (Unit →ₒ Option (SS × SR)) (GameM SS SR AD M C) :=
  fun () => do
    let st ← get
    if st.ended || st.chall ≠ ∅ then return none
    set { st with ended := true }
    return some (st.vA, st.vB)
```
:::::

:::::gameCell "\\mathsf{record}(\\mathit{flag}, a, m, e)" (kind := "compact")
$`\begin{array}{l}
\pcommentline{\text{(D4) not in Figure 5}} \\
\pif\;i_\A \in \mathsf{preempted}\;\pthen\;\Return; \\
\mathsf{trans} \gets \mathsf{trans} \cup \{(i_\A, a, m, e)\}; \\
\pif\;\mathsf{corrA}\;\pthen\;\mathsf{comp} \gets \mathsf{comp} \cup \{i_\A\}; \\
\pif\;\mathit{flag} = \mathsf{chall}\;\pthen\;\mathsf{chall} \gets \mathsf{chall} \cup \{i_\A\}
\end{array}`

```anchor gameStateRecord (project := ".") (module := SecureMessaging.FSAEAD.Defs)
def record (st : GameState SS SR AD M C) (isChall : Bool) (a : AD) (m : M) (e : C) :
    GameState SS SR AD M C :=
  if st.iA ∈ st.preempted then st else
  { st with
    trans := st.trans ++ [(st.iA, a, m, e)]
    chall := if isChall then insert st.iA st.chall else st.chall
    comp := if st.corrA then insert st.iA st.comp else st.comp }
```
:::::

:::::gameCell "\\mathsf{delete}(i)" (kind := "compact")
$`\begin{array}{l}
\mathsf{trans} \gets \mathsf{trans} \setminus \{(i, \cdot, \cdot, \cdot)\}; \\
\mathsf{chall}, \mathsf{comp} \gets \mathsf{chall} \setminus \{i\}, \mathsf{comp} \setminus \{i\}; \\
\pcommentline{\text{(D4) not in Figure 5}} \\
\pif\;i > i_\A\;\pthen\;\mathsf{preempted} \gets \mathsf{preempted} \cup \{i\}
\end{array}`

```anchor gameStateDelete (project := ".") (module := SecureMessaging.FSAEAD.Defs)
def delete (st : GameState SS SR AD M C) (i : ℕ) : GameState SS SR AD M C :=
  { st with
    trans := st.trans.filter (·.1 ≠ i)
    chall := st.chall.erase i
    comp := st.comp.erase i
    preempted := if st.iA < i then insert i st.preempted else st.preempted }
```
:::::
::::::

::::::gameGrid
:::::gameCell "\\textsf{Example run: when a forgery counts as a win}" (kind := "scheme")
Whether the adversary wins depends on what is still in transit and on when A was
corrupted. In this run, a rejected forgery leaves the honest message 1 in transit (D2).
After $`\mathsf{corr\text{-}A}` at $`i_\A = 2`, A cannot send a challenge, and a forgery
for index 3, which A has not sent yet, is accepted without a win (D4).

Black arrows are honest ciphertexts. Red arrows are under the adversary's control. An X
marks a call that the game refuses.

:::fsaeadAdversaryIllustration
:::
:::::
::::::

::::::gameGrid
:::::gameCell "\\Exp{\\textsf{fs-aead}}{\\textsf{FS-AEAD}}(\\adv)" (kind := "game")
$`\begin{array}{l}
\pcommentline{\text{Initialize both parties with a shared key}} \\
k \sample \mathcal K;\quad v_\A \gets \mathsf{FS\text{-}Init\text{-}S}(k);\quad v_\B \gets \mathsf{FS\text{-}Init\text{-}R}(k); \\
\pcommentline{\text{Initialize the game records}} \\
i_\A \gets 0; \\
\mathsf{corrA} \gets \mathsf{false}; \\
\mathsf{trans}, \mathsf{chall}, \mathsf{comp} \gets \emptyset; \\
\pcommentline{\text{(D4) not in Figure 5}} \\
\mathsf{preempted} \gets \emptyset; \\
\pcommentline{\text{Not in Figure 5: they encode }\mathsf{win}\text{ and }\mathsf{end}} \\
\mathsf{won}, \mathsf{ended} \gets \mathsf{false}; \\
\pcommentline{\text{Sample the challenge bit and run the adversary}} \\
b \sample \bit;\quad b' \gets \adv^{\O}; \\
\pcommentline{\text{Win by a win instruction or by guessing } b} \\
\Return(\mathsf{won} \vee b'=b)
\end{array}`

:::leanPillCaption "Initial game state"
:::

```anchor gameStateInit (project := ".") (module := SecureMessaging.FSAEAD.Defs)
def init (fs : FSAEADScheme K SS SR AD M C) (k : K) : GameState SS SR AD M C where
  vA := fs.initS k
  vB := fs.initR k
  iA := 0
  corrA := false
  ended := false
  won := false
  trans := []
  chall := ∅
  comp := ∅
  preempted := ∅
```

:::leanPillCaption "Security experiment"
:::

```anchor securityExp (project := ".") (module := SecureMessaging.FSAEAD.Defs)
def securityExp [SampleableType K] [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (fs : FSAEADScheme K SS SR AD M C) (len : M → ℕ)
    (adversary : FSAEADAdversary SS SR AD M C) : ProbComp Bool := do
  let k ← $ᵗ K
  let b ← $ᵗ Bool
  let (b', st) ← (simulateQ (fsaeadSecurityImpl fs len b) adversary).run (.init fs k)
  return st.won || b == b'
```
:::::
::::::

The advantage of $`\adv` is

$$`\mathsf{Adv}^{\textsf{fs-aead}}_{\textsf{FS-AEAD}}(\adv)
  = \Bigl|\, \Pr\bigl[\Exp{\textsf{fs-aead}}{\textsf{FS-AEAD}}(\adv) = 1\bigr] - \tfrac{1}{2} \,\Bigr|`

```anchor advantage (project := ".") (module := SecureMessaging.FSAEAD.Defs)
noncomputable def advantage [SampleableType K] [DecidableEq AD] [DecidableEq M]
    [DecidableEq C] (fs : FSAEADScheme K SS SR AD M C) (len : M → ℕ)
    (adversary : FSAEADAdversary SS SR AD M C) : ℝ :=
  |(Pr[= true | securityExp fs len adversary]).toReal - 1 / 2|
```
:::::::
