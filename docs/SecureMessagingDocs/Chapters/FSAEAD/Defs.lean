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

:::group "fs_aead"
Forward-Secure AEAD (FS-AEAD).
:::

:::defTitle "fs_aead_scheme" "FS-AEAD scheme"
:::

::::definition "fs_aead_scheme" (parent := "fs_aead") (lean := "FSAEADScheme") (tags := "gh-186")
Adapted from {Informal.citet ACD19}[], Definition 14.

An FS-AEAD scheme is a tuple of algorithms
$`(\mathsf{FS\text{-}Init\text{-}S}, \mathsf{FS\text{-}Init\text{-}R}, \mathsf{FS\text{-}Send}, \mathsf{FS\text{-}Rcv})`,
where

- $`\mathsf{FS\text{-}Init\text{-}S}` takes a key $`k` and outputs the sender's state
  $`v_\A \gets \mathsf{FS\text{-}Init\text{-}S}(k)`,
- $`\mathsf{FS\text{-}Init\text{-}R}` takes a key $`k` and outputs the receiver's state
  $`v_\B \gets \mathsf{FS\text{-}Init\text{-}R}(k)`,
- $`\mathsf{FS\text{-}Send}` takes a state $`v`, associated data $`a` and a message $`m`,
  and produces a new state and a ciphertext $`(v', e) \gets \mathsf{FS\text{-}Send}(v, a, m)`,
- $`\mathsf{FS\text{-}Rcv}` takes a state $`v`, associated data $`a` and a ciphertext
  $`e`, and produces a new state, an index and a message
  $`(v', i, m) \gets \mathsf{FS\text{-}Rcv}(v, a, e)`,
  $`\boxed{\text{or } \bot \text{ if it rejects } e}.`

All algorithms are deterministic.

```anchor FSAEADScheme (project := ".") (module := SecureMessaging.FSAEAD.Defs)
structure FSAEADScheme (K StS StR AD M C : Type) where
  /-- `FS-Init-S`: the sender's initial state. -/
  initS : K → StS
  /-- `FS-Init-R`: the receiver's initial state. -/
  initR : K → StR
  /-- `FS-Send(v, a, m) = (v', e)`. -/
  send : StS → AD → M → StS × C
  /-- `FS-Rcv(v, a, e) = (v', i, m)`, or `none` if `e` is rejected. -/
  rcv : StR → AD → C → Option (StR × ℕ × M)
```
::::

:::defTitle "fs_aead_security" "FS-AEAD security"
:::

:::::::definition "fs_aead_security" (parent := "fs_aead") (lean := "FSAEADScheme.GameState, FSAEADScheme.securityExp, FSAEADScheme.fsaeadSecurityImpl, FSAEADScheme.advantage") (tags := "gh-187") (uses := "fs_aead_scheme")
Adapted from {Informal.citet ACD19}[], Figure 5 and Definition 15.

::::::gameGrid
:::::gameCell "\\textsf{Game state and notation}" (kind := "scheme-notation")
The game state consists of:

::::table -header
*
  *
    * $`v_\A`, $`v_\B`: the states of A and B.
    * $`i_\A`: the number of messages A has sent.
    * $`\mathsf{corrA}`: whether A has been corrupted.
    * $`\mathsf{win}`: whether the adversary reached a winning condition.
    * $`\mathsf{end}`: whether the game has ended.
  *
    * $`\mathsf{trans}`: the records $`(i, a, m, e)` of ciphertexts in transit (sent by A
      for indices $`i` not yet received by B).
    * $`\mathsf{chall} \subseteq \mathbb N`: the indices of challenge ciphertexts in
      $`\mathsf{trans}`.
    * $`\mathsf{comp} \subseteq \mathbb N`: indices exposed by A's corruption and not yet
      received by B: those in $`\mathsf{trans}` sent while A was corrupted,
      $`\boxed{\textit{\small and indices that A has not sent yet, once A is corrupted}}.`
::::

In the oracles, $`\req\varphi` means: if $`\varphi` is false, the oracle returns
$`\bot` and the game state does not change. $`\mathsf{end}` disables all oracles: after
it, every oracle returns $`\bot`.

:::leanPillCaption "Game state"
:::

```anchor GameState (project := ".") (module := SecureMessaging.FSAEAD.Defs)
structure GameState (StS StR AD M C : Type) where
  /-- Sender state `v_A`. -/
  vA : StS
  /-- Receiver state `v_B`. -/
  vB : StR
  /-- Number of messages sent so far, `i_A`. -/
  iA : ℕ
  /-- Whether A has been corrupted. -/
  corrA : Bool
  /-- Set by `O-Corr-B`, after which every oracle except the uniform-randomness oracle
  returns `none`. -/
  end_ : Bool
  /-- Whether the adversary reached a winning condition. -/
  win : Bool
  /-- Ciphertexts in transit, as records `(i, a, m, e)`. -/
  trans : List (ℕ × AD × M × C)
  /-- Indices of challenge ciphertexts in transit. -/
  chall : Finset ℕ
  /-- Indices exposed by A's corruption and not yet received by B. -/
  comp : ℕ → Bool
```
:::::

:::::gameCell "\\textsf{Corrections}" (kind := "scheme-notation")
A sends its $`i`-th message at index $`i`, so the indices $`i > i_\A` are the ones A has
not used yet. Once the adversary corrupts A at counter $`i_\A^c`, it knows A's state. It
can then compute the ciphertext that A would send at an index $`i > i_\A^c` and inject it
before A sends it, and B must accept it. In {Informal.citet ACD19}[], Figure 5, this
counts as a forgery, because $`\mathsf{comp}` only holds indices that A has already sent,
so every correct scheme loses. We make two corrections for this case, marked by boxes in
pseudocode:

- $`\OCorrA` adds every index $`i > i_\A^c` to $`\mathsf{comp}`, so injecting at these
  indices does not count as a forgery, and $`\mathsf{record}` no longer adds to
  $`\mathsf{comp}`;
- when A later sends at an index $`i_\A > i_\A^c`, $`\mathsf{record}` does nothing if
  $`\mathsf{corrA}` holds and $`i_\A \notin \mathsf{comp}`, i.e. when an earlier injection
  already consumed $`i_\A`.
:::::
::::::

:::leanPillCaption "specification for oracle types"
:::

```anchor fsaeadSpec (project := ".") (module := SecureMessaging.FSAEAD.Defs)
abbrev fsaeadSpec (StS StR AD M C : Type) :=
  unifSpec
    + (AD × M →ₒ Option C)
    + (AD × M × M →ₒ Option C)
    + (Unit →ₒ Option StS)
    + (Unit →ₒ Option (StS × StR))
    + (AD × C →ₒ Option (ℕ × Option M))
    + (AD × C →ₒ Option (ℕ × M))
```

::::::gameGrid
:::::gameCell "\\OTransmitA(a, m)" (kind := "compact")
$`\begin{array}{l}
i_\A{+}{+}; \\
(v_\A, e) \gets \mathsf{FS\text{-}Send}(v_\A, a, m); \\
\mathsf{record}(\mathsf{good}, a, m, e); \\
\Return e
\end{array}`

```anchor oracleTransmitA (project := ".") (module := SecureMessaging.FSAEAD.Defs)
def oracleTransmitA (fs : FSAEADScheme K StS StR AD M C) :
    QueryImpl (AD × M →ₒ Option C) (GameM StS StR AD M C) :=
  fun (a, m) => do
    let st ← get
    if st.end_ then return none
    let (vA, e) := fs.send st.vA a m
    set ({ st with vA, iA := st.iA + 1 }.record false a m e)
    return some e
```
:::::

:::::gameCell "\\ODeliverB(a, e)" (kind := "compact")
$`\begin{array}{l}
\req\;(i, a, m, e) \in \mathsf{trans}\text{, with the smallest such } i; \\
r \gets \mathsf{FS\text{-}Rcv}(v_\B, a, e); \\
\pcommentline{\text{correctness failure: B rejects the honest ciphertext } e} \\
\pif\;r = \bot\;\pthen \\
\quad\mathsf{win} \gets \mathsf{true}; \\
\quad\Return \bot; \\
(v_\B, i', m') \gets r; \\
\pcommentline{\text{correctness failure: B outputs a wrong index or message}} \\
\pif\;(i', m') \neq (i, m)\;\pthen \\
\quad\mathsf{win} \gets \mathsf{true}; \\
\pif\;i \in \mathsf{chall}\;\pthen \\
\quad m' \gets \bot; \\
\mathsf{delete}(i); \\
\Return (i', m')
\end{array}`

```anchor oracleDeliverB (project := ".") (module := SecureMessaging.FSAEAD.Defs)
def oracleDeliverB [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (fs : FSAEADScheme K StS StR AD M C) :
    QueryImpl (AD × C →ₒ Option (ℕ × Option M)) (GameM StS StR AD M C) :=
  fun (a, e) => do
    let st ← get
    if st.end_ then return none
    let some (i, _, m, _) := st.findTrans a e | return none
    match fs.rcv st.vB a e with
    | none =>
      set { st with win := true }
      return none
    | some (vB, i', m') =>
      let win := st.win || !(decide (i' = i) && decide (m' = m))
      set ({ st with vB, win }.delete i)
      return some (i', if i ∈ st.chall then none else some m')
```
:::::

:::::gameCell "\\OChallA(a, m_0, m_1)" (kind := "compact")
$`\begin{array}{l}
\req\;\neg\mathsf{corrA} \wedge |m_0| = |m_1|; \\
i_\A{+}{+}; \\
(v_\A, e) \gets \mathsf{FS\text{-}Send}(v_\A, a, m_b); \\
\mathsf{record}(\mathsf{chall}, a, m_b, e); \\
\Return e
\end{array}`

```anchor oracleChallA (project := ".") (module := SecureMessaging.FSAEAD.Defs)
def oracleChallA (fs : FSAEADScheme K StS StR AD M C) (len : M → ℕ) (b : Bool) :
    QueryImpl (AD × M × M →ₒ Option C) (GameM StS StR AD M C) :=
  fun (a, m₀, m₁) => do
    let st ← get
    if st.end_ || st.corrA || len m₀ ≠ len m₁ then return none
    let m := if b then m₁ else m₀
    let (vA, e) := fs.send st.vA a m
    set ({ st with vA, iA := st.iA + 1 }.record true a m e)
    return some e
```
:::::

:::::gameCell "\\OInjectB(a, e)" (kind := "compact")
$`\begin{array}{l}
\req\;\neg(\exists i, m: (i, a, m, e) \in \mathsf{trans}); \\
r \gets \mathsf{FS\text{-}Rcv}(v_\B, a, e); \\
\req\;r \neq \bot; \\
(v_\B, i', m') \gets r; \\
\pcommentline{\text{authenticity failure: B accepts a forgery at an index that is not compromised}} \\
\pif\;i' \notin \mathsf{comp}\;\pthen \\
\quad\mathsf{win} \gets \mathsf{true}; \\
\mathsf{delete}(i'); \\
\Return (i', m')
\end{array}`

```anchor oracleInjectB (project := ".") (module := SecureMessaging.FSAEAD.Defs)
def oracleInjectB [DecidableEq AD] [DecidableEq C]
    (fs : FSAEADScheme K StS StR AD M C) :
    QueryImpl (AD × C →ₒ Option (ℕ × M)) (GameM StS StR AD M C) :=
  fun (a, e) => do
    let st ← get
    if st.end_ || (st.findTrans a e).isSome then return none
    let some (vB, i', m') := fs.rcv st.vB a e | return none
    let win := st.win || !st.comp i'
    set ({ st with vB, win }.delete i')
    return some (i', m')
```
:::::

:::::gameCell "\\OCorrA" (kind := "compact")
$`\begin{array}{l}
\boxed{\kern-5pt\begin{array}{l}
\pif\;\neg\mathsf{corrA}\;\pthen \\
\quad\mathsf{comp} \gets \{i \mid i > i_\A\};
\end{array}\kern-5pt} \\
\mathsf{corrA} \gets \mathsf{true}; \\
\Return v_\A
\end{array}`

```anchor oracleCorrA (project := ".") (module := SecureMessaging.FSAEAD.Defs)
def oracleCorrA (StS StR AD M C : Type) :
    QueryImpl (Unit →ₒ Option StS) (GameM StS StR AD M C) :=
  fun () => do
    let st ← get
    if st.end_ then return none
    let comp := if st.corrA then st.comp else fun i => decide (st.iA < i)
    set { st with corrA := true, comp }
    return some st.vA
```
:::::

:::::gameCell "\\OCorrB" (kind := "compact")
$`\begin{array}{l}
\req\;\mathsf{chall} = \emptyset; \\
\mathsf{end} \gets \mathsf{true}; \\
\Return (v_\A, v_\B)
\end{array}`

```anchor oracleCorrB (project := ".") (module := SecureMessaging.FSAEAD.Defs)
def oracleCorrB (StS StR AD M C : Type) :
    QueryImpl (Unit →ₒ Option (StS × StR)) (GameM StS StR AD M C) :=
  fun () => do
    let st ← get
    if st.end_ || st.chall ≠ ∅ then return none
    set { st with end_ := true }
    return some (st.vA, st.vB)
```
:::::

:::::gameCell "\\mathsf{record}(\\mathit{flag}, a, m, e)" (kind := "compact")
$`\begin{array}{l}
\boxed{\kern-5pt\begin{array}{l}
\pif\;\mathsf{corrA} \wedge i_\A \notin \mathsf{comp}\;\pthen \\
\quad\Return;
\end{array}\kern-5pt} \\
\mathsf{trans} \gets \mathsf{trans} \cup \{(i_\A, a, m, e)\}; \\
\pif\;\mathit{flag} = \mathsf{chall}\;\pthen \\
\quad\mathsf{chall} \gets \mathsf{chall} \cup \{i_\A\}
\end{array}`

```anchor gameStateRecord (project := ".") (module := SecureMessaging.FSAEAD.Defs)
def record (st : GameState StS StR AD M C) (isChall : Bool) (a : AD) (m : M) (e : C) :
    GameState StS StR AD M C :=
  if st.corrA && !st.comp st.iA then st else
  { st with
    trans := st.trans ++ [(st.iA, a, m, e)]
    chall := if isChall then insert st.iA st.chall else st.chall }
```
:::::

:::::gameCell "\\mathsf{delete}(i)" (kind := "compact")
$`\begin{array}{l}
\mathsf{trans} \gets \mathsf{trans} \setminus \{(i, \cdot, \cdot, \cdot)\}; \\
\mathsf{chall} \gets \mathsf{chall} \setminus \{i\}; \\
\mathsf{comp} \gets \mathsf{comp} \setminus \{i\}
\end{array}`

```anchor gameStateDelete (project := ".") (module := SecureMessaging.FSAEAD.Defs)
def delete (st : GameState StS StR AD M C) (i : ℕ) : GameState StS StR AD M C :=
  { st with
    trans := st.trans.filter (·.1 ≠ i)
    chall := st.chall.erase i
    comp := fun j => j != i && st.comp j }
```
:::::
::::::

::::::gameGrid
:::::gameCell "\\textsf{Example run of this game}" (kind := "scheme")
Each oracle call has a solid arrow for the adversary's query and a dashed arrow for the
oracle's reply. An X marks a query that the game refuses; the reply is then $`\bot`.
Black arrows carry the states of A and B. The adversary holds $`e_1` and delivers the
challenge $`e_2` first. A rejected forgery ($`e^*`) returns $`\bot` and
leaves message 1 in $`\mathsf{trans}`. Corrupting A at $`i_\A = 2` sets
$`\mathsf{comp} = \{i \mid i > 2\}`, so injecting $`e_3` for index 3 before A sends it
does not set $`\mathsf{win}`.

:::fsaeadAdversaryIllustration
:::
:::::
::::::

::::::gameGrid
:::::gameCell "\\Exp{\\textsf{fs-aead}}{\\textsf{FS-AEAD}}(\\adv)" (kind := "game")
$`\begin{array}{l}
\pcommentline{\text{Initialize both parties with a shared key}} \\
k \sample \mathcal K;\quad v_\A \gets \mathsf{FS\text{-}Init\text{-}S}(k);\quad v_\B \gets \mathsf{FS\text{-}Init\text{-}R}(k); \\
\pcommentline{\text{Initialize the game state}} \\
i_\A \gets 0;\quad \mathsf{corrA} \gets \mathsf{false};\quad \mathsf{win} \gets \mathsf{false};\quad \mathsf{end} \gets \mathsf{false}; \\
\mathsf{trans}, \mathsf{chall}, \mathsf{comp} \gets \emptyset; \\
\pcommentline{\text{Sample the challenge bit and run the adversary}} \\
b \sample \bit;\quad b' \gets \adv^{\O}; \\
\pcommentline{\text{Win by a winning condition or by guessing } b} \\
\Return(\mathsf{win} \vee b'=b)
\end{array}`

:::leanPillCaption "Initial game state"
:::

```anchor gameStateInit (project := ".") (module := SecureMessaging.FSAEAD.Defs)
def init (fs : FSAEADScheme K StS StR AD M C) (k : K) : GameState StS StR AD M C where
  vA := fs.initS k
  vB := fs.initR k
  iA := 0
  corrA := false
  end_ := false
  win := false
  trans := []
  chall := ∅
  comp := fun _ => false
```

:::leanPillCaption "Security experiment"
:::

```anchor securityExp (project := ".") (module := SecureMessaging.FSAEAD.Defs)
def securityExp [SampleableType K] [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (fs : FSAEADScheme K StS StR AD M C) (len : M → ℕ)
    (adversary : FSAEADAdversary StS StR AD M C) : ProbComp Bool := do
  let k ← $ᵗ K
  let b ← $ᵗ Bool
  let (b', st) ← (simulateQ (fsaeadSecurityImpl fs len b) adversary).run (.init fs k)
  return st.win || b == b'
```
:::::
::::::

The advantage of $`\adv` is

$$`\mathsf{Adv}^{\textsf{fs-aead}}_{\textsf{FS-AEAD}}(\adv)
  = \Bigl|\, \Pr\bigl[\Exp{\textsf{fs-aead}}{\textsf{FS-AEAD}}(\adv) = 1\bigr] - \tfrac{1}{2} \,\Bigr|`

```anchor advantage (project := ".") (module := SecureMessaging.FSAEAD.Defs)
noncomputable def advantage [SampleableType K] [DecidableEq AD] [DecidableEq M]
    [DecidableEq C] (fs : FSAEADScheme K StS StR AD M C) (len : M → ℕ)
    (adversary : FSAEADAdversary StS StR AD M C) : ℝ :=
  |(Pr{let x ← securityExp fs len adversary}[x = true]).toReal - 1 / 2|
```
:::::::
