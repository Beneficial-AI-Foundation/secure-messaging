import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Visuals.FSAEADKeyChain
import SecureMessaging.FSAEAD.FromAEADPRG.Construction
import SecureMessaging.FSAEAD.FromAEADPRG.Correctness

/-! # Blueprint chapter: FS-AEAD from AEAD and PRG -/

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

#doc (Manual) "FS-AEAD from AEAD and PRG" =>

*References:*

- {Informal.citet ACD19}[] — the construction (§4.2.2, Figure 6).

:::group "fs_aead_fs_aead_from_aead_prg"
FS-AEAD from AEAD and PRG.
:::

:::defTitle "fs_aead_from_aead_prg_spec" "FS-AEAD from AEAD and PRG construction"
:::

::::::::definition "fs_aead_from_aead_prg_spec" (parent := "fs_aead_fs_aead_from_aead_prg") (lean := "FSAEADScheme.fromAEADPRG, FSAEADScheme.FromAEADPRG.SendState, FSAEADScheme.FromAEADPRG.RecvState, FSAEADScheme.FromAEADPRG.initS, FSAEADScheme.FromAEADPRG.initR, FSAEADScheme.FromAEADPRG.send, FSAEADScheme.FromAEADPRG.rcv, FSAEADScheme.FromAEADPRG.trySkipped, FSAEADScheme.FromAEADPRG.skip, FSAEADScheme.FromAEADPRG.skipSteps") (tags := "gh-31") (uses := "fs_aead_scheme, aead, prg")
Adapted from {Informal.citet ACD19}[], §4.2.2, Figure 6.

Let $`\mathsf{AE} = (\mathsf{KeyGen}, \Enc, \Dec)` be an {bpref "aead"}[AEAD] scheme with key space
$`\K`. Let $`\W` be a set, and let
$`G : \W \to \W \times \K` be a {bpref "prg"}[PRG] with seed space
$`\mathcal S = \W` and output space $`\mathcal R = \W \times \K`. The {bpref "fs_aead_scheme"}[FS-AEAD scheme] below has key space
$`\W`. The construction does not call $`\mathsf{KeyGen}`, because $`G` derives the
keys. The state of each party consists of the variables set by its initialisation. When
$`\mathsf{FS\text{-}Rcv}` raises $`\mathsf{error}`, B's state goes back to what it was before
the call.

:::::::gameGrid
::::::gameCell "\\mathsf{Init}\\text{-}\\A(k)" (kind := "compact")
$`\begin{array}{l}
w \gets k;\quad i_\A \gets 0; \\
v_\A \gets (w, i_\A); \\
\Return v_\A
\end{array}`

:::leanPillCaption "A's state"
:::

```anchor SendState (project := ".") (module := SecureMessaging.FSAEAD.FromAEADPRG.Construction)
structure SendState (W : Type) where
  /-- `w_A`: current seed. -/
  w : W
  /-- `i_A`: number of messages sent. -/
  iA : ℕ
```

:::leanPillCaption "A's initial state"
:::

```anchor initS (project := ".") (module := SecureMessaging.FSAEAD.FromAEADPRG.Construction)
def initS (k : W) : SendState W := { w := k, iA := 0 }
```

::::::

::::::gameCell "\\mathsf{Init}\\text{-}\\B(k)" (kind := "compact")
$`\begin{array}{l}
w \gets k;\quad i_\B \gets 0;\quad D[\cdot] \gets \bot; \\
v_\B \gets (w, i_\B, D); \\
\Return v_\B
\end{array}`

:::leanPillCaption "B's state"
:::

```anchor RecvState (project := ".") (module := SecureMessaging.FSAEAD.FromAEADPRG.Construction)
structure RecvState (W Kae : Type) where
  /-- `w_B`: current seed. -/
  w : W
  /-- `i_B`: B's position in the chain, so `w_B = w_{i_B}`. It is 0 initially. -/
  iB : ℕ
  /-- `D`: keys of the skipped indices that B has not received, with `none` for `⊥`. -/
  D : ℕ → Option Kae
```

:::leanPillCaption "B's initial state"
:::

```anchor initR (project := ".") (module := SecureMessaging.FSAEAD.FromAEADPRG.Construction)
def initR (k : W) : RecvState W Kae := { w := k, iB := 0, D := fun _ => none }
```

::::::
:::::::

:::leanPillCaption "The FS-AEAD scheme"
:::

```anchor fromAEADPRG (project := ".") (module := SecureMessaging.FSAEAD.FromAEADPRG.Construction)
def fromAEADPRG (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae)) :
    FSAEADScheme W (SendState W) (RecvState W Kae) AD M (ℕ × Cae) where
  initS := FromAEADPRG.initS
  initR := FromAEADPRG.initR
  send := FromAEADPRG.send ae prg
  rcv := FromAEADPRG.rcv ae prg
```

:::::::gameGrid
::::::gameCell "\\mathsf{FS\\text{-}Send}(a, m)" (kind := "compact")
$`\begin{array}{l}
i_\A{+}{+}; \\
(w, K) \gets G(w); \\
h \gets (i_\A, a); \\
e \gets \Enc(K, h, m); \\
\Return (i_\A, e)
\end{array}`

```anchor send (project := ".") (module := SecureMessaging.FSAEAD.FromAEADPRG.Construction)
def send (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae))
    (st : SendState W) (a : AD) (m : M) : SendState W × (ℕ × Cae) :=
  let iA := st.iA + 1
  let (w, K) := prg.gen st.w
  ({ w, iA }, (iA, ae.encrypt K (iA, a) m))
```
::::::

::::::gameCell "\\mathsf{FS\\text{-}Rcv}(a, c)" (kind := "compact")
$`\begin{array}{l}
(i, e) \gets c; \\
K \gets \mathsf{try\text{-}skipped}(i); \\
\pif\;K = \bot\;\pthen \\
\quad\boxed{\pif\;i \le i_\B\;\pthen\;\mathsf{error};} \\
\quad\mathsf{skip}(i); \\
\quad(w, K) \gets G(w); \\
\quad i_\B \gets i; \\
h \gets (i, a); \\
m \gets \Dec(K, h, e); \\
\pif\;m = \bot\;\pthen\;\mathsf{error}; \\
\Return (i, m)
\end{array}`

```anchor rcv (project := ".") (module := SecureMessaging.FSAEAD.FromAEADPRG.Construction)
def rcv (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae) (prg : PRGScheme W (W × Kae))
    (st : RecvState W Kae) (a : AD) (c : ℕ × Cae) : Option (RecvState W Kae × ℕ × M) := do
  let (i, e) := c
  let (K?, st) := trySkipped st i
  let (st, K) ← match K? with
    | some K => some (st, K)
    | none => do
      if i ≤ st.iB then none
      let st := skip prg i st
      let (w, K) := prg.gen st.w
      some ({ st with w, iB := i }, K)
  let m ← ae.decrypt K (i, a) e
  return (st, i, m)
```
::::::

::::::gameCell "\\mathsf{try\\text{-}skipped}(i)" (kind := "compact")
$`\begin{array}{l}
K \gets D[i]; \\
D[i] \gets \bot; \\
\Return K
\end{array}`

```anchor trySkipped (project := ".") (module := SecureMessaging.FSAEAD.FromAEADPRG.Construction)
def trySkipped (st : RecvState W Kae) (i : ℕ) : Option Kae × RecvState W Kae :=
  (st.D i, { st with D := Function.update st.D i none })
```
::::::

::::::gameCell "\\mathsf{skip}(u)" (kind := "compact")
$`\begin{array}{l}
\mathsf{while}\;i_\B < u - 1: \\
\quad i_\B{+}{+}; \\
\quad(w, K) \gets G(w); \\
\quad\boxed{D[i_\B] \gets K}
\end{array}`

```anchor skip (project := ".") (module := SecureMessaging.FSAEAD.FromAEADPRG.Construction)
def skip (prg : PRGScheme W (W × Kae)) (u : ℕ) (st : RecvState W Kae) : RecvState W Kae :=
  skipSteps prg (u - 1 - st.iB) st
```

```anchor skipSteps (project := ".") (module := SecureMessaging.FSAEAD.FromAEADPRG.Construction)
def skipSteps (prg : PRGScheme W (W × Kae)) : ℕ → RecvState W Kae → RecvState W Kae
  | 0, st => st
  | n + 1, st =>
    let iB := st.iB + 1
    let (w, K) := prg.gen st.w
    skipSteps prg n { w, iB, D := Function.update st.D iB (some K) }
```
::::::
:::::::

:::::::gameGrid
::::::gameCell "\\textsf{Deviations}" (kind := "scheme-notation")
We change {Informal.citet ACD19}[], Figure 6, in three places. Boxes in pseudocode mark the
first two:

1. $`\mathsf{skip}` stores each skipped key at its own index, $`D[i_\B] \gets K`. Figure 6
   stores all of them at $`D[u]`, so each one overwrites the one before.
2. When $`\mathsf{try\text{-}skipped}(i)` returns $`\bot`, $`\mathsf{FS\text{-}Rcv}` rejects
   $`i \le i_\B`. Figure 6 instead decrypts $`e` under the key of index $`i_\B + 1` and sets
   $`i_\B \gets i`.
3. $`\mathsf{Init}\text{-}\B` sets $`D[\cdot] \gets \bot`. Figure 6 writes $`\lambda` there,
   but $`\mathsf{try\text{-}skipped}` and $`\mathsf{FS\text{-}Rcv}` test for $`\bot`.
::::::
:::::::
::::::::

:::::::gameGrid
::::::gameCell "\\textsf{Illustration: the key chain}" (kind := "scheme")
:::fsAeadKeyChainIllustration
:::

A and B derive the same chain from $`w_0 = k`: $`(w_j, K_j) \gets G(w_{j-1})`. A sends its
$`j`-th message as $`(j, e_j)`, with $`e_j` encrypted under $`K_j`. Here message 3 arrives
first, so B runs $`\mathsf{skip}(3)` and keeps $`K_1` and $`K_2` in $`D` for messages 1 and 2.
::::::
:::::::

:::defTitle "fs_aead_from_aead_prg_correctness" "FS-AEAD from AEAD and PRG correctness"
:::

::::theorem "fs_aead_from_aead_prg_correctness" (parent := "fs_aead_fs_aead_from_aead_prg") (lean := "FSAEADScheme.fromAEADPRG_noFirstDeliverWin, FSAEADScheme.FromAEADPRG.sendAll_eq, FSAEADScheme.FromAEADPRG.rcvAll_honest_initR") (tags := "gh-29") (uses := "fs_aead_from_aead_prg_spec, fs_aead_scheme, fs_aead_delivery_correctness, aead_correctness, prg")
Adapted from {Informal.citet ACD19}[], proof of Theorem 5 (step from $`H_1` to $`H_2`).

Let $`\mathsf{AE}` be a correct AEAD scheme and $`G` a PRG. Then:
1. The FS-AEAD scheme from $`\mathsf{AE}` and $`G` is
   {bpref "fs_aead_delivery_correctness"}[delivery-correct].
2. Let B start from $`\mathsf{Init\text{-}B}(k)` and receive ciphertexts
   $`(j, \Enc(K_j, (j, a), m))` with associated data $`a`, for distinct indices
   $`j \geq 1`, in any order. Then B outputs $`(j, m)` for each of them. A's $`j`-th
   ciphertext from $`\mathsf{Init\text{-}A}(k)` has this form.

The proof follows the states of A and B along the chain from $`k`. While
$`\mathsf{win}` is false, B keeps the key of every ciphertext in transit: its index is
above $`i_B`, or its key is in $`D`. After $`\OCorrA`, an injection that consumes an index
before A sends it removes that index from $`\mathsf{comp}`, so $`\mathsf{record}` does not
add A's later ciphertext at that index.

:::leanPillCaption "delivery correctness"
:::

```anchor fromAEADPRG_noFirstDeliverWin (project := ".") (module := SecureMessaging.FSAEAD.FromAEADPRG.Correctness)
theorem fromAEADPRG_noFirstDeliverWin {Cae AD M : Type} [DecidableEq AD] [DecidableEq M]
    [DecidableEq Cae] (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (prg : PRGScheme W (W × Kae)) (hae : ae.Correct) (len : M → ℕ) :
    (fromAEADPRG ae prg).NoFirstDeliverWin len
```

:::leanPillCaption "honest delivery in any order"
:::

```anchor rcvAll_honest_initR (project := ".") (module := SecureMessaging.FSAEAD.FromAEADPRG.Correctness)
theorem rcvAll_honest_initR (ae : AEADScheme ProbComp M (ℕ × AD) Kae Cae)
    (prg : PRGScheme W (W × Kae)) (hae : ae.Correct) (k : W) (del : List (ℕ × AD × M))
    (hnd : (del.map (·.1)).Nodup) (hpos : ∀ x ∈ del, 1 ≤ x.1) :
    (rcvAll ae prg (initR k) (del.map fun x =>
      (x.2.1, (x.1, ae.encrypt (chainKey prg k x.1) (x.1, x.2.1) x.2.2)))).1 =
      del.map fun x => some (x.1, x.2.2)
```
::::

:::defTitle "fs_aead_from_aead_prg_security" "FS-AEAD from AEAD and PRG security"
:::

::::theorem "fs_aead_from_aead_prg_security" (parent := "fs_aead_fs_aead_from_aead_prg") (tags := "gh-32") (uses := "fs_aead_from_aead_prg_spec, fs_aead_scheme, fs_aead_security, aead_security_exp, prg")
$`\todo`

:::leanPill "missing"
:::
::::
