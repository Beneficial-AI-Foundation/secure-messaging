import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessaging.FSAEAD.FromAEADPRG.Construction

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

Let $`\mathsf{AE} = (\Enc, \Dec)` be an {bpref "aead"}[AEAD] scheme with key space
$`\mathcal K`, whose associated data are pairs $`h = (i, a)` of an index $`i` and the
associated data $`a` of the FS-AEAD scheme. Let $`\mathcal W` be a set of seeds, and let
$`G : \mathcal W \to \mathcal W \times \mathcal K` be a {bpref "prg"}[PRG]: from a seed, it
outputs a new seed and an AEAD key. The construction is an
{bpref "fs_aead_scheme"}[FS-AEAD scheme] with key space $`\mathcal W`.

A and B share a key $`k \in \mathcal W`. Starting from $`k`, both apply $`G` again and again,
so they derive the same sequence of seeds and keys, the chain:

$$`w_0 = k, \qquad (w_j, K_j) \gets G(w_{j-1}) \text{ for } j \ge 1.`

Each step overwrites the seed. From its current seed, a party can compute the later keys.
Let $`k` be uniform and $`G` a secure PRG. Then, over a bounded number of steps, the
earlier keys look uniform to a party that knows only a later seed. To send its $`i`-th message $`m` with
associated data $`a`, A encrypts $`m` under $`K_i` with the AEAD associated data
$`(i, a)`, and sends $`i` with the ciphertext. B keeps its
position $`i_\B` in the chain, its current seed $`w_{i_\B}`, and a dictionary $`D`
of the keys of the indices that it skipped and has not received yet. The construction does
not use the key generation of $`\mathsf{AE}`, because $`G` derives the keys.

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
::::::gameCell "\\textsf{Changes to Figure 6}" (kind := "scheme-notation")
Corrections, marked by boxes in the pseudocode:

- $`\mathsf{skip}` stores each skipped key at its own index, $`D[i_\B] \gets K`. Figure 6
  stores all of them at $`D[u]`, so each one overwrites the one before.
- $`\mathsf{FS\text{-}Rcv}` rejects an index $`i \le i_\B` that is not in $`D`. Figure 6
  derives the next chain key for it instead.

Ambiguity resolved: Figure 6 initialises $`D[\cdot] \gets \lambda`, but
$`\mathsf{try\text{-}skipped}` and $`\mathsf{FS\text{-}Rcv}` use $`\bot` for an empty
entry. We write $`\bot` for both.

Rollback: when $`\mathsf{FS\text{-}Rcv}` raises $`\mathsf{error}`, B's state goes back to
what it was before the call, as {Informal.citet ACD19}[] specify in the prose before
Figure 6. So a failed $`\Dec` puts back the key that $`\mathsf{try\text{-}skipped}` removed,
and the honest message at that index can still arrive.
::::::
:::::::
::::::::

:::defTitle "fs_aead_from_aead_prg_correctness" "FS-AEAD from AEAD and PRG correctness"
:::

::::theorem "fs_aead_from_aead_prg_correctness" (parent := "fs_aead_fs_aead_from_aead_prg") (tags := "gh-29") (uses := "fs_aead_from_aead_prg_spec, fs_aead_scheme, aead_correctness, prg")
$`\todo`

:::leanPill "missing"
:::
::::

:::defTitle "fs_aead_from_aead_prg_security" "FS-AEAD from AEAD and PRG security"
:::

::::theorem "fs_aead_from_aead_prg_security" (parent := "fs_aead_fs_aead_from_aead_prg") (tags := "gh-32") (uses := "fs_aead_from_aead_prg_spec, fs_aead_scheme, fs_aead_security, aead_security_exp, prg")
$`\todo`

:::leanPill "missing"
:::
::::
