import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import ToVCVio.CryptoFoundations.PRP
import ToVCVio.CryptoFoundations.PRPSwitching

/-! # Blueprint chapter: Pseudorandom Permutations -/

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

#doc (Manual) "Pseudorandom Permutations" =>

*References:*

- {Informal.citet BR06}[] — the PRP/PRF switching lemma.
- {Informal.citet NIST_GCM}[] — the block cipher as a prerequisite of GCM (§5.1).

:::group "prp"
Pseudorandom permutation (PRP).
:::

:::defTitle "prp" "Pseudorandom permutation - PRP scheme and advantage"
:::

:::::::definition "prp" (parent := "prp") (lean := "BlockCipher, PRPScheme, PRPScheme.prpAdvantage") (tags := "gh-240")
A block cipher on a key space $`\mathcal K` and a block space $`\mathcal X` is a pair of
maps $`\mathsf{perm}, \mathsf{perm}^{-1} : \mathcal K \times \mathcal X \to \mathcal X`
with $`\mathsf{perm}^{-1}(k, \mathsf{perm}(k, x)) = x` and
$`\mathsf{perm}(k, \mathsf{perm}^{-1}(k, x)) = x` for all $`k` and $`x`. A PRP scheme is a
block cipher together with a key generation algorithm $`\mathsf{keygen}`. Its PRP
advantage against an adversary $`\adv` is

$$`\mathsf{Adv}^{\textsf{prp}}_{\textsf{PRP}}(\adv)
  = \Bigl|\, \Pr\bigl[\Exp{\textsf{prp}\text{-}\textsf{real}}{\textsf{PRP}}(\adv) = 1\bigr]
  - \Pr\bigl[\Exp{\textsf{prp}\text{-}\textsf{ideal}}{\textsf{PRP}}(\adv) = 1\bigr] \,\Bigr|`

for the experiments below, where $`\mathsf{Perm}(\mathcal X)` is the set of permutations
of $`\mathcal X`.

:::leanPillCaption "block cipher"
:::

```anchor BlockCipher (project := ".") (module := ToVCVio.CryptoFoundations.PRP)
structure BlockCipher (K X : Type) where
  /-- The forward cipher function `CIPHₖ`. -/
  perm : K → X → X
  /-- The inverse cipher function `CIPHₖ⁻¹`. -/
  invPerm : K → X → X
  /-- `perm k` and `invPerm k` are mutually inverse for every key `k`. -/
  correct : ∀ k x, invPerm k (perm k x) = x ∧ perm k (invPerm k x) = x
```

:::leanPillCaption "PRP scheme"
:::

```anchor PRPScheme (project := ".") (module := ToVCVio.CryptoFoundations.PRP)
structure PRPScheme (K X : Type) extends BlockCipher K X where
  /-- Randomized key generation. -/
  keygen : ProbComp K
```

::::::gameGrid
:::::gameCell "\\Exp{\\textsf{prp}\\text{-}\\textsf{real}}{\\textsf{PRP}}(\\adv)" (kind := "compact")
$`\begin{array}{l}
k \sample \mathsf{keygen}; \\
b' \gets \adv^{\mathsf{perm}\ k}; \\
\Return b'
\end{array}`
:::::
:::::gameCell "\\Exp{\\textsf{prp}\\text{-}\\textsf{ideal}}{\\textsf{PRP}}(\\adv)" (kind := "compact")
$`\begin{array}{l}
\pi \sample \mathsf{Perm}(\mathcal X); \\
b' \gets \adv^{\pi}; \\
\Return b'
\end{array}`
:::::
::::::

:::leanPillCaption "PRP advantage"
:::

```anchor prpAdvantage (project := ".") (module := ToVCVio.CryptoFoundations.PRP)
noncomputable def prpAdvantage [SampleableType (Equiv.Perm X)]
    (prp : PRPScheme K X) (adversary : PRPAdversary X) : ℝ≥0∞ :=
  𝒟[prpRealExp prp adversary].boolDist 𝒟[prpIdealExp adversary]
```

:::::::

:::defTitle "prp_switching" "PRP/PRF switching"
:::

::::theorem "prp_switching" (parent := "prp") (lean := "PRPScheme.fixedQueryAdversary, PRPScheme.prfAdvantage_le_prpAdvantage_fixedQuery") (uses := "prp, prf")
Adapted from {Informal.citet BR06}[], Lemma 1, for queries fixed in advance.

Let $`P` be a PRP scheme on a finite block space $`\mathcal X` of $`N` blocks, and
$`x_1, \ldots, x_q` distinct blocks. Let $`\mathcal B` be a PRF adversary that first queries
its function oracle at $`x_1, \ldots, x_q` and then computes its output from the answers,
with no further function-oracle query. Then the {bpref "prf"}[PRF advantage] and the
{bpref "prp"}[PRP advantage] of $`\mathcal B` satisfy

$$`\mathsf{Adv}^{\textsf{prf}}_{P}(\mathcal B)
  \le \mathsf{Adv}^{\textsf{prp}}_{P}(\mathcal B) + \frac{q(q - 1)}{2N}.`

Lemma 1 of {Informal.citet BR06}[] holds for every adversary that makes at most $`q` queries,
adaptive ones included. Our statement covers only queries at blocks fixed in advance.

:::leanPillCaption "adversary with fixed queries"
:::

```anchor fixedQueryAdversary (project := ".") (module := ToVCVio.CryptoFoundations.PRPSwitching)
def fixedQueryAdversary {X : Type} (pts : List X) (tail : List X → ProbComp Bool) :
    PRPAdversary X
```

:::leanPillCaption "switching bound"
:::

```anchor prfAdvantage_le_prpAdvantage_fixedQuery (project := ".") (module := ToVCVio.CryptoFoundations.PRPSwitching)
theorem prfAdvantage_le_prpAdvantage_fixedQuery {K X : Type} [FinEnum X] [Nonempty X]
    (prp : PRPScheme K X) (pts : List X) (hpts : pts.Nodup) (tail : List X → ProbComp Bool) :
    (PRFScheme.prfAdvantage prp.toPRFScheme (fixedQueryAdversary pts tail)).toReal ≤
      (prpAdvantage prp (fixedQueryAdversary pts tail)).toReal +
      (pts.length * (pts.length - 1) : ℝ) / (2 * Fintype.card X)
```
::::
