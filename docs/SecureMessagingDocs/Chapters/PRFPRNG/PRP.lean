import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import ToVCVio.CryptoFoundations.PRP

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
:::::gameCell "\\Exp{\\textsf{prp}\\text{-}\\textsf{real}}{\\textsf{PRP}}(\\adv)" (kind := "game")
$`k \sample \mathsf{keygen};\quad b' \gets \adv^{\mathsf{perm}\ k};\quad \Return b'`
:::::
:::::gameCell "\\Exp{\\textsf{prp}\\text{-}\\textsf{ideal}}{\\textsf{PRP}}(\\adv)" (kind := "game")
$`\pi \sample \mathsf{Perm}(\mathcal X);\quad b' \gets \adv^{\pi};\quad \Return b'`
:::::
::::::

:::leanPillCaption "PRP advantage"
:::

```anchor prpAdvantage (project := ".") (module := ToVCVio.CryptoFoundations.PRP)
noncomputable def prpAdvantage [SampleableType (Equiv.Perm X)]
    (prp : PRPScheme K X) (adversary : PRPAdversary X) : ℝ :=
  |(Pr[= true | prpRealExp prp adversary]).toReal -
    (Pr[= true | prpIdealExp adversary]).toReal|
```

:::::::
