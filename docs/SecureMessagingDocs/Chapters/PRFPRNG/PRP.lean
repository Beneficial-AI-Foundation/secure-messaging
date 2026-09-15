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

:::::::definition "prp" (parent := "prp") (lean := "BlockCipher, PRPScheme, PRPScheme.prpAdvantage")
A pseudorandom permutation is the abstract model of a block cipher: a keyed, invertible
map on a block space $`\mathcal X` that no adversary can distinguish from a uniformly
random permutation of $`\mathcal X`.

:::leanPillCaption "a keyed permutation, given as mutually inverse forward and inverse maps"
:::

```anchor BlockCipher (project := ".") (module := ToVCVio.CryptoFoundations.PRP)
structure BlockCipher (K X : Type) where
  /-- The forward cipher function `CIPHₖ` (§5.1). -/
  perm : K → X → X
  /-- The inverse cipher function `CIPHₖ⁻¹`. -/
  invPerm : K → X → X
  /-- `perm k` and `invPerm k` are mutually inverse for every key `k`. -/
  correct : ∀ k x, invPerm k (perm k x) = x ∧ perm k (invPerm k x) = x
```

:::leanPillCaption "a block cipher plus randomized key generation"
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

The real experiment is *defined* to be the PRF real experiment at the forward permutation,
so the PRP and PRF games differ only on their ideal sides. That shared real term is what
the PRP/PRF switching inequality of {Informal.citet BR06}[] rests on.

:::leanPillCaption "the advantage: the gap between the real and ideal experiments"
:::

```anchor prpAdvantage (project := ".") (module := ToVCVio.CryptoFoundations.PRP)
noncomputable def prpAdvantage [SampleableType (Equiv.Perm X)]
    (prp : PRPScheme K X) (adversary : PRPAdversary X) : ℝ :=
  |(Pr[= true | prpRealExp prp adversary]).toReal -
    (Pr[= true | prpIdealExp adversary]).toReal|
```

{githubLabel}`github` {githubIssue 240}[]
:::::::
