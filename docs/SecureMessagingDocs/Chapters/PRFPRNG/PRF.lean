import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import VCVio.CryptoFoundations.PRF

/-! # Blueprint chapter: Pseudorandom Functions -/

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

#doc (Manual) "Pseudorandom Functions" =>

*References:*

- {Informal.citet NRS14}[] — the function family $`F` and its advantage
  $`\mathsf{Adv}^{\textsf{prf}}_F` (Section 2); the tag of the Encrypt-then-MAC scheme A5.
- {Informal.citet BR06}[] — the PRP/PRF switching lemma, which GCM uses to replace the block
  cipher by a random function.

:::group "prf"
Pseudorandom function (PRF).
:::

:::defTitle "prf" "Pseudorandom function - PRF scheme and advantage"
:::

:::::::definition "prf" (parent := "prf") (lean := "PRFScheme, PRFScheme.prfAdvantage")
A PRF scheme with key space $`\mathcal K`, domain $`\mathcal D` and finite nonempty range
$`\mathcal R` is a key generation algorithm $`\mathsf{keygen}` together with a deterministic map
$`F : \mathcal K \times \mathcal D \to \mathcal R`. Its PRF advantage against an adversary
$`\adv` is

$$`\mathsf{Adv}^{\textsf{prf}}_{F}(\adv)
  = \Bigl|\, \Pr\bigl[\Exp{\textsf{prf}\text{-}\textsf{real}}{F}(\adv) = 1\bigr]
  - \Pr\bigl[\Exp{\textsf{prf}\text{-}\textsf{ideal}}{F}(\adv) = 1\bigr] \,\Bigr|`

for the experiments below, where $`\mathsf{Func}(\mathcal D, \mathcal R)` is the set of
functions from $`\mathcal D` to $`\mathcal R`. {Informal.citet NRS14}[] define the advantage
without the absolute value. The absolute value does not change the bounds, because an
adversary can flip its output. In Lean, the ideal experiment samples the random function
lazily: it samples
$`\rho(x)` at the first query on $`x` and caches it. The Lean definitions are VCVio's
`PRFScheme` and `PRFScheme.prfAdvantage`.

::::::gameGrid
:::::gameCell "\\Exp{\\textsf{prf}\\text{-}\\textsf{real}}{F}(\\adv)" (kind := "game")
$`k \gets \mathsf{keygen};\quad b' \gets \adv^{F(k, \cdot)};\quad \Return b'`
:::::
:::::gameCell "\\Exp{\\textsf{prf}\\text{-}\\textsf{ideal}}{F}(\\adv)" (kind := "game")
$`\rho \sample \mathsf{Func}(\mathcal D, \mathcal R);\quad b' \gets \adv^{\rho};\quad \Return b'`
:::::
::::::
:::::::
