import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import VCVio.CryptoFoundations.PRG

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option verso.docstring.allowMissing true

open Verso.Genre Manual
open Informal

set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "Pseudorandom Generators" =>

*References:*

- {Informal.citet ACD19}[] — PRG security (Section 2); the PRG $`G : \mathcal W \to \mathcal W \times \mathcal K`
  of the FS-AEAD construction (Section 4.2.2).

:::group "prg"
Pseudorandom generator (PRG).
:::

:::defTitle "prg" "Pseudorandom generator - PRG scheme and advantage"
:::

:::::::definition "prg" (parent := "prg") (lean := "PRGScheme, PRGScheme.prgAdvantage")
A PRG with seed space $`\mathcal S` and output space $`\mathcal R` is a deterministic map
$`G : \mathcal S \to \mathcal R`. Its advantage against a distinguisher $`\adv` is

$$`\mathsf{Adv}^{\textsf{prg}}_{G}(\adv)
  = \Bigl|\, \Pr\bigl[\Exp{\textsf{prg}\text{-}\textsf{real}}{G}(\adv) = 1\bigr]
  - \Pr\bigl[\Exp{\textsf{prg}\text{-}\textsf{ideal}}{G}(\adv) = 1\bigr] \,\Bigr|`

for the experiments below. The Lean definitions are VCVio's `PRGScheme`.

::::::gameGrid
:::::gameCell "\\Exp{\\textsf{prg}\\text{-}\\textsf{real}}{G}(\\adv)" (kind := "compact")
$`\begin{array}{l}
s \sample \mathcal S; \\
b' \gets \adv(G(s)); \\
\Return b'
\end{array}`
:::::
:::::gameCell "\\Exp{\\textsf{prg}\\text{-}\\textsf{ideal}}{G}(\\adv)" (kind := "compact")
$`\begin{array}{l}
r \sample \mathcal R; \\
b' \gets \adv(r); \\
\Return b'
\end{array}`
:::::
::::::
:::::::
