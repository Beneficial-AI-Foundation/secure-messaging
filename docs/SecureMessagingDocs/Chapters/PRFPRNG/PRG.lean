import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import VCVio.CryptoFoundations.PRG
import SecureMessaging.SCKA.MLKEMBraid.Security.KDFGame

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option verso.docstring.allowMissing true

open Verso.Genre Manual
open Informal
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "Pseudorandom Generators" =>

*References:*

- {Informal.citet ACD19}[] — PRG security (Section 2); the PRG $`G : \W \to \W \times \K`
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

:::defTitle "kdf_context_game" "Key derivation with an adversarially chosen label"
:::

:::::::definition "kdf_context_game" (parent := "prg") (lean := "Braid.kdfExp, Braid.KDFContextAdversary, Braid.kdfContextExp, Braid.kdfAdvantage") (uses := "prg")
Let $`F:\mathcal K\times\mathbb N\to\mathcal I` be a derivation function. A distinguisher
$`\mathcal C` first chooses a label $`e` and retains a state $`\sigma`. It then receives either
$`F(u,e)` for uniform $`u\in\mathcal K`, or a uniform $`x\in\mathcal I`, and outputs a bit.
Thus, for each label, $`u\mapsto F(u,e)` is viewed as a {bpref "prg"}[PRG], with the label chosen
before sampling $`u`.

Its advantage is

$$`\Adv{\mathsf{KDF}}{F}(\mathcal C)=
\left|\Pr[\mathsf{KDF}^{\mathsf{real}}_F(\mathcal C)=1]
-\Pr[\mathsf{KDF}^{\mathsf{ideal}}_F(\mathcal C)=1]\right|.`

::::::gameGrid
:::::gameCell "\\mathsf{KDF}^{\\mathsf{real}}_F(\\mathcal C)" (kind := "compact")
$`\begin{array}{l}
(e,\sigma)\sample\mathcal C.\mathsf{context}();\\
u\sample\mathcal K;\\
\Return\mathcal C.\mathsf{guess}(\sigma,F(u,e))
\end{array}`
:::::
:::::gameCell "\\mathsf{KDF}^{\\mathsf{ideal}}_F(\\mathcal C)" (kind := "compact")
$`\begin{array}{l}
(e,\sigma)\sample\mathcal C.\mathsf{context}();\\
x\sample\mathcal I;\\
\Return\mathcal C.\mathsf{guess}(\sigma,x)
\end{array}`
:::::
::::::

:::leanPillCaption "experiment at a fixed label"
:::

```anchor kdfExp (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Security.KDFGame)
def kdfExp {K EpochKey : Type} (kdfOK : K → ℕ → EpochKey)
    [SampleableType K] [SampleableType EpochKey]
    (e : ℕ) (D : EpochKey → ProbComp Bool) (derived : Bool) : ProbComp Bool :=
  if derived then PRGScheme.prgRealExperiment ⟨(kdfOK · e)⟩ D
  else PRGScheme.prgIdealExperiment D
```

:::leanPillCaption "distinguisher"
:::

```anchor KDFContextAdversary (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Security.KDFGame)
structure KDFContextAdversary (EpochKey : Type) where
  /-- The information kept between choosing the label and guessing. -/
  State : Type
  /-- Choose the label and the kept information. -/
  context : ProbComp (ℕ × State)
  /-- Guess from the kept information and the epoch key received. -/
  guess : State → EpochKey → ProbComp Bool
```

:::leanPillCaption "experiment with a chosen label"
:::

```anchor kdfContextExp (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Security.KDFGame)
def kdfContextExp {K EpochKey : Type} (kdfOK : K → ℕ → EpochKey)
    [SampleableType K] [SampleableType EpochKey]
    (C : KDFContextAdversary EpochKey) (derived : Bool) : ProbComp Bool := do
  let (e, st) ← C.context
  kdfExp kdfOK e (C.guess st) derived
```

:::leanPillCaption "advantage"
:::

```anchor kdfAdvantage (project := ".") (module := SecureMessaging.SCKA.MLKEMBraid.Security.KDFGame)
noncomputable def kdfAdvantage {K EpochKey : Type} (kdfOK : K → ℕ → EpochKey)
    [SampleableType K] [SampleableType EpochKey] (C : KDFContextAdversary EpochKey) : ℝ :=
  (𝒟[kdfContextExp kdfOK C true].boolDist 𝒟[kdfContextExp kdfOK C false]).toReal
```

:::::::
