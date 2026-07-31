import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessaging.KEM.MLKEM.Construction
import SecureMessaging.KEM.MLKEM.Correctness
import SecureMessaging.KEM.MLKEM.Correctness.EasyCryptBoundary

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

#doc (Manual) "ML-KEM" =>

:::group "ml_kem"
Module-Lattice Key Encapsulation Mechanism (ML-KEM, FIPS 203).
:::

:::defTitle "ml_kem_scheme" "ML-KEM scheme"
:::

::::definition "ml_kem_scheme" (parent := "ml_kem") (lean := "MLKEM.mlkemScheme")
$`\todo`

```anchor mlkemScheme (project := ".") (module := SecureMessaging.KEM.MLKEM.Construction)
def mlkemScheme (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p))) :
    KEMScheme ProbComp SharedSecret
      (EncapsulationKey (ParameterSet.params p)
        (Concrete.concreteEncoding (ParameterSet.params p)))
      (DecapsulationKey (ParameterSet.params p)
        (Concrete.concreteEncoding (ParameterSet.params p)))
      (Ciphertext (ParameterSet.params p)
        (Concrete.concreteEncoding (ParameterSet.params p))) :=
  asKEMScheme ring (Concrete.concreteEncoding (ParameterSet.params p)) prims
```

{githubLabel}`github` {githubIssue 215}[]
::::

:::defTitle "ml_kem_correctness" "ML-KEM correctness"
:::

::::theorem "ml_kem_correctness" (parent := "ml_kem") (lean := "MLKEM.deltaCorrect_fips203")
$`\todo`

```anchor deltaCorrectFips203 (project := ".") (module := SecureMessaging.KEM.MLKEM.Correctness)
theorem deltaCorrect_fips203 (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p)))
    (hRing : NTTRingLaws ring) (hModel : CoefficientFailureBound p ring prims) :
    (mlkemScheme p ring prims).deltaCorrect ProbCompRuntime.probComp
      (fips203DecapsulationFailureBound p)
```

:::leanPillCaption "`δ`-correctness predicate"
:::

```anchor deltaCorrect (project := ".") (module := ToVCVio.CryptoFoundations.KeyEncapMech)
def deltaCorrect (kem : KEMScheme m K PK SK C)
    (runtime : ProbCompRuntime m) (delta : ℝ≥0∞) : Prop :=
  kem.correctnessError runtime ≤ delta
```

:::leanPillCaption "FIPS 203 Table 1 exponents"
:::

```anchor decapsulationFailureExponent (project := ".") (module := SecureMessaging.KEM.MLKEM.Correctness.FailureRates)
def decapsulationFailureExponent : ParameterSet → ℚ
  | .MLKEM512 => 138.8
  | .MLKEM768 => 164.8
  | .MLKEM1024 => 174.8
```

:::leanPillCaption "failure bound $`δ_p = 2^{-e_p}`"
:::

```anchor fips203DecapsulationFailureBound (project := ".") (module := SecureMessaging.KEM.MLKEM.Correctness.FailureRates)
noncomputable def fips203DecapsulationFailureBound (p : ParameterSet) : ℝ≥0∞ :=
  2 ^ (-(decapsulationFailureExponent p : ℝ))
```

{usesLabel}`uses` {uses "ml_kem_scheme"}[] · {githubLabel}`github` {githubIssue 219}[]
::::

:::defTitle "ml_kem_correctness_easycrypt" "ML-KEM-768 correctness from EasyCrypt boundary axioms"
:::

::::theorem "ml_kem_correctness_easycrypt" (parent := "ml_kem")
  (lean := "MLKEM.deltaCorrect_mlkem768_easycrypt_of_le")
Assuming EC-1 (`EasyCryptMLKEM768.romCorrectnessError_le`) and EC-2
(`EasyCryptMLKEM768.correctnessError_le_romCorrectnessError`), and upper bounds
$`\delta_\mathrm{CB}\le\texttt{failprob}`$, $`\varepsilon_\mathrm{hs}\le\texttt{hsadv}`$,
$`\varepsilon_\mathrm{prf,kg}\le\texttt{prfadv}`$, and
$`\varepsilon_\mathrm{prf,enc}\le\texttt{prfadv}`$, ML-KEM-768 is
$`(\texttt{failprob} + \texttt{hsadv} + 2\cdot\texttt{prfadv})`$-correct.

:::leanPillCaption "EasyCrypt-boundary ML-KEM-768 correctness theorem"
:::

```anchor deltaCorrect_mlkem768_easycrypt_of_le (project := ".") (module := SecureMessaging.KEM.MLKEM.Correctness.EasyCryptBoundary)
theorem deltaCorrect_mlkem768_easycrypt_of_le {failprob hsadv prfadv : ℝ≥0∞}
    (hcb : EasyCryptMLKEM768.correctnessBoundError ≤ failprob)
    (hhs : EasyCryptMLKEM768.smoothingAdvantage ≤ hsadv)
    (hkg : EasyCryptMLKEM768.keygenPRFAdvantage ≤ prfadv)
    (henc : EasyCryptMLKEM768.encapsPRFAdvantage ≤ prfadv) :
    mlkem768Scheme.deltaCorrect ProbCompRuntime.probComp (failprob + hsadv + 2 * prfadv)
```

{usesLabel}`uses` {uses "ml_kem_scheme"}[] · {uses "ml_kem_correctness"}[] · {githubLabel}`github` {githubIssue 238}[]
::::

:::defTitle "ml_kem_security" "ML-KEM security"
:::

::::theorem "ml_kem_security" (parent := "ml_kem")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "ml_kem_scheme"}[] · {githubLabel}`github` {githubIssue 216}[]
::::
