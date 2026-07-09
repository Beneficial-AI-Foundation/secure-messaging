import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessaging.KEM.MLKEM.Construction
import SecureMessaging.KEM.MLKEM.Correctness

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
    (hRing : NTTRingLaws ring) (hModel : FIPS203NoiseModel p ring prims) :
    (mlkemScheme p ring prims).deltaCorrect ProbCompRuntime.probComp
      (fips203DecapsulationFailureBound p) :=
  deltaCorrect_of_underlying ring _ prims
    (underlyingCorrectnessError_le_fips203 p ring prims hRing hModel)
```

{usesLabel}`uses` {uses "ml_kem_scheme"}[] · {githubLabel}`github` {githubIssue 219}[]
::::

:::defTitle "ml_kem_security" "ML-KEM security"
:::

::::theorem "ml_kem_security" (parent := "ml_kem")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "ml_kem_scheme"}[] · {githubLabel}`github` {githubIssue 216}[]
::::
