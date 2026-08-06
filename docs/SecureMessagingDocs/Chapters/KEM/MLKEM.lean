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

{usesLabel}`uses` {uses "kpke"}[] · {githubLabel}`github` {githubIssue 215}[]
::::

:::defTitle "ml_kem_rand_leak" "ML-KEM randomness leakage"
:::

::::definition "ml_kem_rand_leak" (parent := "ml_kem") (lean := "MLKEM.mlkemRandLeak")

:::leanPillCaption "ML-KEM randomness leakage"
:::

```anchor mlkemRandLeak (project := ".") (module := SecureMessaging.KEM.MLKEM.Construction)
def mlkemRandLeak (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p))) :
    (mlkemScheme p ring prims).RandLeak where
  KeygenRand := Seed32 × Seed32
  EncapsRand := Message
  keygenRleak := do
    let d ← $ᵗ Seed32
    let z ← $ᵗ Seed32
    return (keygenInternal ring (Concrete.concreteEncoding (ParameterSet.params p)) prims d z,
      (d, z))
  encapsRleak := fun ek => do
    let m ← $ᵗ Message
    let (k, c) := encapsInternal ring (Concrete.concreteEncoding (ParameterSet.params p))
      prims ek m
    return ((c, k), m)
  keygen_fst := by
    simp only [mlkemScheme, asKEMScheme, keygen, bind_assoc, pure_bind]
  encaps_fst := fun _ek => by
    simp only [mlkemScheme, asKEMScheme, bind_assoc, pure_bind]
```

{usesLabel}`uses` {uses "ml_kem_scheme"}[]
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

:::defTitle "ml_kem_correctness_easycrypt" "ML-KEM-768 correctness from EasyCrypt assumptions"
:::

::::theorem "ml_kem_correctness_easycrypt" (parent := "ml_kem") (lean := "MLKEM.deltaCorrect_mlkem768_easycrypt_of_le")
$`\todo`

:::leanPillCaption "δ-correctness from EasyCrypt bounds"
:::

```anchor deltaCorrect_mlkem768_easycrypt_of_le (project := ".") (module := SecureMessaging.KEM.MLKEM.Correctness.EasyCryptBoundary)
theorem deltaCorrect_mlkem768_easycrypt_of_le {failprob hsadv prfadv : ℝ≥0∞}
    (hcb : EasyCryptMLKEM768.correctnessBoundError ≤ failprob)
    (hhs : EasyCryptMLKEM768.smoothingAdvantage ≤ hsadv)
    (hkg : EasyCryptMLKEM768.keygenPRFAdvantage ≤ prfadv)
    (henc : EasyCryptMLKEM768.encapsPRFAdvantage ≤ prfadv) :
    mlkem768Scheme.deltaCorrect ProbCompRuntime.probComp (failprob + hsadv + 2 * prfadv)
```

{usesLabel}`uses` {uses "ml_kem_scheme"}[] · {githubLabel}`github` {githubIssue 238}[]
::::

:::defTitle "ml_kem_security" "ML-KEM security"
:::

::::theorem "ml_kem_security" (parent := "ml_kem")
$`\todo`

:::leanPill "missing"
:::

{usesLabel}`uses` {uses "ml_kem_scheme"}[] · {githubLabel}`github` {githubIssue 216}[]
::::
