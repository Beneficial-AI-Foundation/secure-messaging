import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessaging.AEAD.Defs

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

#doc (Manual) "AEAD Definitions" =>

*References:*

- {Informal.citet ACD19}[] — AEAD syntax (Definition 1) and the one-time
  IND-CCA game (Figure 1, Definition 2).
- {Informal.citet TR25}[] — the AEAD advantage convention (Definition 2.5).

:::defTitle "aead" "Authenticated Encryption with Associated Data - AEAD scheme"
:::

:::definition "aead" (lean := "AEADScheme")
$`\todo`

```anchor AEADScheme (project := ".") (module := SecureMessaging.AEAD.Defs)
structure AEADScheme (m : Type → Type u) [Monad m] (M AD K C : Type) where
  /-- Sample a fresh symmetric key. -/
  keygen : m K
  /-- Deterministic encryption: `Enc(K, a, m) = e`. -/
  encrypt : K → AD → M → C
  /-- Deterministic authenticated decryption: `Dec(K, a, e) = some m` or `none`. -/
  decrypt : K → AD → C → Option M
```

{githubLabel}`github` {githubIssue 192}[]
:::


:::defTitle "aead_oracles" "AEAD game oracles"
:::

:::::::definition "aead_oracles" (lean := "AEADScheme.oracleEncrypt, AEADScheme.oracleDecrypt")
$`\todo`

::::::gameGrid
:::::gameCell "\\Oenc(a,m)" (kind := "oracle") (state := "\\gamestate\\; (e^*\\text{ - challenge ciphertext}, b\\text{ - challenge bit})")
$`\pif\;e^*\neq\bot\;\pthen\;\Return\bot`

$`\pif\;b\;\pthen\;e^* \sample \mathcal C\;\pelse\;e^* \gets \Enc(K,a,m);\quad \Return e^*`

```anchor oracleEncrypt (project := ".") (module := SecureMessaging.AEAD.Defs)
def oracleEncrypt [SampleableType C] (ae : AEADScheme ProbComp M AD K C)
    (b : Bool) (k : K) :
    QueryImpl (AD × M →ₒ Option C) (StateT (Option C) ProbComp) :=
  fun (a, m) => do
    match (← get) with
    | some _ => pure none
    | none =>
      let eStar ← if b
        then liftM ($ᵗ C : ProbComp C)
        else pure (ae.encrypt k a m)
      set (some eStar)
      return some eStar
```
:::::

:::::gameCell "\\Odec(a,e)" (kind := "oracle") (state := "\\gamestate\\; (e^*\\text{ - challenge ciphertext}, b\\text{ - challenge bit})")
$`\pif\;b\,\vee\,e{ = }e^*\;\pthen\;\Return\bot\;\pelse\;\Return \Dec(K,a,e)`

```anchor oracleDecrypt (project := ".") (module := SecureMessaging.AEAD.Defs)
def oracleDecrypt [DecidableEq C] (ae : AEADScheme ProbComp M AD K C)
    (b : Bool) (k : K) :
    QueryImpl (AD × C →ₒ Option M) (StateT (Option C) ProbComp) :=
  fun (a, e) => do
    if b || (← get) == some e then pure none
    else pure (ae.decrypt k a e)
```
:::::
::::::

{usesLabel}`uses` {uses "aead"}[]
:::::::

:::defTitle "aead_correctness" "AEAD correctness"
:::

:::definition "aead_correctness" (lean := "AEADScheme.Correct")
$`\todo`

```anchor Correct (project := ".") (module := SecureMessaging.AEAD.Defs)
def Correct (ae : AEADScheme m M AD K C) : Prop :=
  ∀ (k : K) (a : AD) (msg : M), ae.decrypt k a (ae.encrypt k a msg) = some msg
```

{usesLabel}`uses` {uses "aead"}[] · {githubLabel}`github` {githubIssue 193}[]
:::

:::defTitle "aead_security_exp" "AEAD security experiment"
:::

:::::::definition "aead_security_exp" (lean := "AEADScheme.securityExp, AEADScheme.aeadSecurityImpl, AEADScheme.OneTimeCCAAdversary")
$`\todo`

Let $`\O = \{\Oenc, \Odec\}` and denote by $`\adv^{\O}` an adversary with oracle access to $`\O`.

:::leanPillCaption "specification for oracle $`\\O` types"
:::

```anchor aeadOneTimeCCASpec (project := ".") (module := SecureMessaging.AEAD.Defs)
abbrev aeadOneTimeCCASpec (AD M C : Type) :=
  unifSpec + (AD × M →ₒ Option C) + (AD × C →ₒ Option M)
```

:::leanPillCaption "specification for oracle set $`\\O`"
:::

```anchor aeadSecurityImpl (project := ".") (module := SecureMessaging.AEAD.Defs)
def aeadSecurityImpl [SampleableType C] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C) (b : Bool) (k : K) :
    QueryImpl (aeadOneTimeCCASpec AD M C) (StateT (Option C) ProbComp) :=
  oracleUnif C + oracleEncrypt ae b k + oracleDecrypt ae b k
```

:::leanPillCaption "type of adversaries with oracle access"
:::

```anchor OneTimeCCAAdversary (project := ".") (module := SecureMessaging.AEAD.Defs)
abbrev OneTimeCCAAdversary (AD M C : Type) :=
  OracleComp (aeadOneTimeCCASpec AD M C) Bool
```

::::::gameGrid
:::::gameCell "\\Exp{\\textsf{1\\text{-}CCA}}{\\textsf{AEAD}}(\\adv)" (kind := "game")
$`K \sample \mathcal K;\quad b \sample \bit;\quad b' \gets \adv^{\O};\quad \Return(b'=b)`
:::::
::::::

```anchor securityExp (project := ".") (module := SecureMessaging.AEAD.Defs)
def securityExp [SampleableType C] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OneTimeCCAAdversary AD M C) : ProbComp Bool := do
  let k ← ae.keygen
  let b ← $ᵗ Bool
  let (b', _) ← (simulateQ (aeadSecurityImpl ae b k) adversary).run none
  return (b == b')
```

{usesLabel}`uses` {uses "aead"}[] · {uses "aead_oracles"}[] · {githubLabel}`github` {githubIssue 194}[]
:::::::


:::defTitle "aead_decrypt_query_bound" "AEAD decryption-query bound"
:::

:::definition "aead_decrypt_query_bound" (lean := "AEADScheme.decryptQueryBound")
$`\todo`

$`\mathsf{decryptQueryBound}(\adv, q_d)` asserts that the adversary $`\adv` makes at
most $`q_d` queries to the decryption oracle $`\Odec` (the tag-guessing term
$`q_d/|T|` in the EtM security bound is stated against this bound).

```anchor decryptQueryBound (project := ".") (module := SecureMessaging.AEAD.Defs)
def decryptQueryBound (adv : OneTimeCCAAdversary AD M C)
    (q_d : ℕ) : Prop :=
  adv.IsQueryBoundP (· matches Sum.inr _) q_d
```

{usesLabel}`uses` {uses "aead_security_exp"}[]
:::

:::defTitle "aead_guess_advantage" "AEAD guess advantage"
:::

:::definition "aead_guess_advantage" (lean := "AEADScheme.guessAdvantage")
$`\todo`

$$`\mathsf{Adv}^{\textsf{guess}}_{\textsf{AEAD}}(\adv)
  = \Bigl|\, \Pr[\,b' = b\,] - \tfrac{1}{2} \,\Bigr|`

```anchor guessAdvantage (project := ".") (module := SecureMessaging.AEAD.Defs)
noncomputable def guessAdvantage [SampleableType C] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OneTimeCCAAdversary AD M C) : ℝ :=
  |(Pr[= true | securityExp ae adversary]).toReal - 1 / 2|
```

{usesLabel}`uses` {uses "aead_security_exp"}[]
:::

:::defTitle "aead_dist_advantage" "AEAD distinguishing advantage"
:::

:::::definition "aead_dist_advantage" (lean := "AEADScheme.distAdvantage, AEADScheme.securityExpFixedBit")
$`\todo`

$$`\mathsf{Adv}^{\textsf{dist}}_{\textsf{AEAD}}(\adv)
  = \Bigl|\, \Pr[\mathsf{AEAD_{rand}} = 1] - \Pr[\mathsf{AEAD_{real}} = 1] \,\Bigr|`

Stated over the two fixed-bit experiments, each returning the adversary's raw
guess $`b'`: $`\mathsf{AEAD_{real}}` fixes $`b = 0` and $`\mathsf{AEAD_{rand}}`
fixes $`b = 1`. This is the advantage the Encrypt-then-MAC security theorem bounds.

:::leanPillCaption "security experiment with a fixed challenge bit"
:::

```anchor securityExpFixedBit (project := ".") (module := SecureMessaging.AEAD.Defs)
def securityExpFixedBit [SampleableType C] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OneTimeCCAAdversary AD M C)
    (b : Bool) : ProbComp Bool := do
  let k ← ae.keygen
  let (b', _) ← (simulateQ (aeadSecurityImpl ae b k) adversary).run none
  return b'
```

:::leanPillCaption "distinguishing advantage over the two fixed-bit experiments"
:::

```anchor distAdvantage (project := ".") (module := SecureMessaging.AEAD.Defs)
noncomputable def distAdvantage [SampleableType C] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OneTimeCCAAdversary AD M C) : ℝ :=
  |(Pr[= true | securityExpFixedBit ae adversary true]).toReal -
   (Pr[= true | securityExpFixedBit ae adversary false]).toReal|
```

{usesLabel}`uses` {uses "aead_security_exp"}[]
:::::

:::defTitle "aead_guess_dist_advantage" "Guess vs. distinguishing advantage"
:::

:::theorem "aead_guess_dist_advantage" (lean := "AEADScheme.guessAdvantage_eq_distAdvantage_div_two")
$`\todo`

$$`\mathsf{Adv}^{\textsf{guess}}_{\textsf{AEAD}}(\adv)
  = \tfrac{1}{2}\,\mathsf{Adv}^{\textsf{dist}}_{\textsf{AEAD}}(\adv)`

```anchor guessAdvantage_eq_distAdvantage_div_two (project := ".") (module := SecureMessaging.AEAD.Defs)
lemma guessAdvantage_eq_distAdvantage_div_two [SampleableType C] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OneTimeCCAAdversary AD M C) :
    guessAdvantage ae adversary = distAdvantage ae adversary / 2
```

{usesLabel}`uses` {uses "aead_guess_advantage"}[] · {uses "aead_dist_advantage"}[]
:::
