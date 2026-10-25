import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Bibliography
import SecureMessagingDocs.Visuals.Notation
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Visuals.AEADAdversary
import SecureMessaging.AEAD.Defs

/-! # Blueprint chapter: AEAD Definitions -/

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

- {Informal.citet ACD19}[] — AEAD syntax and correctness (Definition 1), one-time IND-CCA
  game (Figure 1) and security (Definition 2).
- {Informal.citet TR25}[] — the AEAD advantage convention (Definition 2.5).

:::defTitle "aead" "AEAD scheme"
:::

::::definition "aead" (lean := "AEADScheme") (tags := "gh-192")
Adapted from {Informal.citet ACD19}[], Definition 1.

An authenticated encryption with associated data (AEAD) scheme is a tuple of algorithms
$`(\boxed{\mathsf{KeyGen}}, \Enc, \Dec)` with message space $`\mathcal M`, associated data
space $`\mathcal{AD}`, key space $`\mathcal K` and ciphertext space $`\mathcal C`, where

- $`\boxed{\mathsf{KeyGen}}` samples a key $`K \in \mathcal K`,
- $`\Enc` takes a key $`K`, associated data $`a` and a message $`m`, and produces a
  ciphertext $`e \gets \Enc(K, a, m)`,
- $`\Dec` takes a key $`K`, associated data $`a` and a ciphertext $`e`, and produces a
  message $`m \gets \Dec(K, a, e)`, $`\boxed{\text{or } \bot \text{ if it rejects } e}.`

$`\Enc` and $`\Dec` are deterministic. The boxed parts are not in Definition 1:
$`\mathsf{KeyGen}` replaces the uniform key $`K \sample \mathcal K` of Figure 1, and
$`\Dec` signals a rejection by $`\bot`.

```anchor AEADScheme (project := ".") (module := SecureMessaging.AEAD.Defs)
structure AEADScheme (m : Type → Type u) [Monad m] (M AD K C : Type) where
  /-- Sample a fresh symmetric key. -/
  keygen : m K
  /-- Deterministic encryption: `Enc(K, a, m) = e`. -/
  encrypt : K → AD → M → C
  /-- Deterministic authenticated decryption: `Dec(K, a, e) = some m` or `none`. -/
  decrypt : K → AD → C → Option M
```
::::

:::defTitle "aead_oracles" "AEAD game oracles"
:::

:::::::definition "aead_oracles" (lean := "AEADScheme.oracleEncrypt, AEADScheme.oracleDecrypt") (uses := "aead")
Adapted from {Informal.citet ACD19}[], Figure 1.

::::::gameGrid
:::::gameCell "\\textsf{Game state and notation}" (kind := "scheme-notation")
The game state consists of the key $`K`, the challenge bit $`b` and the challenge pair
$`(a^*, e^*)`: the associated data and the ciphertext returned by $`\Oenc`. Before the
first $`\Oenc` call, $`(a^*, e^*) = (\bot, \bot)`.

In the oracles, $`\req\varphi` means: if $`\varphi` is false, the oracle returns
$`\bot` and the game state does not change.
:::::

:::::gameCell "\\textsf{Correction}" (kind := "scheme-notation")
In {Informal.citet ACD19}[], Figure 1, $`\Odec` refuses every query $`(a, e^*)`, for every
associated data $`a`. The game then never tests whether $`e^*` decrypts under associated
data other than $`a^*`, so a scheme that ignores associated data is secure. Built on such a
scheme, the FS-AEAD scheme of {Informal.citet ACD19}[], Figure 6, is insecure, which
contradicts their Theorem 5. We correct this, marked by boxes in pseudocode:

- $`\Oenc` also stores the associated data $`a^*`;
- $`\Odec` refuses only the challenge pair $`(a^*, e^*)`.

{Informal.citet NRS14}[] restrict decryption queries in the same way.
:::::

:::::gameCell "\\textsf{Deviation}" (kind := "scheme-notation")
In {Informal.citet ACD19}[], Figure 1, $`\Oenc` with $`b = 1` samples $`e^*` from the whole
ciphertext space $`\mathcal C`. We sample $`e^*` uniformly among the ciphertexts of the same
length as $`\Enc(K, a, m)`, as the $`\$` oracle of {Informal.citet NRS14}[], Figure 4, does
(boxed in $`\Oenc`). When messages have variable length, $`\mathcal C` has no uniform
distribution, and every variable-length scheme fails the game of Figure 1 through the
ciphertext length alone. For ciphertexts of one length, the two games are the same. The FS-AEAD
game of {Informal.citet ACD19}[], Figure 5, requires $`|m_0| = |m_1|`, so their Theorem 5 needs
only this weaker notion.
:::::
::::::

::::::gameGrid
:::::gameCell "\\Oenc(a, m)" (kind := "compact")
$`\begin{array}{l}
\req\;e^* = \bot; \\
\pif\;b = 0\;\pthen \\
\quad e^* \gets \Enc(K, a, m); \\
\pelse \\
\quad \boxed{e^* \sample \{e \in \mathcal C : |e| = |\Enc(K, a, m)|\}}; \\
\boxed{a^* \gets a}; \\
\Return e^*
\end{array}`

```anchor oracleEncrypt (project := ".") (module := SecureMessaging.AEAD.Defs)
def oracleEncrypt [LenSampleable C] (ae : AEADScheme ProbComp M AD K C)
    (b : Bool) (k : K) :
    QueryImpl (AD × M →ₒ Option C) (StateT (Option (AD × C)) ProbComp) :=
  fun (a, m) => do
    match (← get) with
    | some _ => pure none
    | none =>
      let eStar ← if b
        then liftM (LenSampleable.unifSameLen (ae.encrypt k a m))
        else pure (ae.encrypt k a m)
      set (some (a, eStar))
      return some eStar
```
:::::

:::::gameCell "\\Odec(a, e)" (kind := "compact")
$`\begin{array}{l}
\req\;b = 0; \\
\req\;\boxed{(a, e) \neq (a^*, e^*)}; \\
\Return \Dec(K, a, e)
\end{array}`

```anchor oracleDecrypt (project := ".") (module := SecureMessaging.AEAD.Defs)
def oracleDecrypt [DecidableEq AD] [DecidableEq C] (ae : AEADScheme ProbComp M AD K C)
    (b : Bool) (k : K) :
    QueryImpl (AD × C →ₒ Option M) (StateT (Option (AD × C)) ProbComp) :=
  fun (a, e) => do
    let chal ← get
    if b || chal == some (a, e) then pure none
    else pure (ae.decrypt k a e)
```
:::::
::::::
:::::::

:::defTitle "aead_correctness" "AEAD correctness"
:::

:::definition "aead_correctness" (lean := "AEADScheme.Correct") (tags := "gh-193") (uses := "aead")
Adapted from {Informal.citet ACD19}[], Definition 1.

An AEAD scheme is correct if for all keys $`K`, associated data $`a` and messages $`m`,
$`\Dec(K, a, \Enc(K, a, m)) = m`.

```anchor Correct (project := ".") (module := SecureMessaging.AEAD.Defs)
def Correct (ae : AEADScheme m M AD K C) : Prop :=
  ∀ (k : K) (a : AD) (msg : M), ae.decrypt k a (ae.encrypt k a msg) = some msg
```
:::

:::defTitle "aead_security_exp" "AEAD security experiment"
:::

:::::::definition "aead_security_exp" (lean := "AEADScheme.securityExp, AEADScheme.aeadSecurityImpl, AEADScheme.OneTimeCCAAdversary") (tags := "gh-194") (uses := "aead, aead_oracles")
Adapted from {Informal.citet ACD19}[], Figure 1 and Definition 2.

Let $`\O = \{\Oenc, \Odec\}` and denote by $`\adv^{\O}` an adversary with oracle access to
$`\O`. The adversary can call $`\Odec` any number of times, before and after the single
$`\Oenc` call.

:::leanPillCaption "specification for oracle $`\\O` types"
:::

```anchor aeadOneTimeCCASpec (project := ".") (module := SecureMessaging.AEAD.Defs)
abbrev aeadOneTimeCCASpec (AD M C : Type) :=
  unifSpec + (AD × M →ₒ Option C) + (AD × C →ₒ Option M)
```

:::leanPillCaption "specification for oracle set $`\\O`"
:::

```anchor aeadSecurityImpl (project := ".") (module := SecureMessaging.AEAD.Defs)
def aeadSecurityImpl [LenSampleable C] [DecidableEq AD] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C) (b : Bool) (k : K) :
    QueryImpl (aeadOneTimeCCASpec AD M C) (StateT (Option (AD × C)) ProbComp) :=
  oracleUnif AD C + oracleEncrypt ae b k + oracleDecrypt ae b k
```

:::leanPillCaption "type of adversaries with oracle access"
:::

```anchor OneTimeCCAAdversary (project := ".") (module := SecureMessaging.AEAD.Defs)
abbrev OneTimeCCAAdversary (AD M C : Type) :=
  OracleComp (aeadOneTimeCCASpec AD M C) Bool
```

::::::gameGrid
:::::gameCell "\\textsf{Example run of this game}" (kind := "scheme")
Each oracle call has a solid arrow for the adversary's query and a dashed arrow for the
oracle's reply. An X marks a query that the game refuses; the reply is then $`\bot`.
The adversary decrypts once before the challenge. $`\Oenc` answers only its first call.
$`\Odec` refuses the challenge pair $`(a_1, e^*)` but answers $`(a_2, e^*)`, which
{Informal.citet ACD19}[], Figure 1, refuses (see the correction above).

:::aeadAdversaryIllustration
:::
:::::
::::::

::::::gameGrid
:::::gameCell "\\Exp{\\textsf{ot-cca}}{\\textsf{AEAD}}(\\adv)" (kind := "game")
$`\begin{array}{l}
\pcommentline{\text{Sample the key and the challenge bit}} \\
K \gets \mathsf{KeyGen};\quad b \sample \bit; \\
\pcommentline{\text{Initialize the game state: no challenge yet}} \\
(a^*, e^*) \gets (\bot, \bot); \\
\pcommentline{\text{Run the adversary and check its guess}} \\
b' \gets \adv^{\O}; \\
\Return(b' = b)
\end{array}`

:::leanPillCaption "Security experiment"
:::

```anchor securityExp (project := ".") (module := SecureMessaging.AEAD.Defs)
def securityExp [LenSampleable C] [DecidableEq AD] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OneTimeCCAAdversary AD M C) : ProbComp Bool := do
  let k ← ae.keygen
  let b ← $ᵗ Bool
  let (b', _) ← (simulateQ (aeadSecurityImpl ae b k) adversary).run none
  return (b == b')
```
:::::
::::::
:::::::

:::defTitle "aead_decrypt_query_bound" "AEAD decryption-query bound"
:::

:::definition "aead_decrypt_query_bound" (lean := "AEADScheme.decryptQueryBound") (uses := "aead_security_exp")
$`\mathsf{decryptQueryBound}(\adv, q_d)` holds if the adversary $`\adv` makes at most
$`q_d` queries to $`\Odec`. The security bounds for Encrypt-then-MAC and GCM have a term in
$`q_d`, the number of tries the adversary has to forge a tag.

```anchor decryptQueryBound (project := ".") (module := SecureMessaging.AEAD.Defs)
def decryptQueryBound (adv : OneTimeCCAAdversary AD M C)
    (q_d : ℕ) : Prop :=
  adv.IsQueryBoundP (· matches Sum.inr _) q_d
```
:::

:::defTitle "aead_guess_advantage" "AEAD guess advantage"
:::

:::definition "aead_guess_advantage" (lean := "AEADScheme.guessAdvantage") (uses := "aead_security_exp")
Following {Informal.citet TR25}[], Definition 2.5, the advantage of $`\adv` is

$$`\mathsf{Adv}^{\textsf{guess}}_{\textsf{AEAD}}(\adv)
  = \Bigl|\, \Pr[\,b' = b\,] - \tfrac{1}{2} \,\Bigr|`

```anchor guessAdvantage (project := ".") (module := SecureMessaging.AEAD.Defs)
noncomputable def guessAdvantage [LenSampleable C] [DecidableEq AD] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OneTimeCCAAdversary AD M C) : ℝ :=
  |(Pr{let x ← securityExp ae adversary}[x = true]).toReal - 1 / 2|
```
:::

:::defTitle "aead_dist_advantage" "AEAD distinguishing advantage"
:::

:::::definition "aead_dist_advantage" (lean := "AEADScheme.distAdvantage, AEADScheme.securityExpFixedBit") (uses := "aead_security_exp")
$$`\mathsf{Adv}^{\textsf{dist}}_{\textsf{AEAD}}(\adv)
  = \Bigl|\, \Pr[\mathsf{AEAD_{rand}} = 1] - \Pr[\mathsf{AEAD_{real}} = 1] \,\Bigr|`

where $`\mathsf{AEAD_{real}}` and $`\mathsf{AEAD_{rand}}` are the security experiment
with $`b` fixed to $`0` and to $`1`, and each returns the guess $`b'`. The security
theorems for Encrypt-then-MAC and GCM bound this advantage.

:::leanPillCaption "security experiment with a fixed challenge bit"
:::

```anchor securityExpFixedBit (project := ".") (module := SecureMessaging.AEAD.Defs)
def securityExpFixedBit [LenSampleable C] [DecidableEq AD] [DecidableEq C]
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
noncomputable def distAdvantage [LenSampleable C] [DecidableEq AD] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OneTimeCCAAdversary AD M C) : ℝ :=
  |(Pr{let x ← securityExpFixedBit ae adversary true}[x = true]).toReal -
   (Pr{let x ← securityExpFixedBit ae adversary false}[x = true]).toReal|
```
:::::

:::defTitle "aead_guess_dist_advantage" "Guess vs. distinguishing advantage"
:::

:::theorem "aead_guess_dist_advantage" (lean := "AEADScheme.guessAdvantage_eq_distAdvantage_div_two") (uses := "aead_guess_advantage, aead_dist_advantage")
Let $`\adv` be a one-time IND-CCA adversary. Then

$$`\mathsf{Adv}^{\textsf{guess}}_{\textsf{AEAD}}(\adv)
  = \tfrac{1}{2}\,\mathsf{Adv}^{\textsf{dist}}_{\textsf{AEAD}}(\adv)`

```anchor guessAdvantage_eq_distAdvantage_div_two (project := ".") (module := SecureMessaging.AEAD.Defs)
lemma guessAdvantage_eq_distAdvantage_div_two
    [LenSampleable C] [DecidableEq AD] [DecidableEq C]
    (ae : AEADScheme ProbComp M AD K C)
    (adversary : OneTimeCCAAdversary AD M C) :
    guessAdvantage ae adversary = distAdvantage ae adversary / 2
```
:::
