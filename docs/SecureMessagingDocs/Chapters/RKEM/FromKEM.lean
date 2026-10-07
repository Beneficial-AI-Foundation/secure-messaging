import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Bibliography
import SecureMessaging.RKEM.FromKEM.Construction
import SecureMessaging.RKEM.FromKEM.Correctness
import SecureMessaging.RKEM.FromKEM.Security
import SecureMessaging.RKEM.FromKEM.RatchetSimulatability

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option verso.docstring.allowMissing true

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open Informal

set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "RKEM from KEM" =>

:::group "rkem_rkem_from_kem"
RKEM from KEM.
:::

:::defTitle "rkem_from_kem_spec" "RKEM from KEM construction"
:::

::::definition "rkem_from_kem_spec" (parent := "rkem_rkem_from_kem") (lean := "kemRKEM.scheme, kemRKEM.rencRleak, kemRKEM.randLeak") (tags := "gh-75") (uses := "rkem_scheme")
$`\todo`

:::leanPillCaption "fresh/updated ratcheting key generation"
:::

```anchor rkeygen (project := ".") (module := SecureMessaging.RKEM.FromKEM.Construction)
def rkeygen {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C) : Unit → m (PK × SK) :=
  fun _ => kem.keygen
```

:::leanPillCaption "encapsulation"
:::

```anchor renc (project := ".") (module := SecureMessaging.RKEM.FromKEM.Construction)
def renc {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C) (_par : Unit) (ekPeer : PK) (_dkSelf : SK) :
    m ((PK × C) × K × SK) := do
  let (ct, key) ← kem.encaps ekPeer
  let (ekSelfHat, dkSelfHat) ← kem.keygen
  return ((ekSelfHat, ct), key, dkSelfHat)
```

:::leanPillCaption "decapsulation"
:::

```anchor rdec (project := ".") (module := SecureMessaging.RKEM.FromKEM.Construction)
def rdec {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C) (total : TotalDecaps kem)
    (_par : Unit) (dkSelfHat : SK) (ctSelf : PK × C) (_ekPeer : PK) :
    m (K × PK) := do
  let (ekPeerHat, ct) := ctSelf
  -- We have that kem.decaps dkSelfHat ct = some <$> decapsTotal dkSelfHat ct
  let key ← total.decapsTotal dkSelfHat ct
  return (key, ekPeerHat)
```

:::leanPillCaption "generic RKEM scheme"
:::

```anchor scheme (project := ".") (module := SecureMessaging.RKEM.FromKEM.Construction)
def scheme {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C) (total : TotalDecaps kem) :
    RKEMScheme m Unit PK SK (PK × C) K where
  rsetup := pure ()
  rkeygenAFresh := rkeygen kem
  rkeygenAUpdated := rkeygen kem
  rkeygenBFresh := rkeygen kem
  rkeygenBUpdated := rkeygen kem
  rencA := renc kem
  rdecA := rdec kem total
  rencB := renc kem
  rdecB := rdec kem total
```

Security notions that expose algorithm coins are stated relative to a randomness-leak package of the RKEM. For this construction it is built from one of the underlying KEM: fresh key generation leaks the coins of $`\KeyGen`, and $`\REnc\text{-}\mathsf{P}`, which runs $`\Enc` and then $`\KeyGen`, leaks the pair of their coins.

:::leanPillCaption "Leaking encapsulation"
:::

```anchor rencRleak (project := ".") (module := SecureMessaging.RKEM.FromKEM.Construction)
def rencRleak {kem : KEMScheme m K PK SK C} (kemLeak : kem.RandLeak) (_par : Unit)
    (ekPeer : PK) (_dkSelf : SK) : m (((PK × C) × K × SK) × kemLeak.Rand) := do
  let ((ct, key), encRand) ← kemLeak.encapsRleak ekPeer
  let ((ekSelfHat, dkSelfHat), keygenRand) ← kemLeak.keygenRleak
  return (((ekSelfHat, ct), key, dkSelfHat), (encRand, keygenRand))
```

:::leanPillCaption "Randomness-leak package"
:::

```anchor randLeak (project := ".") (module := SecureMessaging.RKEM.FromKEM.Construction)
def randLeak (kem : KEMScheme m K PK SK C) (total : TotalDecaps kem) (kemLeak : kem.RandLeak) :
    (scheme kem total).RandLeak where
  KeygenRand := kemLeak.KeygenRand
  EncRand := kemLeak.Rand
  rkeygenAFreshRleak := fun _ => kemLeak.keygenRleak
  rkeygenBFreshRleak := fun _ => kemLeak.keygenRleak
  rencARleak := rencRleak kemLeak
  rencBRleak := rencRleak kemLeak
  rkeygenAFresh_fst := fun _ => kemLeak.keygen_fst
  rkeygenBFresh_fst := fun _ => kemLeak.keygen_fst
  rencA_fst := rencRleak_fst kemLeak
  rencB_fst := rencRleak_fst kemLeak
```
::::

:::defTitle "rkem_from_kem_correctness" "RKEM from KEM correctness"
:::

:::theorem "rkem_from_kem_correctness" (parent := "rkem_rkem_from_kem") (lean := "kemRKEM.deltaCorrect") (tags := "gh-76") (uses := "rkem_from_kem_spec, rkem_scheme, rkem_correctness")
$`\todo`

```anchor deltaCorrect (project := ".") (module := SecureMessaging.RKEM.FromKEM.Correctness)
theorem deltaCorrect [DecidableEq K] (kem : KEMScheme ProbComp K PK SK C)
    (total : TotalDecaps kem) (δ : ℝ≥0∞) (hkem : kem.deltaCorrect ProbCompRuntime.probComp δ) :
    RKEMScheme.deltaCorrect (scheme kem total) ProbCompRuntime.probComp δ 0
```
:::

:::defTitle "rkem_from_kem_forward_security" "RKEM from KEM forward security"
:::

::::theorem "rkem_from_kem_forward_security" (parent := "rkem_rkem_from_kem") (lean := "kemRKEM.FSINDCPASecure") (tags := "gh-77") (uses := "rkem_from_kem_spec, rkem_scheme, rkem_forward_security")
$`\todo`

:::leanPillCaption "IND-CPA reduction adversary"
:::

```anchor indCpaReduction (project := ".") (module := SecureMessaging.RKEM.FromKEM.Security)
def indCpaReduction (kem : KEMScheme ProbComp K PK SK C)
    (adversary : RKEMScheme.FSINDCPAAdversary Unit PK SK (PK × C) K) :
    kem.IND_CPA_Adversary where
  State := PK
  preChallenge := fun ekBHat => pure ekBHat
  postChallenge := fun ekBHat ct kb => do
    let (ekA, _dkA) ← kem.keygen
    let (ekAHat, dkAHat) ← kem.keygen
    let b' ← adversary () ekA ekAHat ekBHat (ekAHat, ct) dkAHat kb
    return !b'
```

:::leanPillCaption "FS-IND-CPA security"
:::

```anchor FSINDCPASecure (project := ".") (module := SecureMessaging.RKEM.FromKEM.Security)
theorem FSINDCPASecure (kem : KEMScheme ProbComp K PK SK C) (total : TotalDecaps kem)
    (ε : ℝ)
    (hcpa : ∀ adv : kem.IND_CPA_Adversary,
      kem.IND_CPA_Advantage ProbCompRuntime.probComp adv ≤ ε)
    (adversaryA adversaryB : RKEMScheme.FSINDCPAAdversary Unit PK SK (PK × C) K) :
    RKEMScheme.FSINDCPASecure (scheme kem total) adversaryA adversaryB (ε / 2)
```
::::

:::defTitle "rkem_from_kem_ratchet_sim" "RKEM from KEM ratchet simulatability"
:::

:::::::theorem "rkem_from_kem_ratchet_sim" (parent := "rkem_rkem_from_kem") (lean := "kemRKEM.rsimKey1, kemRKEM.rsimKey2, kemRKEM.rsimCtxt, kemRKEM.ratchetSimulator, kemRKEM.RatchetSimulatable") (tags := "gh-78") (uses := "rkem_from_kem_spec, rkem_scheme, rkem_ratchet_sim")
Adapted from {Informal.citet TR25}[], Theorem A.2 and Figure 27.

The RKEM from KEM is perfectly ratchet simulatable: with the simulators below, the real and simulated distributions of base-key, updated-key and ciphertext simulatability coincide, so every distinguisher has advantage $`0`. This holds for any KEM whose decapsulation is total, which the construction itself already requires, with no correctness or security assumption.

:::leanPillCaption "Perfect ratchet simulatability"
:::

```anchor RatchetSimulatable (project := ".") (module := SecureMessaging.RKEM.FromKEM.RatchetSimulatability)
theorem RatchetSimulatable (kem : KEMScheme ProbComp K PK SK C) (total : TotalDecaps kem)
    (kemLeak : kem.RandLeak) :
    (scheme kem total).RatchetSimulatable (leak := randLeak kem total kemLeak) 0
```

Ratchet simulatability is stated relative to the construction's randomness-leak package, built from one of the underlying KEM (see the RKEM from KEM construction).

The simulators are the same for both parties $`\mathsf{P}\in\{\A,\B\}`, with peer $`\mathsf{\bar P}`. They follow Figure 27 of the paper, with the changes marked in comments, which make the simulation perfect: as printed, $`\RSimCtxt\text{-}\mathsf{P}` reuses $`\ekh{P}` as the fresh key $`\ek_\mathsf{P}`, which the real distribution samples independently, and $`\RSimKey\text{-}\mathsf{P}_2` returns $`K` twice, which would require a perfectly correct KEM. The figure also returns the outputs of $`\RSimKey\text{-}\mathsf{P}_1` in a different order.

::::::gameGrid
:::::gameCell "\\RSimKey\\text{-}\\mathsf{P}_1(\\ek_\\mathsf{P},\\dk_\\mathsf{P})" (kind := "compact")
$`\begin{array}{l}
(\ekh{P},\dkh{P})\sample\KeyGen(1^\lambda;\rand) \\
\aux_1:=(\ekh{P},\rand) \\
\Return(\ekh{P},\dkh{P},\aux_1)
\end{array}`

:::leanPillCaption "RSimKey-P₁"
:::

```anchor rsimKey1 (project := ".") (module := SecureMessaging.RKEM.FromKEM.RatchetSimulatability)
def rsimKey1 {kem : KEMScheme ProbComp K PK SK C} (kemLeak : kem.RandLeak) (_par : Unit)
    (_ekSelf : PK) (_dkSelf : SK) : ProbComp (PK × SK × (PK × kemLeak.KeygenRand)) := do
  let ((ekSelfHat, dkSelfHat), rand) ← kemLeak.keygenRleak
  return (ekSelfHat, dkSelfHat, (ekSelfHat, rand))
```
:::::

:::::gameCell "\\RSimKey\\text{-}\\mathsf{P}_2(\\ekh{\\bar P},\\dkh{\\bar P},\\aux_1)" (kind := "compact")
$`\begin{array}{l}
\textbf{parse}\;(\ekh{P},\rand)\gets\aux_1 \\
(\ct,K)\sample\Enc(\ekh{\bar P};\rand') \\
K'\gets\Dec(\dkh{\bar P},\ct) \\
\ct_{\mathsf{\bar P}}:=(\ekh{P},\ct) \\
\rand_2:=(\rand',\rand)\pcomment{\text{Fig. 27: }(\aux_1,\rand')} \\
\Return(\ct_{\mathsf{\bar P}},K,K',\rand_2)\pcomment{\text{Fig. 27: }K\text{ for }K'}
\end{array}`

:::leanPillCaption "RSimKey-P₂"
:::

```anchor rsimKey2 (project := ".") (module := SecureMessaging.RKEM.FromKEM.RatchetSimulatability)
def rsimKey2 {kem : KEMScheme ProbComp K PK SK C} (total : TotalDecaps kem)
    (kemLeak : kem.RandLeak) (_par : Unit) (ekPeerHat : PK) (dkPeerHat : SK)
    (aux : PK × kemLeak.KeygenRand) : ProbComp ((PK × C) × K × K × kemLeak.Rand) := do
  let (ekSelfHat, rand) := aux
  let ((ct, key), rand') ← kemLeak.encapsRleak ekPeerHat
  let key' ← total.decapsTotal dkPeerHat ct
  return ((ekSelfHat, ct), key, key', (rand', rand))
```
:::::

:::::gameCell "\\RSimCtxt\\text{-}\\mathsf{P}(\\ekh{P},\\ekh{\\bar P},\\dkh{\\bar P})" (kind := "compact")
$`\begin{array}{l}
(\ct,K)\sample\Enc(\ekh{\bar P}) \\
K'\gets\Dec(\dkh{\bar P},\ct) \\
\ct_{\mathsf{\bar P}}:=(\ekh{P},\ct) \\
(\ek_\mathsf{P},\_)\sample\KeyGen(1^\lambda)\pcomment{\text{Fig. 27: }\ek_\mathsf{P}:=\ekh{P}} \\
\Return(\ct_{\mathsf{\bar P}},\ek_\mathsf{P},K,K')
\end{array}`

:::leanPillCaption "RSimCtxt-P"
:::

```anchor rsimCtxt (project := ".") (module := SecureMessaging.RKEM.FromKEM.RatchetSimulatability)
def rsimCtxt (kem : KEMScheme ProbComp K PK SK C) (total : TotalDecaps kem) (_par : Unit)
    (ekSelfHat ekPeerHat : PK) (dkPeerHat : SK) : ProbComp ((PK × C) × PK × K × K) := do
  let (ct, key) ← kem.encaps ekPeerHat
  let key' ← total.decapsTotal dkPeerHat ct
  let (ekSelf, _) ← kem.keygen
  return ((ekSelfHat, ct), ekSelf, key, key')
```
:::::
::::::

:::leanPillCaption "Ratchet simulators"
:::

```anchor ratchetSimulator (project := ".") (module := SecureMessaging.RKEM.FromKEM.RatchetSimulatability)
def ratchetSimulator (kem : KEMScheme ProbComp K PK SK C) (total : TotalDecaps kem)
    (kemLeak : kem.RandLeak) :
    (scheme kem total).RatchetSimulator (randLeak kem total kemLeak) where
  Aux := PK × kemLeak.KeygenRand
  rsimKeyA1 := rsimKey1 kemLeak
  rsimKeyA2 := rsimKey2 total kemLeak
  rsimCtxtA := rsimCtxt kem total
  rsimKeyB1 := rsimKey1 kemLeak
  rsimKeyB2 := rsimKey2 total kemLeak
  rsimCtxtB := rsimCtxt kem total
```
:::::::
