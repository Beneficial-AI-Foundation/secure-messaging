import Verso
import VersoManual
import VersoBlueprint
import SecureMessagingDocs.Visuals.GameBoxes
import SecureMessagingDocs.Visuals.AnchorPill
import SecureMessagingDocs.Bibliography
import SecureMessaging.RKEM.Defs

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

#doc (Manual) "RKEM Definitions" =>

:::group "rkem"
Ratcheting Key Encapsulation Mechanism (RKEM).
:::

:::defTitle "rkem_scheme" "RKEM scheme"
:::

:::definition "rkem_scheme" (parent := "rkem") (lean := "RKEMScheme") (tags := "gh-176")
$`\todo`

```anchor RKEMScheme (project := ".") (module := SecureMessaging.RKEM.Defs)
structure RKEMScheme (m : Type → Type u) [Monad m] (Par EK DK CT K : Type) where
  /-- `RSetup(1^λ) → par`: samples the public parameter shared by both parties. -/
  rsetup : m Par
  /-- `RKeyGen-A(par, ⊥) → (ekA, dkA)`: samples a fresh key pair for `A`. -/
  rkeygenAFresh : Par → m (EK × DK)
  /-- `RKeyGen-A(par, updated) → (ekA, dkA)`: samples an updated-distribution
  key pair for `A`. -/
  rkeygenAUpdated : Par → m (EK × DK)
  /-- `RKeyGen-B(par, ⊥) → (ekB, dkB)`: samples a fresh key pair for `B`. -/
  rkeygenBFresh : Par → m (EK × DK)
  /-- `RKeyGen-B(par, updated) → (ekB, dkB)`: samples an updated-distribution
  key pair for `B`. -/
  rkeygenBUpdated : Par → m (EK × DK)
  /-- `REnc-A(par, ekB, dkA) → (ctB, K, dk̂A)`: encapsulates towards `B`'s
  encapsulation key using `A`'s decapsulation key, producing a ciphertext for
  `B`, the shared key, and `A`'s updated decapsulation key. -/
  rencA : Par → EK → DK → m (CT × K × DK)
  /-- `RDec-A(par, dkA, ctA, ekB) → (K, ek̂B)`: decapsulates using `A`'s
  decapsulation key and `B`'s encapsulation key, producing the shared key and
  `B`'s updated encapsulation key. Never fails. -/
  rdecA : Par → DK → CT → EK → m (K × EK)
  /-- `REnc-B(par, ekA, dkB) → (ctA, K, dk̂B)`: as `rencA`, with the roles of
  `A` and `B` swapped. -/
  rencB : Par → EK → DK → m (CT × K × DK)
  /-- `RDec-B(par, dkB, ctB, ekA) → (K, ek̂A)`: as `rdecA`, with the roles of
  `A` and `B` swapped. -/
  rdecB : Par → DK → CT → EK → m (K × EK)
```

:::

:::defTitle "rkem_ratchet_sim" "RKEM ratchet simulatability"
:::

:::::::definition "rkem_ratchet_sim" (parent := "rkem") (lean := "RKEMScheme.RandLeak, RKEMScheme.RatchetSimulator, RKEMScheme.keyBaseSimDistA, RKEMScheme.keyUpdSimDistA, RKEMScheme.ctxtSimDistB, RKEMScheme.RatchetSimulatable") (tags := "gh-179") (uses := "rkem_scheme")
Adapted from {Informal.citet TR25}[], Definition 5.5 and Figures 10–12.

An RKEM is ratchet simulatable if there exist efficient simulators $`(\RSimKey\text{-}P_1,\RSimKey\text{-}P_2,\RSimCtxt\text{-}P)_{P\in\{\A,\B\}}` such that, for both parties $`P`, the real distribution $`\mathcal{D}_{P,0}` and the simulated distribution $`\mathcal{D}_{P,1}` of each of the three properties below are indistinguishable. Each property is shown for one party only, as in the paper; the other party's distributions swap the roles of $`\A` and $`\B`.

::::::gameGrid
:::::gameCell "\\textsf{Simulators}" (kind := "scheme-algorithms")
For each party $`P\in\{\A,\B\}`, with peer $`\bar P`:

$`\RSimKey\text{-}P_1(\ek_P,\dk_P)\to(\ekh{P},\dkh{P},\aux)`: from $`P`'s fresh key pair, simulate $`P`'s updated key pair, with auxiliary state $`\aux`.

$`\RSimKey\text{-}P_2(\ekh{\bar P},\dkh{\bar P},\aux)\to(\ct_{\bar P},K,K',\rand)`: from the peer's updated key pair and $`\aux`, simulate the rest of $`P`'s round: the ciphertext sent to the peer, both parties' shared keys, and coins explaining $`\REnc\text{-}P`.

$`\RSimCtxt\text{-}P(\ekh{P},\ekh{\bar P},\dkh{\bar P})\to(\ct_{\bar P},\ek_P,K,K')`: from $`P`'s updated encapsulation key and the peer's updated key pair, simulate $`P`'s ciphertext, $`P`'s fresh encapsulation key and both shared keys, without $`P`'s decapsulation key.
:::::
::::::

:::leanPillCaption "RatchetSimulator"
:::

```anchor RatchetSimulator (project := ".") (module := SecureMessaging.RKEM.Defs)
structure RatchetSimulator (rkem : RKEMScheme ProbComp Par EK DK CT K) (leak : rkem.RandLeak)
    where
  /-- Auxiliary state produced by `RSimKey-P₁` and consumed by `RSimKey-P₂`. -/
  Aux : Type
  /-- `RSimKey-A₁(par, ekA, dkA) → (ekÂ, dkÂ, aux)`: simulates `A`'s updated key pair from `A`'s
  fresh key pair. -/
  rsimKeyA1 : Par → EK → DK → ProbComp (EK × DK × Aux)
  /-- `RSimKey-A₂(par, ekB̂, dkB̂, aux) → (ctB, K, K', rand₂)`: completes `A`'s round from `B`'s
  updated key pair, producing the ciphertext to `B`, `A`'s and `B`'s shared keys, and coins
  explaining `REnc-A`. -/
  rsimKeyA2 : Par → EK → DK → Aux → ProbComp (CT × K × K × leak.EncRand)
  /-- `RSimCtxt-A(par, ekÂ, ekB̂, dkB̂) → (ctB, ekA, K, K')`: simulates `A`'s ciphertext and
  fresh encapsulation key from `A`'s updated encapsulation key and `B`'s updated key pair. -/
  rsimCtxtA : Par → EK → EK → DK → ProbComp (CT × EK × K × K)
  /-- `RSimKey-B₁`: as `rsimKeyA1`, with the roles of `A` and `B` swapped. -/
  rsimKeyB1 : Par → EK → DK → ProbComp (EK × DK × Aux)
  /-- `RSimKey-B₂`: as `rsimKeyA2`, with the roles of `A` and `B` swapped. -/
  rsimKeyB2 : Par → EK → DK → Aux → ProbComp (CT × K × K × leak.EncRand)
  /-- `RSimCtxt-B`: as `rsimCtxtA`, with the roles of `A` and `B` swapped. -/
  rsimCtxtB : Par → EK → EK → DK → ProbComp (CT × EK × K × K)
```

The updated-key and ciphertext distributions give the distinguisher the coins of some algorithms: $`\mathcal{D}\{\rand\}` samples from $`\mathcal{D}` with coins $`\rand`, which are uniformly distributed unless a simulator outputs them. Since the algorithms of an RKEM do not expose their coins, the definition is relative to a package of randomness-leaking fresh key generation and encapsulation algorithms.

:::leanPillCaption "RandLeak"
:::

```anchor RandLeak (project := ".") (module := SecureMessaging.RKEM.Defs)
structure RandLeak (rkem : RKEMScheme m Par EK DK CT K) where
  /-- Randomness space of one fresh key generation `RKeyGen-P(par, ⊥)`. -/
  KeygenRand : Type
  /-- Randomness space of one encapsulation `REnc-P`. -/
  EncRand : Type
  /-- `RKeyGen-A(par, ⊥)`, also returning its coins. -/
  rkeygenAFreshRleak : Par → m ((EK × DK) × KeygenRand)
  /-- `RKeyGen-B(par, ⊥)`, also returning its coins. -/
  rkeygenBFreshRleak : Par → m ((EK × DK) × KeygenRand)
  /-- `REnc-A(par, ekB, dkA)`, also returning its coins. -/
  rencARleak : Par → EK → DK → m ((CT × K × DK) × EncRand)
  /-- `REnc-B(par, ekA, dkB)`, also returning its coins. -/
  rencBRleak : Par → EK → DK → m ((CT × K × DK) × EncRand)
  /-- Ordinary fresh key generation for `A` is the first component of `rkeygenAFreshRleak`. -/
  rkeygenAFresh_fst : ∀ par,
    (do
      let out ← rkeygenAFreshRleak par
      pure out.1) = rkem.rkeygenAFresh par
  /-- Ordinary fresh key generation for `B` is the first component of `rkeygenBFreshRleak`. -/
  rkeygenBFresh_fst : ∀ par,
    (do
      let out ← rkeygenBFreshRleak par
      pure out.1) = rkem.rkeygenBFresh par
  /-- Ordinary encapsulation for `A` is the first component of `rencARleak`. -/
  rencA_fst : ∀ par ek dk,
    (do
      let out ← rencARleak par ek dk
      pure out.1) = rkem.rencA par ek dk
  /-- Ordinary encapsulation for `B` is the first component of `rencBRleak`. -/
  rencB_fst : ∀ par ek dk,
    (do
      let out ← rencBRleak par ek dk
      pure out.1) = rkem.rencB par ek dk
```

*Base-key simulatability.* A fresh key pair passed through $`\RSimKey\text{-}P_1` is indistinguishable from an updated key pair. This captures the first keys shared between the parties in the CKA protocol.

::::::gameGrid
:::::gameCell "\\mathcal{D}^{\\mathsf{KeyBaseSim}}_{\\A,0}" (kind := "game")
$`\begin{array}{l}
(\ekh{\A},\dkh{\A})\sample\DRKGup{\A} \\
\Return(\ekh{\A},\dkh{\A})
\end{array}`
:::::

:::::gameCell "\\mathcal{D}^{\\mathsf{KeyBaseSim}}_{\\A,1}" (kind := "game")
$`\begin{array}{l}
(\ekA,\dkA)\sample\DRKG{\A} \\
(\ekh{\A},\dkh{\A},\_)\sample\RSimKey\text{-}\A_1(\ekA,\dkA) \\
\Return(\ekh{\A},\dkh{\A})
\end{array}`
:::::
::::::

:::leanPillCaption "Base-key distributions"
:::

```anchor keyBaseSimDistA (project := ".") (module := SecureMessaging.RKEM.Defs)
def keyBaseSimDistA (rkem : RKEMScheme ProbComp Par EK DK CT K) {leak : rkem.RandLeak}
    (sim : rkem.RatchetSimulator leak) (par : Par) (b : Bool) : ProbComp (EK × DK) :=
  if b then do
    let (ekA, dkA) ← rkem.rkeygenAFresh par
    let (ekAHat, dkAHat, _) ← sim.rsimKeyA1 par ekA dkA
    return (ekAHat, dkAHat)
  else
    rkem.rkeygenAUpdated par
```

*Updated-key simulatability.* $`P`'s updated key pair can be simulated from $`P`'s fresh key pair alone, without the peer's encapsulation key that $`\REnc\text{-}P` needs. This breaks the dependence of the updated keys on the peer's keys, which drives the induction in the proof of CKA security from RKEM ({Informal.citet TR25}[], Theorem 5.6).

::::::gameGrid
:::::gameCell "\\mathcal{D}^{\\mathsf{KeyUpdSim}}_{\\A,0}" (kind := "game")
$`\begin{array}{l}
(\ek_\B,\dk_\B)\sample\DRKG{\B}\{\rand_0\} \\
(\ekh{\B},\dkh{\B},\aux_0)\sample\RSimKey\text{-}\B_1(\ek_\B,\dk_\B) \\
(\ekA,\dkA)\sample\DRKG{\A}\{\rand_1\} \\
(\ct_\B,K,\dkh{\A})\getsval\REnc\text{-}\A(\ekh{\B},\dkA;\rand_2) \\
(K',\ekh{\A})\sample\RDec\text{-}\B(\dkh{\B},\ct_\B,\ekA) \\
\Return\big((\ekh{\B},\dkh{\B}),(\ekh{\A},\dkh{\A}),\ct_\B,K,K', \\
\qquad\aux_0,\rand_0,\rand_1,\rand_2\big)
\end{array}`
:::::

:::::gameCell "\\mathcal{D}^{\\mathsf{KeyUpdSim}}_{\\A,1}" (kind := "game")
$`\begin{array}{l}
(\ek_\B,\dk_\B)\sample\DRKG{\B}\{\rand_0\} \\
(\ekh{\B},\dkh{\B},\aux_0)\sample\RSimKey\text{-}\B_1(\ek_\B,\dk_\B) \\
(\ekA,\dkA)\sample\DRKG{\A}\{\rand_1\} \\
(\ekh{\A},\dkh{\A},\aux_1)\sample\RSimKey\text{-}\A_1(\ekA,\dkA) \\
(\ct_\B,K,K',\rand_2)\sample\RSimKey\text{-}\A_2(\ekh{\B},\dkh{\B},\aux_1) \\
\Return\big((\ekh{\B},\dkh{\B}),(\ekh{\A},\dkh{\A}),\ct_\B,K,K', \\
\qquad\aux_0,\rand_0,\rand_1,\rand_2\big)
\end{array}`
:::::
::::::

:::leanPillCaption "Updated-key distributions"
:::

```anchor keyUpdSimDistA (project := ".") (module := SecureMessaging.RKEM.Defs)
def keyUpdSimDistA (rkem : RKEMScheme ProbComp Par EK DK CT K) {leak : rkem.RandLeak}
    (sim : rkem.RatchetSimulator leak) (par : Par) (b : Bool) :
    ProbComp (KeyUpdSimView EK DK CT K sim.Aux leak.KeygenRand leak.EncRand) := do
  let ((ekB, dkB), rand0) ← leak.rkeygenBFreshRleak par
  let (ekBHat, dkBHat, aux0) ← sim.rsimKeyB1 par ekB dkB
  let ((ekA, dkA), rand1) ← leak.rkeygenAFreshRleak par
  if b then
    let (ekAHat, dkAHat, aux1) ← sim.rsimKeyA1 par ekA dkA
    let (ctB, key, key', rand2) ← sim.rsimKeyA2 par ekBHat dkBHat aux1
    return ((ekBHat, dkBHat), (ekAHat, dkAHat), ctB, key, key', aux0, rand0, rand1, rand2)
  else
    let ((ctB, key, dkAHat), rand2) ← leak.rencARleak par ekBHat dkA
    let (key', ekAHat) ← rkem.rdecB par dkBHat ctB ekA
    return ((ekBHat, dkBHat), (ekAHat, dkAHat), ctB, key, key', aux0, rand0, rand1, rand2)
```

*Ciphertext simulatability.* The ciphertext that $`P` sends to its peer $`\bar P` can be simulated from $`\bar P`'s updated decapsulation key instead of $`P`'s own: together with $`\bar P`'s decapsulation key, it leaks nothing about $`P`'s decapsulation key. This is used to argue post-compromise security of the CKA.

::::::gameGrid
:::::gameCell "\\mathcal{D}^{\\mathsf{CtxtSim}}_{\\B,0}" (kind := "game")
$`\begin{array}{l}
(\ekA,\dkA)\sample\DRKG{\A}\{\rand\} \\
(\ekh{\A},\dkh{\A},\aux)\sample\RSimKey\text{-}\A_1(\ekA,\dkA) \\
(\ek_\B,\dk_\B)\sample\DRKG{\B} \\
(\ct_\A,K,\dkh{\B})\sample\REnc\text{-}\B(\ekh{\A},\dk_\B) \\
(K',\ekh{\B})\sample\RDec\text{-}\A(\dkh{\A},\ct_\A,\ek_\B) \\
\Return\big(\aux,\rand,(\ekh{\A},\dkh{\A}),\ct_\A, \\
\qquad(\ek_\B,\ekh{\B}),(K,K')\big)
\end{array}`
:::::

:::::gameCell "\\mathcal{D}^{\\mathsf{CtxtSim}}_{\\B,1}" (kind := "game")
$`\begin{array}{l}
(\ekA,\dkA)\sample\DRKG{\A}\{\rand\} \\
(\ekh{\A},\dkh{\A},\aux)\sample\RSimKey\text{-}\A_1(\ekA,\dkA) \\
(\ekh{\B},\dkh{\B})\sample\DRKGup{\B} \\
(\ct_\A,\ek_\B,K,K')\sample\RSimCtxt\text{-}\B(\ekh{\B},\ekh{\A},\dkh{\A}) \\
\Return\big(\aux,\rand,(\ekh{\A},\dkh{\A}),\ct_\A, \\
\qquad(\ek_\B,\ekh{\B}),(K,K')\big)
\end{array}`
:::::
::::::

:::leanPillCaption "Ciphertext distributions"
:::

```anchor ctxtSimDistB (project := ".") (module := SecureMessaging.RKEM.Defs)
def ctxtSimDistB (rkem : RKEMScheme ProbComp Par EK DK CT K) {leak : rkem.RandLeak}
    (sim : rkem.RatchetSimulator leak) (par : Par) (b : Bool) :
    ProbComp (CtxtSimView EK DK CT K sim.Aux leak.KeygenRand) := do
  let ((ekA, dkA), rand) ← leak.rkeygenAFreshRleak par
  let (ekAHat, dkAHat, aux) ← sim.rsimKeyA1 par ekA dkA
  if b then
    let (ekBHat, _) ← rkem.rkeygenBUpdated par
    let (ctA, ekB, key, key') ← sim.rsimCtxtB par ekBHat ekAHat dkAHat
    return (aux, rand, (ekAHat, dkAHat), ctA, (ekB, ekBHat), (key, key'))
  else
    let (ekB, dkB) ← rkem.rkeygenBFresh par
    let (ctA, key, _) ← rkem.rencB par ekAHat dkB
    let (key', ekBHat) ← rkem.rdecA par dkAHat ctA ekB
    return (aux, rand, (ekAHat, dkAHat), ctA, (ekB, ekBHat), (key, key'))
```

For each property $`\mathsf{X}\in\{\mathsf{KeyBaseSim},\mathsf{KeyUpdSim},\mathsf{CtxtSim}\}` and party $`P`, the advantage of a distinguisher $`\adv` is

$$`\mathsf{Adv}^{\mathsf{X}\text{-}P}(\adv)=\left|\Pr\left[b\sample\bit,\;x\sample\mathcal{D}^{\mathsf{X}}_{P,b},\;b'\sample\adv(x):b'=b\right]-\frac12\right|,\qquad \mathsf{Adv}^{\mathsf{X}}(\adv_\A,\adv_\B)=\max_{P\in\{\A,\B\}}\mathsf{Adv}^{\mathsf{X}\text{-}P}(\adv_P)`

and the RKEM is $`\varepsilon`-ratchet-simulatable when all three advantages are at most $`\varepsilon`.

:::leanPillCaption "RatchetSimulatable"
:::

```anchor RatchetSimulatable (project := ".") (module := SecureMessaging.RKEM.Defs)
def RatchetSimulatable (rkem : RKEMScheme ProbComp Par EK DK CT K) {leak : rkem.RandLeak}
    (sim : rkem.RatchetSimulator leak)
    (baseA baseB : KeyBaseSimAdversary Par EK DK)
    (updA updB : KeyUpdSimAdversary Par EK DK CT K sim.Aux leak.KeygenRand leak.EncRand)
    (ctxtA ctxtB : CtxtSimAdversary Par EK DK CT K sim.Aux leak.KeygenRand)
    (ε : ℝ) : Prop :=
  rkem.keyBaseSimAdvantage sim baseA baseB ≤ ε ∧
    rkem.keyUpdSimAdvantage sim updA updB ≤ ε ∧
    rkem.ctxtSimAdvantage sim ctxtA ctxtB ≤ ε
```
:::::::

:::defTitle "rkem_security_experiment" "RKEM Security Experiment"
:::

:::definition "rkem_security_experiment" (parent := "rkem") (lean := "RKEMScheme.securityExpA") (uses := "rkem_scheme")
$`\todo`

```anchor securityExpA (project := ".") (module := SecureMessaging.RKEM.Defs)
def securityExpA (rkem : RKEMScheme ProbComp Par EK DK CT K)
    (adversary : FSINDCPAAdversary Par EK DK CT K) [SampleableType K] : ProbComp Bool := do
  let b ← $ᵗ Bool
  let k1 ← $ᵗ K
  let par ← rkem.rsetup
  let (ekA, dkA) ← rkem.rkeygenAFresh par
  let (ekBHat, dkBHat) ← rkem.rkeygenBUpdated par
  let (ctB, k0, dkAHat) ← rkem.rencA par ekBHat dkA
  let (_, ekAHat) ← rkem.rdecB par dkBHat ctB ekA
  let b' ← adversary par ekA ekAHat ekBHat ctB dkAHat (if b then k1 else k0)
  return b == b'
```
:::

:::defTitle "rkem_guess_advantageA" "RKEM Guess Advantage"
:::

:::definition "rkem_guess_advantageA" (parent := "rkem") (lean := "RKEMScheme.fsIndCpaAdvantageA") (uses := "rkem_security_experiment")
$`\todo`

```anchor fsIndCpaAdvantageA (project := ".") (module := SecureMessaging.RKEM.Defs)
noncomputable def fsIndCpaAdvantageA (rkem : RKEMScheme ProbComp Par EK DK CT K)
    (adversary : FSINDCPAAdversary Par EK DK CT K) [SampleableType K] : ℝ :=
  |(Pr[= true | rkem.securityExpA adversary]).toReal - 1 / 2|
```
:::

:::defTitle "rkem_guess_advantage" "RKEM Guess Advantage"
:::

:::definition "rkem_guess_advantage" (parent := "rkem") (lean := "RKEMScheme.fsIndCpaAdvantage") (uses := "rkem_guess_advantageA")
$`\todo`

```anchor fsIndCpaAdvantage (project := ".") (module := SecureMessaging.RKEM.Defs)
noncomputable def fsIndCpaAdvantage (rkem : RKEMScheme ProbComp Par EK DK CT K)
    (adversaryA adversaryB : FSINDCPAAdversary Par EK DK CT K) [SampleableType K] : ℝ :=
  max (rkem.fsIndCpaAdvantageA adversaryA) (rkem.fsIndCpaAdvantageB adversaryB)
```
:::

:::defTitle "rkem_forward_security" "RKEM forward security"
:::

:::definition "rkem_forward_security" (parent := "rkem") (lean := "RKEMScheme.FSINDCPASecure") (tags := "gh-178") (uses := "rkem_guess_advantage")
$`\todo`

```anchor FSINDCPASecure (project := ".") (module := SecureMessaging.RKEM.Defs)
def FSINDCPASecure (rkem : RKEMScheme ProbComp Par EK DK CT K)
    (adversaryA adversaryB : FSINDCPAAdversary Par EK DK CT K) (epsilon : ℝ) [SampleableType K] :
    Prop :=
  rkem.fsIndCpaAdvantage adversaryA adversaryB ≤ epsilon
```
:::

:::defTitle "rkem_correctness" "RKEM correctness"
:::

:::definition "rkem_correctness" (parent := "rkem") (lean := "RKEMScheme.deltaCorrect") (tags := "gh-177") (uses := "rkem_scheme")
$`\todo`

```anchor deltaCorrect (project := ".") (module := SecureMessaging.RKEM.Defs)
def deltaCorrect (rkem : RKEMScheme m Par EK DK CT K) (runtime : ProbCompRuntime m)
    (deltaCorr : ℝ≥0∞) (deltaDist : ℝ≥0∞) [DecidableEq K] : Prop :=
  rkem.deltaCorrectUpdatedKeys runtime deltaCorr ∧ rkem.deltaCloseUpdateKeyDist runtime deltaDist
```
:::
