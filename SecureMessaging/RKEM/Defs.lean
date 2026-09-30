/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.ProbCompLift
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Ratcheting Key Encapsulation Mechanism (RKEM)

The forward-secure ratcheting KEM of [TripleRatchet, Def. 5.1], the main building
block used there to generically construct a CKA (compare `CKAScheme`).

An RKEM is a two-party protocol, with parties `A` and `B` exchanging encapsulation
keys and ciphertexts in a ping-pong manner. Unlike a plain KEM, a ciphertext
depends not only on the encapsulation key received in the previous round, but
also on the fresh decapsulation key held for the current round: running
encapsulation/decapsulation *ratchets*, producing an updated key for the next
round alongside the shared key.

[SPACES]
- `Par`: public-parameter space, sampled once by `rsetup` and shared as an
  input to every other algorithm.
- `EK`, `DK`: encapsulation- and decapsulation-key spaces. Definition 5.1 lets
  the "fresh" and "updated" ratcheting key spaces `RKP`/`RK̂P` differ; we use a
  single pair of spaces covering both, with `rkeygenAFresh`/`rkeygenAUpdated` (resp.
  `B`) selecting the distribution, exactly as in the paper's own shorthand
  `D_RKeyGen-P`/`D̂_RKeyGen-P`.
- `CT`: ciphertext space.
- `K`: shared-key space.

[ALGORITHMS]
- `rsetup : m Par`.
  `RSetup(1^λ) → par`: samples the public parameter shared by both parties.
- `rkeygenAFresh : Par → m (EK × DK)`, `rkeygenBFresh : Par → m (EK × DK)`.
  `RKeyGen-P(par, ⊥) → (ekP, dkP)`: samples a fresh encapsulation/decapsulation
  key pair for party `P`.
- `rkeygenAUpdated : Par → m (EK × DK)`, `rkeygenBUpdated : Par → m (EK × DK)`.
  `RKeyGen-P(par, updated) → (ekP, dkP)`: samples a key pair for `P` with the
  distribution of an *updated* key, i.e. one as could arise from `rencP`/`rdecP`.
  Used to state correctness/security, and in the setup of some constructions
  (Definition 5.1, footnote 12).
- `rencA : Par → EK → DK → m (CT × K × DK)`.
  `REnc-A(par, ekB, dkA) → (ctB, K, dk̂A)`: encapsulates towards `B`'s
  encapsulation key `ekB` using `A`'s decapsulation key `dkA`, producing a
  ciphertext `ctB` for `B`, the shared key `K`, and `A`'s updated decapsulation
  key `dk̂A`.
- `rdecA : Par → DK → CT → EK → m (K × EK)`.
  `RDec-A(par, dkA, ctA, ekB) → (K, ek̂B)`: decapsulates `ctA` using `A`'s
  decapsulation key `dkA` and `B`'s encapsulation key `ekB`, producing the
  shared key `K` and `B`'s updated encapsulation key `ek̂B`. Decapsulation never
  fails.
- `rencB : Par → EK → DK → m (CT × K × DK)`, `rdecB : Par → DK → CT → EK → m (K × EK)`.
  `REnc-B`, `RDec-B`: as `rencA`, `rdecA`, with the roles of `A` and `B` swapped.

[REFERENCES]

- [TripleRatchet] Dodis, Jost, Katsumata, Prest, Schmidt.
  *Triple Ratchet: A Bandwidth Efficient Hybrid-Secure Signal Protocol.*
  EUROCRYPT 2025, https://eprint.iacr.org/2025/078.pdf

For the non-forward-secure special case (Remark 5.2 of [TripleRatchet]), take
`rkeygenAUpdated`/`rkeygenBUpdated` to coincide with `rkeygenA`/`rkeygenB`, and
have `rencP`/`rdecP` return their input `dkP`/`ekP` unchanged as the "updated" key.
-/

open ENNReal

universe u

/-- A forward-secure ratcheting key encapsulation mechanism (RKEM), as in
Definition 5.1 of [TripleRatchet]. Public-parameter space `Par`, encapsulation-
and decapsulation-key spaces `EK`, `DK`, ciphertext space `CT`, and shared-key
space `K`. -/
-- ANCHOR: RKEMScheme
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
-- ANCHOR_END: RKEMScheme

namespace RKEMScheme

/-! ## Randomness leakage

The algorithms of `RKEMScheme` do not expose their coins. Security notions that hand the
adversary some of these coins are stated relative to a separate randomness-leak package, as for
`KEMScheme.RandLeak`.
-/

section RandLeak

variable {m : Type → Type u} [Monad m] {Par EK DK CT K : Type}

/-- Randomness-leaking versions of fresh key generation `RKeyGen-P(par, ⊥)` and encapsulation
`REnc-P`, for both parties, as needed by security notions that expose these algorithms' coins,
such as the ratchet-simulatability distributions of [TripleRatchet, Figs. 11–12] (their
`D_RKeyGen-P{rand}` and `REnc-A(…; rand₂)` lines). Each returns the ordinary output together
with the coins it sampled; the `_fst` fields say that the ordinary algorithm is the first
component. The coins of updated key generation and of decapsulation are never exposed, so they
have no leaking version. -/
-- ANCHOR: RandLeak
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
-- ANCHOR_END: RandLeak

end RandLeak

/-! ## Correctness

[TripleRatchet, Def. 5.3] asks for two properties, checked for both parties (`A` and `B`,
stated below only for `A`; the `B` versions swap the roles). Fix `A`'s fresh key pair, `B`'s
*updated* key pair, then run one round of the protocol from `A` towards `B`:

```
(ekA, dkA)   ← RKeyGen-A(par, ⊥),        (ek̂B, dk̂B) ← RKeyGen-B(par, updated),
(ctB, K, dk̂A) ← REnc-A(par, ek̂B, dkA),
(K', ek̂A)     ← RDec-B(par, dk̂B, ctB, ekA)
```

1. **Correctness with updated keys**: `K = K'` except with negligible probability.
2. **Correctness of update-key distribution**: the marginal distribution of `(ek̂A, dk̂A)`
   produced by the round above is statistically close to sampling `(ek̂A, dk̂A)` directly via
   `RKeyGen-A(par, updated)`.

`correctExpP`/`correctnessErrorP` capture property 1; `ratchetRoundOutputP`/`updateKeyDistErrorP`
capture property 2, using total-variation distance (`SPMF.tvDist`) in place of the paper's
asymptotic "statistically close".
-/

section Correctness

variable {m : Type → Type u} [Monad m] {Par EK DK CT K : Type}

/-- One round of the protocol from `A` towards `B`, with `A`'s keys fresh and `B`'s keys
updated, returning whether the two parties agree on the shared key (Def. 5.3, property 1). -/
def correctExpA (rkem : RKEMScheme m Par EK DK CT K) [DecidableEq K] : m Bool := do
  let par ← rkem.rsetup
  let (ekA, dkA) ← rkem.rkeygenAFresh par
  let (ekB, dkB) ← rkem.rkeygenBUpdated par
  let (ctB, key, _) ← rkem.rencA par ekB dkA
  let (key', _) ← rkem.rdecB par dkB ctB ekA
  return decide (key = key')

/-- As `correctExpA`, with the roles of `A` and `B` swapped. -/
def correctExpB (rkem : RKEMScheme m Par EK DK CT K) [DecidableEq K] : m Bool := do
  let par ← rkem.rsetup
  let (ekB, dkB) ← rkem.rkeygenBFresh par
  let (ekA, dkA) ← rkem.rkeygenAUpdated par
  let (ctA, key, _) ← rkem.rencB par ekA dkB
  let (key', _) ← rkem.rdecA par dkA ctA ekB
  return decide (key = key')

/-- Correctness error against `runtime`: missing success mass of `correctExpA`, i.e.
`1 - Pr[correctExpA = true]`. -/
noncomputable def correctnessErrorA (rkem : RKEMScheme m Par EK DK CT K)
    (runtime : ProbCompRuntime m) [DecidableEq K] : ℝ≥0∞ :=
  1 - Pr[= true | runtime.evalDist rkem.correctExpA]

/-- As `correctnessErrorA`, with the roles of `A` and `B` swapped. -/
noncomputable def correctnessErrorB (rkem : RKEMScheme m Par EK DK CT K)
    (runtime : ProbCompRuntime m) [DecidableEq K] : ℝ≥0∞ :=
  1 - Pr[= true | runtime.evalDist rkem.correctExpB]

/-- Def. 5.3, property 1: correctness with updated keys holds within error `delta`, for
both parties. -/
def deltaCorrectUpdatedKeys (rkem : RKEMScheme m Par EK DK CT K) (runtime : ProbCompRuntime m)
    (delta : ℝ≥0∞) [DecidableEq K] : Prop :=
  rkem.correctnessErrorA runtime ≤ delta ∧ rkem.correctnessErrorB runtime ≤ delta

/-- The marginal distribution of `A`'s updated key pair `(ek̂A, dk̂A)`, produced by running one
round of the protocol from `A` towards `B` as in `correctExpA`. -/
def ratchetRoundOutputA (rkem : RKEMScheme m Par EK DK CT K) : m (EK × DK) := do
  let par ← rkem.rsetup
  let (ekA, dkA) ← rkem.rkeygenAFresh par
  let (ekB, dkB) ← rkem.rkeygenBUpdated par
  let (ctB, _, dkAHat) ← rkem.rencA par ekB dkA
  let (_, ekAHat) ← rkem.rdecB par dkB ctB ekA
  return (ekAHat, dkAHat)

/-- As `ratchetRoundOutputA`, with the roles of `A` and `B` swapped. -/
def ratchetRoundOutputB (rkem : RKEMScheme m Par EK DK CT K) : m (EK × DK) := do
  let par ← rkem.rsetup
  let (ekB, dkB) ← rkem.rkeygenBFresh par
  let (ekA, dkA) ← rkem.rkeygenAUpdated par
  let (ctA, _, dkBHat) ← rkem.rencB par ekA dkB
  let (_, ekBHat) ← rkem.rdecA par dkA ctA ekB
  return (ekBHat, dkBHat)

/-- Total-variation distance, under `runtime`, between `ratchetRoundOutputA` and sampling directly
from `distKeyGenAUpdated`. -/
noncomputable def updateKeyDistErrorA (rkem : RKEMScheme m Par EK DK CT K)
    (runtime : ProbCompRuntime m) : ℝ≥0∞ :=
  ‖(SPMF.tvDist (runtime.evalDist rkem.ratchetRoundOutputA)
                (runtime.evalDist (do
                                  let par ← rkem.rsetup
                                  rkem.rkeygenAUpdated par)))‖ₑ

/-- As `updateKeyDistErrorA`, with the roles of `A` and `B` swapped. -/
noncomputable def updateKeyDistErrorB (rkem : RKEMScheme m Par EK DK CT K)
    (runtime : ProbCompRuntime m) : ℝ≥0∞ :=
  ‖SPMF.tvDist (runtime.evalDist rkem.ratchetRoundOutputB)
               (runtime.evalDist (do
                                  let par ← rkem.rsetup
                                  rkem.rkeygenBUpdated par))‖ₑ

/-- Def. 5.3, property 2: the updated-key distribution is within statistical distance `delta`
of the directly sampled updated-key distribution, for both parties. -/
def deltaCloseUpdateKeyDist (rkem : RKEMScheme m Par EK DK CT K) (runtime : ProbCompRuntime m)
    (delta : ℝ≥0∞) : Prop :=
  rkem.updateKeyDistErrorA runtime ≤ delta ∧ rkem.updateKeyDistErrorB runtime ≤ delta

/-- **Definition 5.3** (Correctness). `rkem` is `(deltaCorr, deltaDist)`-correct if it
satisfies both correctness with updated keys (`deltaCorrectUpdatedKeys`) and correctness of
the update-key distribution (`deltaCloseUpdateKeyDist`). -/
-- ANCHOR: deltaCorrect
def deltaCorrect (rkem : RKEMScheme m Par EK DK CT K) (runtime : ProbCompRuntime m)
    (deltaCorr : ℝ≥0∞) (deltaDist : ℝ≥0∞) [DecidableEq K] : Prop :=
  rkem.deltaCorrectUpdatedKeys runtime deltaCorr ∧ rkem.deltaCloseUpdateKeyDist runtime deltaDist
-- ANCHOR_END: deltaCorrect

end Correctness

/-! ## Forward-Secure IND-CPA Security

[TripleRatchet, Def. 5.4] extends a natural IND-CPA game with forward secrecy: the adversary
receives, alongside the challenge ciphertext and key, the *updated* decapsulation key produced
while creating that ciphertext, capturing that a later state compromise should not affect
already-issued keys. As with the correctness experiments, only the `A`-side game is spelled out
below; the `B`-side game (`securityExpB`) swaps the roles.
-/

section Security

variable {Par EK DK CT K : Type}

/-- A one-shot FS-IND-CPA adversary. Receives the challenged party's own encapsulation key,
its own updated encapsulation key, the peer's updated encapsulation key, the ciphertext sent to
the peer, the challenger's own updated decapsulation key, and the challenge key; outputs a
guess bit. Matches the adversary input `A(ekP, ek̂P, ek̂P', ctP, dk̂P, Kb)` of Def. 5.4. -/
abbrev FSINDCPAAdversary (Par EK DK CT K : Type) : Type :=
  Par → EK → EK → EK → CT → DK → K → ProbComp Bool

/-- **Definition 5.4** (FS-IND-CPA experiment, party `A`).

```
b ← {0,1}, K1 ← $K,
(ekA, dkA) ← D_RKeyGen-A, (ek̂B, dk̂B) ← D̂_RKeyGen-B,
(ctB, K0, dk̂A) ← REnc-A(par, ek̂B, dkA),
(·, ek̂A) ← RDec-B(par, dk̂B, ctB, ekA),
b' ← A(ekA, ek̂A, ek̂B, ctB, dk̂A, K_b)
```
returning `b = b'`. -/
-- ANCHOR: securityExpA
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
-- ANCHOR_END: securityExpA

/-- As `securityExpA`, with the roles of `A` and `B` swapped. -/
def securityExpB (rkem : RKEMScheme ProbComp Par EK DK CT K)
    (adversary : FSINDCPAAdversary Par EK DK CT K) [SampleableType K] : ProbComp Bool := do
  let b ← $ᵗ Bool
  let k1 ← $ᵗ K
  let par ← rkem.rsetup
  let (ekB, dkB) ← rkem.rkeygenBFresh par
  let (ekAHat, dkAHat) ← rkem.rkeygenAUpdated par
  let (ctA, k0, dkBHat) ← rkem.rencB par ekAHat dkB
  let (_, ekBHat) ← rkem.rdecA par dkAHat ctA ekB
  let b' ← adversary par ekB ekBHat ekAHat ctA dkBHat (if b then k1 else k0)
  return b == b'

/-- `Adv^{FS-IND-CPA-A}`: `|Pr[securityExpA = true] - 1/2|`. -/
-- ANCHOR: fsIndCpaAdvantageA
noncomputable def fsIndCpaAdvantageA (rkem : RKEMScheme ProbComp Par EK DK CT K)
    (adversary : FSINDCPAAdversary Par EK DK CT K) [SampleableType K] : ℝ :=
  |(Pr[= true | rkem.securityExpA adversary]).toReal - 1 / 2|
-- ANCHOR_END: fsIndCpaAdvantageA

/-- `Adv^{FS-IND-CPA-B}`: as `fsIndCpaAdvantageA`, with the roles of `A` and `B` swapped. -/
noncomputable def fsIndCpaAdvantageB (rkem : RKEMScheme ProbComp Par EK DK CT K)
    (adversary : FSINDCPAAdversary Par EK DK CT K) [SampleableType K] : ℝ :=
  |(Pr[= true | rkem.securityExpB adversary]).toReal - 1 / 2|

/-- `Adv^{FS-IND-CPA} := max_{P ∈ {A,B}} Adv^{FS-IND-CPA-P}`. -/
-- ANCHOR: fsIndCpaAdvantage
noncomputable def fsIndCpaAdvantage (rkem : RKEMScheme ProbComp Par EK DK CT K)
    (adversaryA adversaryB : FSINDCPAAdversary Par EK DK CT K) [SampleableType K] : ℝ :=
  max (rkem.fsIndCpaAdvantageA adversaryA) (rkem.fsIndCpaAdvantageB adversaryB)
-- ANCHOR_END: fsIndCpaAdvantage

/-- **Definition 5.4** (FS-IND-CPA security). `rkem` is `epsilon`-FS-IND-CPA-secure against
`adversaryA`, `adversaryB` if both per-party advantages are at most `epsilon`. Asymptotic
FS-IND-CPA security, as stated in [TripleRatchet], additionally quantifies this over every PPT
adversary and requires `epsilon` to be negligible in the security parameter. -/
-- ANCHOR: FSINDCPASecure
def FSINDCPASecure (rkem : RKEMScheme ProbComp Par EK DK CT K)
    (adversaryA adversaryB : FSINDCPAAdversary Par EK DK CT K) (epsilon : ℝ) [SampleableType K] :
    Prop :=
  rkem.fsIndCpaAdvantage adversaryA adversaryB ≤ epsilon
-- ANCHOR_END: FSINDCPASecure

end Security

/-! ## Ratchet Simulatability

[TripleRatchet, Def. 5.5] asks for simulators `(RSimKey-P₁, RSimKey-P₂, RSimCtxt-P)` for
`P ∈ {A, B}` such that the two distributions of each of [TripleRatchet, Figs. 10–12] are
indistinguishable, for both parties. Lines marked `*` are the ones the paper highlights as the
differences between the real (`0`) and simulated (`1`) distributions.

```text
Figure 10 (base-key simulatability):
+-- D^KeyBaseSim_{A,0} ----------------------------------------+
|   1: (ekÂ, dkÂ) ←$ D̂_RKeyGen-A                               |
|   2: return (ekÂ, dkÂ)                                       |
+-- D^KeyBaseSim_{A,1} ----------------------------------------+
|   1: (ekA, dkA) ←$ D_RKeyGen-A                               |
|   2: (ekÂ, dkÂ, _) ←$ RSimKey-A₁(ekA, dkA)                   |
|   3: return (ekÂ, dkÂ)                                       |
+--------------------------------------------------------------+
```

```text
Figure 11 (updated-key simulatability):
+-- D^KeyUpdSim_{A,0} -----------------------------------------+
|   1: (ekB, dkB) ←$ D_RKeyGen-B{rand₀}                        |
|   2: (ekB̂, dkB̂, aux₀) ←$ RSimKey-B₁(ekB, dkB)                |
|   3: (ekA, dkA) ←$ D_RKeyGen-A{rand₁}                        |
| * 4: (ctB, K, dkÂ) ← REnc-A(ekB̂, dkA; rand₂)                 |
| * 5: (K', ekÂ) ←$ RDec-B(dkB̂, ctB, ekA)                      |
|   6: return ((ekB̂, dkB̂), (ekÂ, dkÂ), ctB, K, K',             |
|               aux₀, rand₀, rand₁, rand₂)                     |
+-- D^KeyUpdSim_{A,1} -----------------------------------------+
|   1: (ekB, dkB) ←$ D_RKeyGen-B{rand₀}                        |
|   2: (ekB̂, dkB̂, aux₀) ←$ RSimKey-B₁(ekB, dkB)                |
|   3: (ekA, dkA) ←$ D_RKeyGen-A{rand₁}                        |
| * 4: (ekÂ, dkÂ, aux₁) ←$ RSimKey-A₁(ekA, dkA)                |
| * 5: (ctB, K, K', rand₂) ←$ RSimKey-A₂(ekB̂, dkB̂, aux₁)       |
|   6: return ((ekB̂, dkB̂), (ekÂ, dkÂ), ctB, K, K',             |
|               aux₀, rand₀, rand₁, rand₂)                     |
+--------------------------------------------------------------+
```

```text
Figure 12 (ciphertext simulatability):
+-- D^CtxtSim_{B,0} -------------------------------------------+
|   1: (ekA, dkA) ←$ D_RKeyGen-A{rand}                         |
|   2: (ekÂ, dkÂ, aux) ←$ RSimKey-A₁(ekA, dkA)                 |
| * 3: (ekB, dkB) ←$ D_RKeyGen-B                               |
| * 4: (ctA, K, dkB̂) ←$ REnc-B(ekÂ, dkB)                       |
|   5: (K', ekB̂) ←$ RDec-A(dkÂ, ctA, ekB)                      |
|   6: return (aux, rand, (ekÂ, dkÂ), ctA,                     |
|               (ekB, ekB̂), (K, K'))                           |
+-- D^CtxtSim_{B,1} -------------------------------------------+
|   1: (ekA, dkA) ←$ D_RKeyGen-A{rand}                         |
|   2: (ekÂ, dkÂ, aux) ←$ RSimKey-A₁(ekA, dkA)                 |
| * 3: (ekB̂, dkB̂) ←$ D̂_RKeyGen-B                               |
| * 4: (ctA, ekB, K, K') ←$ RSimCtxt-B(ekB̂, ekÂ, dkÂ)          |
|   5: return (aux, rand, (ekÂ, dkÂ), ctA,                     |
|               (ekB, ekB̂), (K, K'))                           |
+--------------------------------------------------------------+
```

Each property is a pair of distributions `D_{P,0}` (real) and `D_{P,1}` (simulated), with
advantage `|Pr[b ← {0,1}, x ← D_{P,b}, b' ← 𝒜(x) : b' = b] - 1/2|`. Below, only the `A`-side
distribution of each property from [TripleRatchet, Figs. 10–12] is described in full (for
ciphertext simulatability the paper spells out the `B` side, `D^CtxtSim_{B,b}`); the other side
swaps the roles. `b = false` selects `D_{P,0}` and `b = true` selects `D_{P,1}`.
-/

section RatchetSimulatability

variable {Par EK DK CT K : Type}

/-- Ratchet simulators `(RSimKey-P₁, RSimKey-P₂, RSimCtxt-P)_{P ∈ {A,B}}` of
[TripleRatchet, Def. 5.5], for `rkem` with randomness-leak package `leak`. `Aux` is the
simulator's own auxiliary-state space, passed from `RSimKey-P₁` to `RSimKey-P₂`. -/
-- ANCHOR: RatchetSimulator
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
-- ANCHOR_END: RatchetSimulator

/-! ### Base-key simulatability -/

/-- A base-key-simulatability distinguisher: receives the public parameter and a key pair
`(ekP̂, dkP̂)` (the sample `x` of Def. 5.5), and outputs a guess bit. -/
abbrev KeyBaseSimAdversary (Par EK DK : Type) : Type :=
  Par → EK × DK → ProbComp Bool

/-- **Figure 10** (`D^KeyBaseSim_{A,b}`).

```
D_{A,0}:  (ekÂ, dkÂ) ← D̂_RKeyGen-A
D_{A,1}:  (ekA, dkA) ← D_RKeyGen-A,  (ekÂ, dkÂ, _) ← RSimKey-A₁(ekA, dkA)
return (ekÂ, dkÂ)
``` -/
-- ANCHOR: keyBaseSimDistA
def keyBaseSimDistA (rkem : RKEMScheme ProbComp Par EK DK CT K) {leak : rkem.RandLeak}
    (sim : rkem.RatchetSimulator leak) (par : Par) (b : Bool) : ProbComp (EK × DK) :=
  if b then do
    let (ekA, dkA) ← rkem.rkeygenAFresh par
    let (ekAHat, dkAHat, _) ← sim.rsimKeyA1 par ekA dkA
    return (ekAHat, dkAHat)
  else
    rkem.rkeygenAUpdated par
-- ANCHOR_END: keyBaseSimDistA

/-- As `keyBaseSimDistA`, with the roles of `A` and `B` swapped. -/
def keyBaseSimDistB (rkem : RKEMScheme ProbComp Par EK DK CT K) {leak : rkem.RandLeak}
    (sim : rkem.RatchetSimulator leak) (par : Par) (b : Bool) : ProbComp (EK × DK) :=
  if b then do
    let (ekB, dkB) ← rkem.rkeygenBFresh par
    let (ekBHat, dkBHat, _) ← sim.rsimKeyB1 par ekB dkB
    return (ekBHat, dkBHat)
  else
    rkem.rkeygenBUpdated par

/-- Base-key-simulatability experiment for party `A`: `b ← {0,1}, x ← D^KeyBaseSim_{A,b},
b' ← 𝒜(x)`, returning `b = b'`. -/
def keyBaseSimExpA (rkem : RKEMScheme ProbComp Par EK DK CT K) {leak : rkem.RandLeak}
    (sim : rkem.RatchetSimulator leak) (adversary : KeyBaseSimAdversary Par EK DK) :
    ProbComp Bool := do
  let b ← $ᵗ Bool
  let par ← rkem.rsetup
  let x ← rkem.keyBaseSimDistA sim par b
  let b' ← adversary par x
  return b == b'

/-- As `keyBaseSimExpA`, with the roles of `A` and `B` swapped. -/
def keyBaseSimExpB (rkem : RKEMScheme ProbComp Par EK DK CT K) {leak : rkem.RandLeak}
    (sim : rkem.RatchetSimulator leak) (adversary : KeyBaseSimAdversary Par EK DK) :
    ProbComp Bool := do
  let b ← $ᵗ Bool
  let par ← rkem.rsetup
  let x ← rkem.keyBaseSimDistB sim par b
  let b' ← adversary par x
  return b == b'

/-- `Adv^{KeyBaseSim-A}`: `|Pr[keyBaseSimExpA = true] - 1/2|`. -/
noncomputable def keyBaseSimAdvantageA (rkem : RKEMScheme ProbComp Par EK DK CT K)
    {leak : rkem.RandLeak} (sim : rkem.RatchetSimulator leak)
    (adversary : KeyBaseSimAdversary Par EK DK) : ℝ :=
  |(Pr[= true | rkem.keyBaseSimExpA sim adversary]).toReal - 1 / 2|

/-- `Adv^{KeyBaseSim-B}`: as `keyBaseSimAdvantageA`, with the roles of `A` and `B` swapped. -/
noncomputable def keyBaseSimAdvantageB (rkem : RKEMScheme ProbComp Par EK DK CT K)
    {leak : rkem.RandLeak} (sim : rkem.RatchetSimulator leak)
    (adversary : KeyBaseSimAdversary Par EK DK) : ℝ :=
  |(Pr[= true | rkem.keyBaseSimExpB sim adversary]).toReal - 1 / 2|

/-- `Adv^{KeyBaseSim} := max_{P ∈ {A,B}} Adv^{KeyBaseSim-P}`. -/
noncomputable def keyBaseSimAdvantage (rkem : RKEMScheme ProbComp Par EK DK CT K)
    {leak : rkem.RandLeak} (sim : rkem.RatchetSimulator leak)
    (adversaryA adversaryB : KeyBaseSimAdversary Par EK DK) : ℝ :=
  max (rkem.keyBaseSimAdvantageA sim adversaryA) (rkem.keyBaseSimAdvantageB sim adversaryB)

/-! ### Updated-key simulatability -/

/-- The sample `x` of `D^KeyUpdSim_{P,b}` (Fig. 11), after the public parameter: the peer's
updated key pair, `P`'s updated key pair, the ciphertext sent by `P`, both shared keys `K`, `K'`,
the peer simulator's auxiliary state `aux₀`, the coins `rand₀`, `rand₁` of the peer's and `P`'s
fresh key generation, and the coins `rand₂` of `REnc-P`. -/
abbrev KeyUpdSimView (EK DK CT K Aux KeygenRand EncRand : Type) : Type :=
  (EK × DK) × (EK × DK) × CT × K × K × Aux × KeygenRand × KeygenRand × EncRand

/-- An updated-key-simulatability distinguisher: receives the public parameter and a sample of
`D^KeyUpdSim_{P,b}`, and outputs a guess bit. -/
abbrev KeyUpdSimAdversary (Par EK DK CT K Aux KeygenRand EncRand : Type) : Type :=
  Par → KeyUpdSimView EK DK CT K Aux KeygenRand EncRand → ProbComp Bool

/-- **Figure 11** (`D^KeyUpdSim_{A,b}`).

```
(ekB, dkB) ← D_RKeyGen-B{rand₀},  (ekB̂, dkB̂, aux₀) ← RSimKey-B₁(ekB, dkB),
(ekA, dkA) ← D_RKeyGen-A{rand₁},
D_{A,0}:  (ctB, K, dkÂ) ← REnc-A(ekB̂, dkA; rand₂),  (K', ekÂ) ← RDec-B(dkB̂, ctB, ekA)
D_{A,1}:  (ekÂ, dkÂ, aux₁) ← RSimKey-A₁(ekA, dkA),
          (ctB, K, K', rand₂) ← RSimKey-A₂(ekB̂, dkB̂, aux₁)
return ((ekB̂, dkB̂), (ekÂ, dkÂ), ctB, K, K', aux₀, rand₀, rand₁, rand₂)
``` -/
-- ANCHOR: keyUpdSimDistA
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
-- ANCHOR_END: keyUpdSimDistA

/-- As `keyUpdSimDistA`, with the roles of `A` and `B` swapped. -/
def keyUpdSimDistB (rkem : RKEMScheme ProbComp Par EK DK CT K) {leak : rkem.RandLeak}
    (sim : rkem.RatchetSimulator leak) (par : Par) (b : Bool) :
    ProbComp (KeyUpdSimView EK DK CT K sim.Aux leak.KeygenRand leak.EncRand) := do
  let ((ekA, dkA), rand0) ← leak.rkeygenAFreshRleak par
  let (ekAHat, dkAHat, aux0) ← sim.rsimKeyA1 par ekA dkA
  let ((ekB, dkB), rand1) ← leak.rkeygenBFreshRleak par
  if b then
    let (ekBHat, dkBHat, aux1) ← sim.rsimKeyB1 par ekB dkB
    let (ctA, key, key', rand2) ← sim.rsimKeyB2 par ekAHat dkAHat aux1
    return ((ekAHat, dkAHat), (ekBHat, dkBHat), ctA, key, key', aux0, rand0, rand1, rand2)
  else
    let ((ctA, key, dkBHat), rand2) ← leak.rencBRleak par ekAHat dkB
    let (key', ekBHat) ← rkem.rdecA par dkAHat ctA ekB
    return ((ekAHat, dkAHat), (ekBHat, dkBHat), ctA, key, key', aux0, rand0, rand1, rand2)

/-- Updated-key-simulatability experiment for party `A`: `b ← {0,1}, x ← D^KeyUpdSim_{A,b},
b' ← 𝒜(x)`, returning `b = b'`. -/
def keyUpdSimExpA (rkem : RKEMScheme ProbComp Par EK DK CT K) {leak : rkem.RandLeak}
    (sim : rkem.RatchetSimulator leak)
    (adversary : KeyUpdSimAdversary Par EK DK CT K sim.Aux leak.KeygenRand leak.EncRand) :
    ProbComp Bool := do
  let b ← $ᵗ Bool
  let par ← rkem.rsetup
  let x ← rkem.keyUpdSimDistA sim par b
  let b' ← adversary par x
  return b == b'

/-- As `keyUpdSimExpA`, with the roles of `A` and `B` swapped. -/
def keyUpdSimExpB (rkem : RKEMScheme ProbComp Par EK DK CT K) {leak : rkem.RandLeak}
    (sim : rkem.RatchetSimulator leak)
    (adversary : KeyUpdSimAdversary Par EK DK CT K sim.Aux leak.KeygenRand leak.EncRand) :
    ProbComp Bool := do
  let b ← $ᵗ Bool
  let par ← rkem.rsetup
  let x ← rkem.keyUpdSimDistB sim par b
  let b' ← adversary par x
  return b == b'

/-- `Adv^{KeyUpdSim-A}`: `|Pr[keyUpdSimExpA = true] - 1/2|`. -/
noncomputable def keyUpdSimAdvantageA (rkem : RKEMScheme ProbComp Par EK DK CT K)
    {leak : rkem.RandLeak} (sim : rkem.RatchetSimulator leak)
    (adversary : KeyUpdSimAdversary Par EK DK CT K sim.Aux leak.KeygenRand leak.EncRand) : ℝ :=
  |(Pr[= true | rkem.keyUpdSimExpA sim adversary]).toReal - 1 / 2|

/-- `Adv^{KeyUpdSim-B}`: as `keyUpdSimAdvantageA`, with the roles of `A` and `B` swapped. -/
noncomputable def keyUpdSimAdvantageB (rkem : RKEMScheme ProbComp Par EK DK CT K)
    {leak : rkem.RandLeak} (sim : rkem.RatchetSimulator leak)
    (adversary : KeyUpdSimAdversary Par EK DK CT K sim.Aux leak.KeygenRand leak.EncRand) : ℝ :=
  |(Pr[= true | rkem.keyUpdSimExpB sim adversary]).toReal - 1 / 2|

/-- `Adv^{KeyUpdSim} := max_{P ∈ {A,B}} Adv^{KeyUpdSim-P}`. -/
noncomputable def keyUpdSimAdvantage (rkem : RKEMScheme ProbComp Par EK DK CT K)
    {leak : rkem.RandLeak} (sim : rkem.RatchetSimulator leak)
    (adversaryA adversaryB :
      KeyUpdSimAdversary Par EK DK CT K sim.Aux leak.KeygenRand leak.EncRand) : ℝ :=
  max (rkem.keyUpdSimAdvantageA sim adversaryA) (rkem.keyUpdSimAdvantageB sim adversaryB)

/-! ### Ciphertext simulatability -/

/-- The sample `x` of `D^CtxtSim_{P,b}` (Fig. 12), after the public parameter: the peer
simulator's auxiliary state `aux`, the coins `rand` of the peer's fresh key generation, the
peer's updated key pair, the ciphertext sent by `P`, `P`'s fresh and updated encapsulation keys,
and both shared keys `K`, `K'`. `P`'s decapsulation keys are *not* part of the sample. -/
abbrev CtxtSimView (EK DK CT K Aux KeygenRand : Type) : Type :=
  Aux × KeygenRand × (EK × DK) × CT × (EK × EK) × (K × K)

/-- A ciphertext-simulatability distinguisher: receives the public parameter and a sample of
`D^CtxtSim_{P,b}`, and outputs a guess bit. -/
abbrev CtxtSimAdversary (Par EK DK CT K Aux KeygenRand : Type) : Type :=
  Par → CtxtSimView EK DK CT K Aux KeygenRand → ProbComp Bool

/-- **Figure 12**, roles swapped (`D^CtxtSim_{A,b}`; the figure itself spells out
`D^CtxtSim_{B,b}`, see `ctxtSimDistB`).

```
(ekB, dkB) ← D_RKeyGen-B{rand},  (ekB̂, dkB̂, aux) ← RSimKey-B₁(ekB, dkB),
D_{A,0}:  (ekA, dkA) ← D_RKeyGen-A,
          (ctB, K, dkÂ) ← REnc-A(ekB̂, dkA),  (K', ekÂ) ← RDec-B(dkB̂, ctB, ekA)
D_{A,1}:  (ekÂ, dkÂ) ← D̂_RKeyGen-A,  (ctB, ekA, K, K') ← RSimCtxt-A(ekÂ, ekB̂, dkB̂)
return (aux, rand, (ekB̂, dkB̂), ctB, (ekA, ekÂ), (K, K'))
``` -/
def ctxtSimDistA (rkem : RKEMScheme ProbComp Par EK DK CT K) {leak : rkem.RandLeak}
    (sim : rkem.RatchetSimulator leak) (par : Par) (b : Bool) :
    ProbComp (CtxtSimView EK DK CT K sim.Aux leak.KeygenRand) := do
  let ((ekB, dkB), rand) ← leak.rkeygenBFreshRleak par
  let (ekBHat, dkBHat, aux) ← sim.rsimKeyB1 par ekB dkB
  if b then
    let (ekAHat, _) ← rkem.rkeygenAUpdated par
    let (ctB, ekA, key, key') ← sim.rsimCtxtA par ekAHat ekBHat dkBHat
    return (aux, rand, (ekBHat, dkBHat), ctB, (ekA, ekAHat), (key, key'))
  else
    let (ekA, dkA) ← rkem.rkeygenAFresh par
    let (ctB, key, _) ← rkem.rencA par ekBHat dkA
    let (key', ekAHat) ← rkem.rdecB par dkBHat ctB ekA
    return (aux, rand, (ekBHat, dkBHat), ctB, (ekA, ekAHat), (key, key'))

/-- **Figure 12** (`D^CtxtSim_{B,b}`).

```
(ekA, dkA) ← D_RKeyGen-A{rand},  (ekÂ, dkÂ, aux) ← RSimKey-A₁(ekA, dkA),
D_{B,0}:  (ekB, dkB) ← D_RKeyGen-B,
          (ctA, K, dkB̂) ← REnc-B(ekÂ, dkB),  (K', ekB̂) ← RDec-A(dkÂ, ctA, ekB)
D_{B,1}:  (ekB̂, dkB̂) ← D̂_RKeyGen-B,  (ctA, ekB, K, K') ← RSimCtxt-B(ekB̂, ekÂ, dkÂ)
return (aux, rand, (ekÂ, dkÂ), ctA, (ekB, ekB̂), (K, K'))
``` -/
-- ANCHOR: ctxtSimDistB
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
-- ANCHOR_END: ctxtSimDistB

/-- Ciphertext-simulatability experiment for party `A`: `b ← {0,1}, x ← D^CtxtSim_{A,b},
b' ← 𝒜(x)`, returning `b = b'`. -/
def ctxtSimExpA (rkem : RKEMScheme ProbComp Par EK DK CT K) {leak : rkem.RandLeak}
    (sim : rkem.RatchetSimulator leak)
    (adversary : CtxtSimAdversary Par EK DK CT K sim.Aux leak.KeygenRand) :
    ProbComp Bool := do
  let b ← $ᵗ Bool
  let par ← rkem.rsetup
  let x ← rkem.ctxtSimDistA sim par b
  let b' ← adversary par x
  return b == b'

/-- As `ctxtSimExpA`, with the roles of `A` and `B` swapped. -/
def ctxtSimExpB (rkem : RKEMScheme ProbComp Par EK DK CT K) {leak : rkem.RandLeak}
    (sim : rkem.RatchetSimulator leak)
    (adversary : CtxtSimAdversary Par EK DK CT K sim.Aux leak.KeygenRand) :
    ProbComp Bool := do
  let b ← $ᵗ Bool
  let par ← rkem.rsetup
  let x ← rkem.ctxtSimDistB sim par b
  let b' ← adversary par x
  return b == b'

/-- `Adv^{CtxtSim-A}`: `|Pr[ctxtSimExpA = true] - 1/2|`. -/
noncomputable def ctxtSimAdvantageA (rkem : RKEMScheme ProbComp Par EK DK CT K)
    {leak : rkem.RandLeak} (sim : rkem.RatchetSimulator leak)
    (adversary : CtxtSimAdversary Par EK DK CT K sim.Aux leak.KeygenRand) : ℝ :=
  |(Pr[= true | rkem.ctxtSimExpA sim adversary]).toReal - 1 / 2|

/-- `Adv^{CtxtSim-B}`: as `ctxtSimAdvantageA`, with the roles of `A` and `B` swapped. -/
noncomputable def ctxtSimAdvantageB (rkem : RKEMScheme ProbComp Par EK DK CT K)
    {leak : rkem.RandLeak} (sim : rkem.RatchetSimulator leak)
    (adversary : CtxtSimAdversary Par EK DK CT K sim.Aux leak.KeygenRand) : ℝ :=
  |(Pr[= true | rkem.ctxtSimExpB sim adversary]).toReal - 1 / 2|

/-- `Adv^{CtxtSim} := max_{P ∈ {A,B}} Adv^{CtxtSim-P}`. -/
noncomputable def ctxtSimAdvantage (rkem : RKEMScheme ProbComp Par EK DK CT K)
    {leak : rkem.RandLeak} (sim : rkem.RatchetSimulator leak)
    (adversaryA adversaryB : CtxtSimAdversary Par EK DK CT K sim.Aux leak.KeygenRand) : ℝ :=
  max (rkem.ctxtSimAdvantageA sim adversaryA) (rkem.ctxtSimAdvantageB sim adversaryB)

/-! ### Ratchet simulatability -/

/-- **Definition 5.5** (Ratchet simulatability). `rkem`, with randomness-leak package `leak`,
is `ε`-ratchet-simulatable via the simulators `sim` against the given distinguishers if
its base-key, updated-key and ciphertext simulatability advantages (each a maximum over both
parties) are all at most `ε`. Asymptotic ratchet simulatability, as stated in
[TripleRatchet], additionally asks for `sim` to be efficient, quantifies over every PPT
distinguisher and requires `ε` to be negligible in the security parameter. -/
-- ANCHOR: RatchetSimulatable
def RatchetSimulatable (rkem : RKEMScheme ProbComp Par EK DK CT K) {leak : rkem.RandLeak}
    (sim : rkem.RatchetSimulator leak)
    (baseA baseB : KeyBaseSimAdversary Par EK DK)
    (updA updB : KeyUpdSimAdversary Par EK DK CT K sim.Aux leak.KeygenRand leak.EncRand)
    (ctxtA ctxtB : CtxtSimAdversary Par EK DK CT K sim.Aux leak.KeygenRand)
    (ε : ℝ) : Prop :=
  rkem.keyBaseSimAdvantage sim baseA baseB ≤ ε ∧
    rkem.keyUpdSimAdvantage sim updA updB ≤ ε ∧
    rkem.ctxtSimAdvantage sim ctxtA ctxtB ≤ ε
-- ANCHOR_END: RatchetSimulatable

end RatchetSimulatability

end RKEMScheme
