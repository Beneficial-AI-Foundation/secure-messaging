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

[TripleRatchet, Def. 5.5] captures two further properties beyond correctness and FS-IND-CPA
security, needed to prove security of the generic CKA-from-RKEM construction (Thm. 5.6) by
induction over the ping-pong rounds. It asks for simulators, one per party, each with three
components:

* `simKeyP` (`RSimKey-P1` in the paper) witnesses **base-key simulatability**: `P`'s *updated* key
  pair can be produced from a *fresh* key pair alone, with no access to the peer's key material.
  It also outputs auxiliary state consumed by `simRencP`.
* `simRencP` (`RSimKey-P2`) witnesses **updated-key simulatability**: the ciphertext, shared key,
  and "other" key of an honest `P`-towards-peer round — normally computed from `P`'s own fresh
  decapsulation key — can instead be produced from the peer's *simulated* updated key pair and
  `simKeyP`'s auxiliary state alone. This breaks the round's dependence on `P`'s actual fresh
  secret, the key property the CKA induction relies on.
* `simCtxtP` (`RSimCtxt-P`) witnesses **ciphertext simulatability**: the same round's outputs can
  instead be produced *directly from both parties' simulated updated key pairs* (including the
  peer's updated decapsulation key), again without `P`'s fresh decapsulation key. This is what
  lets the CKA proof argue post-compromise security: once `P` refreshes its key, a corrupted
  peer's prior view of `P`'s ciphertexts reveals nothing about `P`'s fresh secret.

Each property is phrased as a `Bool`-guessing advantage between the honest ("real", `b = false`)
and simulated (`b = true`) distribution, in the style of `securityExpA`/`fsIndCpaAdvantageA`.
Unlike [TripleRatchet]'s Figs. 10–12, this formalization does not expose the simulators' internal
random coins to the distinguisher: the paper tracks them explicitly only for its own hybrid-style
proof of Thm. 5.6, not as part of Def. 5.5's mathematical content. A coin-exposing variant (in the
style of `KEMScheme.RandLeak`) can be added later if some proof needs the stronger notion.
-/

section RatchetSimulatability

variable {Par EK DK CT K : Type}

/-- A pair of ratchet simulators (Def. 5.5), one per party. Bundled together (rather than split
per-party) because `keyUpdSimA`/`ctxtSimA` below need both `simKeyA` *and* `simKeyB` at once: the
peer's updated key pair is always produced via the peer's own simulator, even in the "real" world,
so that the only thing being tested is whether *this* party's side can be simulated too. -/
structure RatchetSim (rkem : RKEMScheme ProbComp Par EK DK CT K) where
  /-- Auxiliary state threaded from `simKeyA` into `simRencA`. -/
  AuxA : Type
  /-- Auxiliary state threaded from `simKeyB` into `simRencB`. -/
  AuxB : Type
  /-- `RSimKey-A1`: simulates `A`'s updated key pair from a freshly sampled one, producing the
  auxiliary state `simRencA` needs. -/
  simKeyA : EK → DK → ProbComp (EK × DK × AuxA)
  /-- `RSimKey-A2`: simulates the ciphertext, shared key, and "other" key of an `A`-towards-`B`
  round from `B`'s simulated updated key pair and `simKeyA`'s auxiliary state, without `A`'s fresh
  decapsulation key. -/
  simRencA : EK → DK → AuxA → ProbComp (CT × K × K)
  /-- `RSimCtxt-A`: simulates `A`'s ciphertext, a fresh-looking encapsulation key for `A`, and the
  two keys of an `A`-towards-`B` round directly from both parties' simulated updated key pairs,
  without `A`'s fresh decapsulation key. -/
  simCtxtA : EK → EK → DK → ProbComp (CT × EK × K × K)
  /-- `RSimKey-B1`, as `simKeyA` with the roles of `A` and `B` swapped. -/
  simKeyB : EK → DK → ProbComp (EK × DK × AuxB)
  /-- `RSimKey-B2`, as `simRencA` with the roles of `A` and `B` swapped. -/
  simRencB : EK → DK → AuxB → ProbComp (CT × K × K)
  /-- `RSimCtxt-B`, as `simCtxtA` with the roles of `A` and `B` swapped. -/
  simCtxtB : EK → EK → DK → ProbComp (CT × EK × K × K)

/-- Base-key simulatability distribution (`D^{KeyBaseSim}_{A,b}`, Fig. 10): `b = false` samples
`A`'s updated key pair directly; `b = true` samples a fresh pair and simulates the updated one
from it via `simKeyA`. -/
def keyBaseSimA (rkem : RKEMScheme ProbComp Par EK DK CT K) (sim : RatchetSim rkem) (b : Bool) :
    ProbComp (EK × DK) := do
  let par ← rkem.rsetup
  if b then
    let (ekA, dkA) ← rkem.rkeygenAFresh par
    let (ekAHat, dkAHat, _) ← sim.simKeyA ekA dkA
    return (ekAHat, dkAHat)
  else
    rkem.rkeygenAUpdated par

/-- As `keyBaseSimA`, with the roles of `A` and `B` swapped. -/
def keyBaseSimB (rkem : RKEMScheme ProbComp Par EK DK CT K) (sim : RatchetSim rkem) (b : Bool) :
    ProbComp (EK × DK) := do
  let par ← rkem.rsetup
  if b then
    let (ekB, dkB) ← rkem.rkeygenBFresh par
    let (ekBHat, dkBHat, _) ← sim.simKeyB ekB dkB
    return (ekBHat, dkBHat)
  else
    rkem.rkeygenBUpdated par

/-- Updated-key simulatability distribution (`D^{KeyUpdSim}_{A,b}`, Fig. 11): both worlds first
simulate `B`'s updated key pair from a fresh one via `simKeyB`. `b = false` then runs an honest
`A`-towards-`B` round using `A`'s own fresh key; `b = true` instead simulates `A`'s updated key
pair and the round's outputs via `simKeyA`/`simRencA`, without `A`'s fresh decapsulation key. -/
def keyUpdSimA (rkem : RKEMScheme ProbComp Par EK DK CT K) (sim : RatchetSim rkem) (b : Bool) :
    ProbComp ((EK × DK) × (EK × DK) × CT × K × K) := do
  let par ← rkem.rsetup
  let (ekB, dkB) ← rkem.rkeygenBFresh par
  let (ekBHat, dkBHat, _) ← sim.simKeyB ekB dkB
  let (ekA, dkA) ← rkem.rkeygenAFresh par
  if b then
    let (ekAHat, dkAHat, auxA) ← sim.simKeyA ekA dkA
    let (ctB, key, key') ← sim.simRencA ekBHat dkBHat auxA
    return ((ekBHat, dkBHat), (ekAHat, dkAHat), ctB, key, key')
  else
    let (ctB, key, dkAHat) ← rkem.rencA par ekBHat dkA
    let (key', ekAHat) ← rkem.rdecB par dkBHat ctB ekA
    return ((ekBHat, dkBHat), (ekAHat, dkAHat), ctB, key, key')

/-- As `keyUpdSimA`, with the roles of `A` and `B` swapped. -/
def keyUpdSimB (rkem : RKEMScheme ProbComp Par EK DK CT K) (sim : RatchetSim rkem) (b : Bool) :
    ProbComp ((EK × DK) × (EK × DK) × CT × K × K) := do
  let par ← rkem.rsetup
  let (ekA, dkA) ← rkem.rkeygenAFresh par
  let (ekAHat, dkAHat, _) ← sim.simKeyA ekA dkA
  let (ekB, dkB) ← rkem.rkeygenBFresh par
  if b then
    let (ekBHat, dkBHat, auxB) ← sim.simKeyB ekB dkB
    let (ctA, key, key') ← sim.simRencB ekAHat dkAHat auxB
    return ((ekAHat, dkAHat), (ekBHat, dkBHat), ctA, key, key')
  else
    let (ctA, key, dkBHat) ← rkem.rencB par ekAHat dkB
    let (key', ekBHat) ← rkem.rdecA par dkAHat ctA ekB
    return ((ekAHat, dkAHat), (ekBHat, dkBHat), ctA, key, key')

/-- Ciphertext simulatability distribution (`D^{CtxtSim}_{A,b}`, Fig. 12): both worlds first
simulate `B`'s updated key pair. `b = false` then runs an honest `A`-towards-`B` round using `A`'s
own fresh key, with `B` decapsulating via its simulated key; `b = true` instead samples `A`'s
updated key pair directly and simulates the ciphertext/keys/`A`'s fresh-looking key via
`simCtxtA`, without `A`'s fresh decapsulation key. -/
def ctxtSimA (rkem : RKEMScheme ProbComp Par EK DK CT K) (sim : RatchetSim rkem) (b : Bool) :
    ProbComp ((EK × DK) × CT × (EK × EK) × K × K) := do
  let par ← rkem.rsetup
  let (ekB, dkB) ← rkem.rkeygenBFresh par
  let (ekBHat, dkBHat, _) ← sim.simKeyB ekB dkB
  if b then
    let (ekAHat, _dkAHat) ← rkem.rkeygenAUpdated par
    let (ctB, ekA, key, key') ← sim.simCtxtA ekAHat ekBHat dkBHat
    return ((ekBHat, dkBHat), ctB, (ekA, ekAHat), key, key')
  else
    let (ekA, dkA) ← rkem.rkeygenAFresh par
    let (ctB, key, _dkAHat) ← rkem.rencA par ekBHat dkA
    let (key', ekAHat) ← rkem.rdecB par dkBHat ctB ekA
    return ((ekBHat, dkBHat), ctB, (ekA, ekAHat), key, key')

/-- As `ctxtSimA`, with the roles of `A` and `B` swapped. -/
def ctxtSimB (rkem : RKEMScheme ProbComp Par EK DK CT K) (sim : RatchetSim rkem) (b : Bool) :
    ProbComp ((EK × DK) × CT × (EK × EK) × K × K) := do
  let par ← rkem.rsetup
  let (ekA, dkA) ← rkem.rkeygenAFresh par
  let (ekAHat, dkAHat, _) ← sim.simKeyA ekA dkA
  if b then
    let (ekBHat, _dkBHat) ← rkem.rkeygenBUpdated par
    let (ctA, ekB, key, key') ← sim.simCtxtB ekBHat ekAHat dkAHat
    return ((ekAHat, dkAHat), ctA, (ekB, ekBHat), key, key')
  else
    let (ekB, dkB) ← rkem.rkeygenBFresh par
    let (ctA, key, _dkBHat) ← rkem.rencB par ekAHat dkB
    let (key', ekBHat) ← rkem.rdecA par dkAHat ctA ekB
    return ((ekAHat, dkAHat), ctA, (ekB, ekBHat), key, key')

/-- Advantage of `distinguisher` at telling apart the real (`b = false`) and simulated (`b = true`)
`keyBaseSimA` distributions: `|Pr[b' = true] - 1/2|`, in the style of `fsIndCpaAdvantageA`. -/
noncomputable def keyBaseSimAdvantageA (rkem : RKEMScheme ProbComp Par EK DK CT K)
    (sim : RatchetSim rkem) (distinguisher : EK × DK → ProbComp Bool) : ℝ :=
  |(Pr[= true | do
      let b ← $ᵗ Bool
      let x ← keyBaseSimA rkem sim b
      let b' ← distinguisher x
      pure (b == b')]).toReal - 1 / 2|

/-- As `keyBaseSimAdvantageA`, with the roles of `A` and `B` swapped. -/
noncomputable def keyBaseSimAdvantageB (rkem : RKEMScheme ProbComp Par EK DK CT K)
    (sim : RatchetSim rkem) (distinguisher : EK × DK → ProbComp Bool) : ℝ :=
  |(Pr[= true | do
      let b ← $ᵗ Bool
      let x ← keyBaseSimB rkem sim b
      let b' ← distinguisher x
      pure (b == b')]).toReal - 1 / 2|

/-- `Adv^{KeyBaseSim} := max_{P ∈ {A,B}} Adv^{KeyBaseSim-P}`. -/
noncomputable def keyBaseSimAdvantage (rkem : RKEMScheme ProbComp Par EK DK CT K)
    (sim : RatchetSim rkem) (distinguisherA distinguisherB : EK × DK → ProbComp Bool) : ℝ :=
  max (keyBaseSimAdvantageA rkem sim distinguisherA) (keyBaseSimAdvantageB rkem sim distinguisherB)

/-- Advantage of `distinguisher` at telling apart the real and simulated `keyUpdSimA`
distributions. -/
noncomputable def keyUpdSimAdvantageA (rkem : RKEMScheme ProbComp Par EK DK CT K)
    (sim : RatchetSim rkem)
    (distinguisher : (EK × DK) × (EK × DK) × CT × K × K → ProbComp Bool) : ℝ :=
  |(Pr[= true | do
      let b ← $ᵗ Bool
      let x ← keyUpdSimA rkem sim b
      let b' ← distinguisher x
      pure (b == b')]).toReal - 1 / 2|

/-- As `keyUpdSimAdvantageA`, with the roles of `A` and `B` swapped. -/
noncomputable def keyUpdSimAdvantageB (rkem : RKEMScheme ProbComp Par EK DK CT K)
    (sim : RatchetSim rkem)
    (distinguisher : (EK × DK) × (EK × DK) × CT × K × K → ProbComp Bool) : ℝ :=
  |(Pr[= true | do
      let b ← $ᵗ Bool
      let x ← keyUpdSimB rkem sim b
      let b' ← distinguisher x
      pure (b == b')]).toReal - 1 / 2|

/-- `Adv^{KeyUpdSim} := max_{P ∈ {A,B}} Adv^{KeyUpdSim-P}`. -/
noncomputable def keyUpdSimAdvantage (rkem : RKEMScheme ProbComp Par EK DK CT K)
    (sim : RatchetSim rkem)
    (distinguisherA distinguisherB : (EK × DK) × (EK × DK) × CT × K × K → ProbComp Bool) : ℝ :=
  max (keyUpdSimAdvantageA rkem sim distinguisherA) (keyUpdSimAdvantageB rkem sim distinguisherB)

/-- Advantage of `distinguisher` at telling apart the real and simulated `ctxtSimA`
distributions. -/
noncomputable def ctxtSimAdvantageA (rkem : RKEMScheme ProbComp Par EK DK CT K)
    (sim : RatchetSim rkem)
    (distinguisher : (EK × DK) × CT × (EK × EK) × K × K → ProbComp Bool) : ℝ :=
  |(Pr[= true | do
      let b ← $ᵗ Bool
      let x ← ctxtSimA rkem sim b
      let b' ← distinguisher x
      pure (b == b')]).toReal - 1 / 2|

/-- As `ctxtSimAdvantageA`, with the roles of `A` and `B` swapped. -/
noncomputable def ctxtSimAdvantageB (rkem : RKEMScheme ProbComp Par EK DK CT K)
    (sim : RatchetSim rkem)
    (distinguisher : (EK × DK) × CT × (EK × EK) × K × K → ProbComp Bool) : ℝ :=
  |(Pr[= true | do
      let b ← $ᵗ Bool
      let x ← ctxtSimB rkem sim b
      let b' ← distinguisher x
      pure (b == b')]).toReal - 1 / 2|

/-- `Adv^{CtxtSim} := max_{P ∈ {A,B}} Adv^{CtxtSim-P}`. -/
noncomputable def ctxtSimAdvantage (rkem : RKEMScheme ProbComp Par EK DK CT K)
    (sim : RatchetSim rkem)
    (distinguisherA distinguisherB : (EK × DK) × CT × (EK × EK) × K × K → ProbComp Bool) : ℝ :=
  max (ctxtSimAdvantageA rkem sim distinguisherA) (ctxtSimAdvantageB rkem sim distinguisherB)

/-- **Definition 5.5** (Ratchet Simulatability). `rkem` is
`(epsilonBase, epsilonUpd, epsilonCtxt)`-ratchet-simulatable if there is a simulator pair `sim`
against which every distinguisher's base-key, updated-key, and ciphertext simulatability
advantages are respectively at most `epsilonBase`, `epsilonUpd`, `epsilonCtxt`. Asymptotic ratchet
simulatability, as stated in [TripleRatchet], additionally requires the simulators to be PPT,
quantifies over every PPT distinguisher, and requires the epsilons to be negligible. -/
-- ANCHOR: RatchetSimulatable
def RatchetSimulatable (rkem : RKEMScheme ProbComp Par EK DK CT K)
    (epsilonBase epsilonUpd epsilonCtxt : ℝ) : Prop :=
  ∃ sim : RatchetSim rkem,
    (∀ distinguisherA distinguisherB,
      keyBaseSimAdvantage rkem sim distinguisherA distinguisherB ≤ epsilonBase) ∧
    (∀ distinguisherA distinguisherB,
      keyUpdSimAdvantage rkem sim distinguisherA distinguisherB ≤ epsilonUpd) ∧
    (∀ distinguisherA distinguisherB,
      ctxtSimAdvantage rkem sim distinguisherA distinguisherB ≤ epsilonCtxt)
-- ANCHOR_END: RatchetSimulatable

end RatchetSimulatability

end RKEMScheme
