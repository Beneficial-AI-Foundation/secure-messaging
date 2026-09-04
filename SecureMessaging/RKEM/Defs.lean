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
- `rdecA : Par → DK → CT → EK → m (Option (K × EK))`.
  `RDec-A(par, dkA, ctA, ekB) → (K, ek̂B)`: decapsulates `ctA` using `A`'s
  decapsulation key `dkA` and `B`'s encapsulation key `ekB`, producing the
  shared key `K` and `B`'s updated encapsulation key `ek̂B`.
- `rencB : Par → EK → DK → m (CT × K × DK)`, `rdecB : Par → DK → CT → EK → m (Option (K × EK))`.
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
  `B`'s updated encapsulation key. -/
  rdecA : Par → DK → CT → EK → m (Option (K × EK))
  /-- `REnc-B(par, ekA, dkB) → (ctA, K, dk̂B)`: as `rencA`, with the roles of
  `A` and `B` swapped. -/
  rencB : Par → EK → DK → m (CT × K × DK)
  /-- `RDec-B(par, dkB, ctB, ekA) → (K, ek̂A)`: as `rdecA`, with the roles of
  `A` and `B` swapped. -/
  rdecB : Par → DK → CT → EK → m (Option (K × EK))
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
  let res ← rkem.rdecB par dkB ctB ekA
  match res with
  | none => return false
  | some (key', _) => return decide (key = key')

/-- As `correctExpA`, with the roles of `A` and `B` swapped. -/
def correctExpB (rkem : RKEMScheme m Par EK DK CT K) [DecidableEq K] : m Bool := do
  let par ← rkem.rsetup
  let (ekB, dkB) ← rkem.rkeygenBFresh par
  let (ekA, dkA) ← rkem.rkeygenAUpdated par
  let (ctA, key, _) ← rkem.rencB par ekA dkB
  let res ← rkem.rdecA par dkA ctA ekB
  match res with
  | none => return false
  | some (key', _) => return decide (key = key')

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
round of the protocol from `A` towards `B` as in `correctExpA`; `none` if `B`'s decapsulation
fails. -/
def ratchetRoundOutputA (rkem : RKEMScheme m Par EK DK CT K) : m (Option (EK × DK)) := do
  let par ← rkem.rsetup
  let (ekA, dkA) ← rkem.rkeygenAFresh par
  let (ekB, dkB) ← rkem.rkeygenBUpdated par
  let (ctB, _, dkAHat) ← rkem.rencA par ekB dkA
  let res ← rkem.rdecB par dkB ctB ekA
  match res with
  | none => return none
  | some (_, ekAHat) => return some (ekAHat, dkAHat)

/-- As `ratchetRoundOutputA`, with the roles of `A` and `B` swapped. -/
def ratchetRoundOutputB (rkem : RKEMScheme m Par EK DK CT K) : m (Option (EK × DK)) := do
  let par ← rkem.rsetup
  let (ekB, dkB) ← rkem.rkeygenBFresh par
  let (ekA, dkA) ← rkem.rkeygenAUpdated par
  let (ctA, _, dkBHat) ← rkem.rencB par ekA dkB
  let res ← rkem.rdecA par dkA ctA ekB
  match res with
  | none => return none
  | some (_, ekBHat) => return some (ekBHat, dkBHat)

/-- Total-variation distance, under `runtime`, between `ratchetRoundOutputA` and sampling directly
from `distKeyGenAUpdated`. -/
noncomputable def updateKeyDistErrorA (rkem : RKEMScheme m Par EK DK CT K)
    (runtime : ProbCompRuntime m) : ℝ≥0∞ :=
  ‖(SPMF.tvDist (runtime.evalDist rkem.ratchetRoundOutputA)
                (runtime.evalDist (do
                                  let par ← rkem.rsetup
                                  let keys ← rkem.rkeygenAUpdated par
                                  return some keys)))‖ₑ

/-- As `updateKeyDistErrorA`, with the roles of `A` and `B` swapped. -/
noncomputable def updateKeyDistErrorB (rkem : RKEMScheme m Par EK DK CT K)
    (runtime : ProbCompRuntime m) : ℝ≥0∞ :=
  ‖SPMF.tvDist (runtime.evalDist rkem.ratchetRoundOutputB)
               (runtime.evalDist (do
                                  let par ← rkem.rsetup
                                  let keys ← rkem.rkeygenBUpdated par
                                  return some keys))‖ₑ

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
abbrev FSINDCPAAdversary (EK DK CT K : Type) : Type := EK → EK → EK → CT → DK → K → ProbComp Bool

/-- **Definition 5.4** (FS-IND-CPA experiment, party `A`).

```
b ← {0,1}, K1 ← $K,
(ekA, dkA) ← D_RKeyGen-A, (ek̂B, dk̂B) ← D̂_RKeyGen-B,
(ctB, K0, dk̂A) ← REnc-A(par, ek̂B, dkA),
(·, ek̂A) ← RDec-B(par, dk̂B, ctB, ekA),
b' ← A(ekA, ek̂A, ek̂B, ctB, dk̂A, K_b)
```
returning `b = b'`. -/
def securityExpA (rkem : RKEMScheme ProbComp Par EK DK CT K)
    (adversary : FSINDCPAAdversary EK DK CT K) [SampleableType K] : ProbComp Bool := do
  let b ← $ᵗ Bool
  let k1 ← $ᵗ K
  let par ← rkem.rsetup
  let (ekA, dkA) ← rkem.rkeygenAFresh par
  let (ekBHat, dkBHat) ← rkem.rkeygenBUpdated par
  let (ctB, k0, dkAHat) ← rkem.rencA par ekBHat dkA
  let res ← rkem.rdecB par dkBHat ctB ekA
  match res with
  | none => return false
  | some (_, ekAHat) =>
    let b' ← adversary ekA ekAHat ekBHat ctB dkAHat (if b then k1 else k0)
    return b == b'

/-- As `securityExpA`, with the roles of `A` and `B` swapped. -/
def securityExpB (rkem : RKEMScheme ProbComp Par EK DK CT K)
    (adversary : FSINDCPAAdversary EK DK CT K) [SampleableType K] : ProbComp Bool := do
  let b ← $ᵗ Bool
  let k1 ← $ᵗ K
  let par ← rkem.rsetup
  let (ekB, dkB) ← rkem.rkeygenBFresh par
  let (ekAHat, dkAHat) ← rkem.rkeygenAUpdated par
  let (ctA, k0, dkBHat) ← rkem.rencB par ekAHat dkB
  let res ← rkem.rdecA par dkAHat ctA ekB
  match res with
  | none => return false
  | some (_, ekBHat) =>
    let b' ← adversary ekB ekBHat ekAHat ctA dkBHat (if b then k1 else k0)
    return b == b'

/-- `Adv^{FS-IND-CPA-A}`: `|Pr[securityExpA = true] - 1/2|`. -/
noncomputable def fsIndCpaAdvantageA (rkem : RKEMScheme ProbComp Par EK DK CT K)
    (adversary : FSINDCPAAdversary EK DK CT K) [SampleableType K] : ℝ :=
  |(Pr[= true | rkem.securityExpA adversary]).toReal - 1 / 2|

/-- `Adv^{FS-IND-CPA-B}`: as `fsIndCpaAdvantageA`, with the roles of `A` and `B` swapped. -/
noncomputable def fsIndCpaAdvantageB (rkem : RKEMScheme ProbComp Par EK DK CT K)
    (adversary : FSINDCPAAdversary EK DK CT K) [SampleableType K] : ℝ :=
  |(Pr[= true | rkem.securityExpB adversary]).toReal - 1 / 2|

/-- `Adv^{FS-IND-CPA} := max_{P ∈ {A,B}} Adv^{FS-IND-CPA-P}`. -/
noncomputable def fsIndCpaAdvantage (rkem : RKEMScheme ProbComp Par EK DK CT K)
    (adversaryA adversaryB : FSINDCPAAdversary EK DK CT K) [SampleableType K] : ℝ :=
  max (rkem.fsIndCpaAdvantageA adversaryA) (rkem.fsIndCpaAdvantageB adversaryB)

/-- **Definition 5.4** (FS-IND-CPA security). `rkem` is `epsilon`-FS-IND-CPA-secure against
`adversaryA`, `adversaryB` if both per-party advantages are at most `epsilon`. Asymptotic
FS-IND-CPA security, as stated in [TripleRatchet], additionally quantifies this over every PPT
adversary and requires `epsilon` to be negligible in the security parameter. -/
-- ANCHOR: FSINDCPASecure
def FSINDCPASecure (rkem : RKEMScheme ProbComp Par EK DK CT K)
    (adversaryA adversaryB : FSINDCPAAdversary EK DK CT K) (epsilon : ℝ) [SampleableType K] :
    Prop :=
  rkem.fsIndCpaAdvantage adversaryA adversaryB ≤ epsilon
-- ANCHOR_END: FSINDCPASecure

end Security

end RKEMScheme
