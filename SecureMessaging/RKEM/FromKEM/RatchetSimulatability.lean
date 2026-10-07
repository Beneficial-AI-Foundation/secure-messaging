/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SecureMessaging.RKEM.FromKEM.Construction
import ToVCVio.CryptoFoundations.KeyEncapMech
import ToVCVio.EvalDist.Monad.Basic
import ToVCVio.OracleComp.Constructions.SampleableType

/-!
# RKEM from KEM — Ratchet Simulatability

This file states `RKEMScheme.RatchetSimulatable` for the generic RKEM-from-KEM construction of
`SecureMessaging.RKEM.FromKEM.Construction`, matching [TripleRatchet, Thm. A.2]: the construction
of [TripleRatchet, Fig. 26] is *perfectly* ratchet simulatable (advantage `0` against every
distinguisher) using the simulators of [TripleRatchet, Fig. 27].

## Randomness leakage

Ratchet simulatability (Def. 5.5) hands the distinguisher the coins of fresh key generation and
of `REnc-P`, so it is stated relative to an `RKEMScheme.RandLeak` package. For the construction,
`randLeak` builds one from a `KEMScheme.RandLeak` package `kemLeak` of the underlying KEM: fresh
key generation leaks the KEM key-generation coins, and `REnc-P`, which runs `Enc` and then
`KeyGen`, leaks the pair of their coins (`KEMScheme.RandLeak.Rand`).

## Simulators

[TripleRatchet, Fig. 27], with `P̄` the peer of `P`:

```
RSimKey-P₁(ekP, dkP):             RSimKey-P₂(êkP̄, d̂kP̄, aux₁):      RSimCtxt-P(êkP, êkP̄, d̂kP̄):
  (d̂kP, êkP) ← KeyGen(1^λ; rand)    parse (êkP, rand) ← aux₁          (ct, K) ←$ Enc(êkP̄)
  aux₁ := (êkP, rand)               (ct, K) ← Enc(êkP̄; rand')          K' ← Dec(d̂kP̄, ct)
  return (d̂kP, êkP, aux₂)           K' ← Dec(d̂kP̄, ct)                 ctP̄ := (êkP, ct)
                                    ctP̄ := (êkP, ct)                    ekP := êkP
                                    rand₂ := (aux₁, rand')              return (ctP̄, ekP, K, K')
                                    return (ctP̄, K, K, rand₂)
```

The Lean simulators (`rsimKey1`, `rsimKey2`, `rsimCtxt`) follow the figure, with the following
adjustments, each needed for the simulation to be perfect in the Lean model:

- `RSimKey-P₁` returns `(êkP, d̂kP, aux₁)`, in the order and with the `aux₁` of the
  `RatchetSimulator` field (the figure writes `(d̂kP, êkP, aux₂)`).
- `RSimKey-P₂` returns `(ctP̄, K, K', rand₂)`, where `K'` is the decapsulated key of its line 3
  (the figure returns `K` twice, which would need a perfectly correct KEM), and
  `rand₂ := (rand', rand)` is exactly the coin pair `REnc-P` leaks (the figure also includes
  `êkP`, which `rand` already determines).
- `RSimCtxt-P` samples `ekP` as a fresh KEM public key instead of setting `ekP := êkP`: in the
  real distribution `D^CtxtSim_{P,0}` (Fig. 12) `ekP` is a fresh key independent of `êkP`, so a
  distinguisher testing `ekP = êkP` would otherwise succeed for any KEM whose public key is not
  deterministic.

Decapsulation `Dec` is `total.decapsTotal`, as in the construction's own `rdec`.

## Results

`evalDist_keyBaseSimDistA`, `evalDist_keyUpdSimDistA` and `evalDist_ctxtSimDistB` (and their
role-swapped versions) say that the real and simulated distributions of
[TripleRatchet, Figs. 10–12] coincide; every advantage is then `0`, and `RatchetSimulatable`
follows. The only assumption on the KEM is that its decapsulation is total (`TotalDecaps`),
which the construction itself already requires; no correctness or security assumption is needed.

[REFERENCES]

- [TripleRatchet] Dodis, Jost, Katsumata, Prest, Schmidt.
  *Triple Ratchet: A Bandwidth Efficient Hybrid-Secure Signal Protocol.*
  EUROCRYPT 2025, https://eprint.iacr.org/2025/078.pdf
-/

open ToVCVio KEMScheme RKEMScheme

universe u

namespace kemRKEM

section RandLeak

variable {m : Type → Type u} [Monad m] [LawfulMonad m] {K PK SK C : Type}

/-- KEM-RKEM encapsulation `REnc-P` (`renc`), also returning its coins: the coins of the KEM
encapsulation `Enc(êkP̄)` followed by those of the fresh key generation `KeyGen()`.

P̄ above corresponds to Peer below, while P corresponds to Self. -/
-- ANCHOR: rencRleak
def rencRleak {kem : KEMScheme m K PK SK C} (kemLeak : kem.RandLeak) (_par : Unit)
    (ekPeer : PK) (_dkSelf : SK) : m (((PK × C) × K × SK) × kemLeak.Rand) := do
  let ((ct, key), encRand) ← kemLeak.encapsRleak ekPeer
  let ((ekSelfHat, dkSelfHat), keygenRand) ← kemLeak.keygenRleak
  return (((ekSelfHat, ct), key, dkSelfHat), (encRand, keygenRand))
-- ANCHOR_END: rencRleak

/-- `renc` is the first component of `rencRleak`, by the `_fst` laws of `kemLeak`. -/
theorem rencRleak_fst {kem : KEMScheme m K PK SK C} (kemLeak : kem.RandLeak) (par : Unit)
    (ekPeer : PK) (dkSelf : SK) :
    (do
      let out ← rencRleak kemLeak par ekPeer dkSelf
      pure out.1) = renc kem par ekPeer dkSelf := by
  simp only [rencRleak, renc, ← kemLeak.encaps_fst, ← kemLeak.keygen_fst, bind_assoc, pure_bind]

/-- Randomness-leak package of the RKEM-from-KEM construction, built from a randomness-leak
package `kemLeak` of the underlying KEM. Fresh key generation `RKeyGen-P(par, ⊥)` is KEM key
generation and leaks its coins; `REnc-P` leaks the coins of its KEM encapsulation and of its
fresh key generation (`rencRleak`). As for the construction itself, both parties coincide. -/
-- ANCHOR: randLeak
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
-- ANCHOR_END: randLeak

end RandLeak

section Simulators

variable {K PK SK C : Type}

/-- `RSimKey-P₁` of [TripleRatchet, Fig. 27]:

RSimKey-P₁(ekP, dkP):             -- ekP, dkP are unused
  (êkP, d̂kP) ← KeyGen(1^λ; rand)
  aux₁       := (êkP, rand)
  return (êkP, d̂kP, aux₁)

The simulated updated key pair is a fresh KEM key pair, as `REnc-P` itself would produce. -/
-- ANCHOR: rsimKey1
def rsimKey1 {kem : KEMScheme ProbComp K PK SK C} (kemLeak : kem.RandLeak) (_par : Unit)
    (_ekSelf : PK) (_dkSelf : SK) : ProbComp (PK × SK × (PK × kemLeak.KeygenRand)) := do
  let ((ekSelfHat, dkSelfHat), rand) ← kemLeak.keygenRleak
  return (ekSelfHat, dkSelfHat, (ekSelfHat, rand))
-- ANCHOR_END: rsimKey1

/-- `RSimKey-P₂` of [TripleRatchet, Fig. 27]:

RSimKey-P₂(êkP̄, d̂kP̄, aux₁):
  parse (êkP, rand) ← aux₁
  (ct, K)  ← Enc(êkP̄; rand')
  K'       ← Dec(d̂kP̄, ct)
  ctP̄     := (êkP, ct)
  rand₂    := (rand', rand)
  return (ctP̄, K, K', rand₂)

P̄ above corresponds to Peer below, while P corresponds to Self. The figure returns `K` in
place of `K'` and sets `rand₂ := (aux₁, rand')`; see the module docstring. -/
-- ANCHOR: rsimKey2
def rsimKey2 {kem : KEMScheme ProbComp K PK SK C} (total : TotalDecaps kem)
    (kemLeak : kem.RandLeak) (_par : Unit) (ekPeerHat : PK) (dkPeerHat : SK)
    (aux : PK × kemLeak.KeygenRand) : ProbComp ((PK × C) × K × K × kemLeak.Rand) := do
  let (ekSelfHat, rand) := aux
  let ((ct, key), rand') ← kemLeak.encapsRleak ekPeerHat
  let key' ← total.decapsTotal dkPeerHat ct
  return ((ekSelfHat, ct), key, key', (rand', rand))
-- ANCHOR_END: rsimKey2

/-- `RSimCtxt-P` of [TripleRatchet, Fig. 27]:

RSimCtxt-P(êkP, êkP̄, d̂kP̄):
  (ct, K)  ←$ Enc(êkP̄)
  K'       ←  Dec(d̂kP̄, ct)
  ctP̄     :=  (êkP, ct)
  (ekP, ·) ←  KeyGen(1^λ)
  return (ctP̄, ekP, K, K')

P̄ above corresponds to Peer below, while P corresponds to Self. The figure sets
`ekP := êkP` instead of sampling a fresh `ekP`; see the module docstring. -/
-- ANCHOR: rsimCtxt
def rsimCtxt (kem : KEMScheme ProbComp K PK SK C) (total : TotalDecaps kem) (_par : Unit)
    (ekSelfHat ekPeerHat : PK) (dkPeerHat : SK) : ProbComp ((PK × C) × PK × K × K) := do
  let (ct, key) ← kem.encaps ekPeerHat
  let key' ← total.decapsTotal dkPeerHat ct
  let (ekSelf, _) ← kem.keygen
  return ((ekSelfHat, ct), ekSelf, key, key')
-- ANCHOR_END: rsimCtxt

/-- The ratchet simulators of [TripleRatchet, Fig. 27] for the RKEM-from-KEM construction, with
respect to `randLeak`. The auxiliary state `aux₁ = (êkP, rand)` is the simulated updated
encapsulation key and its key-generation coins. As for the construction itself, the simulators
are the same for `A` and `B`. -/
-- ANCHOR: ratchetSimulator
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
-- ANCHOR_END: ratchetSimulator

end Simulators

section Simulatability

variable {K PK SK C : Type}

variable (kem : KEMScheme ProbComp K PK SK C) (total : TotalDecaps kem) (kemLeak : kem.RandLeak)

/-- **Base-key simulatability** ([TripleRatchet, Fig. 10]) is perfect for the simulators of
Fig. 27: the simulated distribution `D^KeyBaseSim_{A,1}` equals the real `D^KeyBaseSim_{A,0}`. -/
theorem evalDist_keyBaseSimDistA (par : Unit) :
    𝒟[(scheme kem total).keyBaseSimDistA (ratchetSimulator kem total kemLeak) par true] =
      𝒟[(scheme kem total).keyBaseSimDistA (ratchetSimulator kem total kemLeak) par false] := by
  simp only [RKEMScheme.keyBaseSimDistA, ratchetSimulator, rsimKey1, scheme, rkeygen,
    ← kemLeak.keygen_fst, bind_assoc, pure_bind, Bool.true_eq_false, ↓reduceIte]
  refine evalDist_ext fun y => ?_
  refine probOutput_bind_of_const' _ fun _ _ => ?_
  rfl

/-- As `evalDist_keyBaseSimDistA`, with the roles of `A` and `B` swapped. -/
theorem evalDist_keyBaseSimDistB (par : Unit) :
    𝒟[(scheme kem total).keyBaseSimDistB (ratchetSimulator kem total kemLeak) par true] =
      𝒟[(scheme kem total).keyBaseSimDistB (ratchetSimulator kem total kemLeak) par false] :=
  evalDist_keyBaseSimDistA kem total kemLeak par

/-- **Updated-key simulatability** ([TripleRatchet, Fig. 11]) is perfect for the simulators of
Fig. 27: the simulated distribution `D^KeyUpdSim_{A,1}` equals the real `D^KeyUpdSim_{A,0}`. -/
theorem evalDist_keyUpdSimDistA (par : Unit) :
    𝒟[(scheme kem total).keyUpdSimDistA (ratchetSimulator kem total kemLeak) par true] =
      𝒟[(scheme kem total).keyUpdSimDistA (ratchetSimulator kem total kemLeak) par false] := by
  simp only [RKEMScheme.keyUpdSimDistA, ratchetSimulator, rsimKey1, rsimKey2, randLeak,
    rencRleak, scheme, rdec, bind_assoc, pure_bind, Bool.true_eq_false, ↓reduceIte]
  refine evalDist_ext fun y => ?_
  refine probOutput_bind_congr fun p _ => ?_
  refine probOutput_bind_congr fun q _ => ?_
  refine probOutput_bind_congr fun r _ => ?_
  rw [probOutput_bind_bind_swap]

/-- As `evalDist_keyUpdSimDistA`, with the roles of `A` and `B` swapped. -/
theorem evalDist_keyUpdSimDistB (par : Unit) :
    𝒟[(scheme kem total).keyUpdSimDistB (ratchetSimulator kem total kemLeak) par true] =
      𝒟[(scheme kem total).keyUpdSimDistB (ratchetSimulator kem total kemLeak) par false] :=
  evalDist_keyUpdSimDistA kem total kemLeak par

/-- **Ciphertext simulatability** ([TripleRatchet, Fig. 12]) is perfect for the simulators of
Fig. 27: the simulated distribution `D^CtxtSim_{B,1}` equals the real `D^CtxtSim_{B,0}`. -/
theorem evalDist_ctxtSimDistB (par : Unit) :
    𝒟[(scheme kem total).ctxtSimDistB (ratchetSimulator kem total kemLeak) par true] =
      𝒟[(scheme kem total).ctxtSimDistB (ratchetSimulator kem total kemLeak) par false] := by
  simp only [RKEMScheme.ctxtSimDistB, ratchetSimulator, rsimKey1, rsimCtxt, randLeak,
    renc, scheme, rdec, rkeygen, bind_assoc, pure_bind, Bool.true_eq_false, ↓reduceIte]
  refine evalDist_ext fun y => ?_
  refine probOutput_bind_congr fun p _ => ?_
  refine probOutput_bind_congr fun q _ => ?_
  refine (probOutput_bind_congr fun k1 _ => (probOutput_bind_congr fun e _ =>
    probOutput_bind_bind_swap _ _ _ _).trans (probOutput_bind_bind_swap _ _ _ _)).trans ?_
  refine (probOutput_bind_bind_swap _ _ _ _).trans ?_
  refine (probOutput_bind_congr fun k1 _ => probOutput_bind_bind_swap _ _ _ _).symm.trans ?_
  rfl

/-- As `evalDist_ctxtSimDistB`, with the roles of `A` and `B` swapped. -/
theorem evalDist_ctxtSimDistA (par : Unit) :
    𝒟[(scheme kem total).ctxtSimDistA (ratchetSimulator kem total kemLeak) par true] =
      𝒟[(scheme kem total).ctxtSimDistA (ratchetSimulator kem total kemLeak) par false] :=
  evalDist_ctxtSimDistB kem total kemLeak par

/-- `Adv^{KeyBaseSim}` of the simulators of [TripleRatchet, Fig. 27] is `0`, against every pair
of distinguishers. -/
theorem keyBaseSimAdvantage_eq_zero (adversaryA adversaryB : KeyBaseSimAdversary Unit PK SK) :
    (scheme kem total).keyBaseSimAdvantage (ratchetSimulator kem total kemLeak)
      adversaryA adversaryB = 0 := by
  unfold RKEMScheme.keyBaseSimAdvantage RKEMScheme.keyBaseSimAdvantageA
    RKEMScheme.keyBaseSimAdvantageB RKEMScheme.keyBaseSimExpA RKEMScheme.keyBaseSimExpB
  rw [probOutput_true_bitGuess_eq_half _ _ _ (evalDist_keyBaseSimDistA kem total kemLeak),
    probOutput_true_bitGuess_eq_half _ _ _ (evalDist_keyBaseSimDistB kem total kemLeak)]
  simp

/-- `Adv^{KeyUpdSim}` of the simulators of [TripleRatchet, Fig. 27] is `0`, against every pair
of distinguishers. -/
theorem keyUpdSimAdvantage_eq_zero
    (adversaryA adversaryB : KeyUpdSimAdversary Unit PK SK (PK × C) K
      (ratchetSimulator kem total kemLeak).Aux (randLeak kem total kemLeak).KeygenRand
      (randLeak kem total kemLeak).EncRand) :
    (scheme kem total).keyUpdSimAdvantage (ratchetSimulator kem total kemLeak)
      adversaryA adversaryB = 0 := by
  unfold RKEMScheme.keyUpdSimAdvantage RKEMScheme.keyUpdSimAdvantageA
    RKEMScheme.keyUpdSimAdvantageB RKEMScheme.keyUpdSimExpA RKEMScheme.keyUpdSimExpB
  rw [probOutput_true_bitGuess_eq_half _ _ _ (evalDist_keyUpdSimDistA kem total kemLeak),
    probOutput_true_bitGuess_eq_half _ _ _ (evalDist_keyUpdSimDistB kem total kemLeak)]
  simp

/-- `Adv^{CtxtSim}` of the simulators of [TripleRatchet, Fig. 27] is `0`, against every pair of
distinguishers. -/
theorem ctxtSimAdvantage_eq_zero
    (adversaryA adversaryB : CtxtSimAdversary Unit PK SK (PK × C) K
      (ratchetSimulator kem total kemLeak).Aux (randLeak kem total kemLeak).KeygenRand) :
    (scheme kem total).ctxtSimAdvantage (ratchetSimulator kem total kemLeak)
      adversaryA adversaryB = 0 := by
  unfold RKEMScheme.ctxtSimAdvantage RKEMScheme.ctxtSimAdvantageA
    RKEMScheme.ctxtSimAdvantageB RKEMScheme.ctxtSimExpA RKEMScheme.ctxtSimExpB
  rw [probOutput_true_bitGuess_eq_half _ _ _ (evalDist_ctxtSimDistA kem total kemLeak),
    probOutput_true_bitGuess_eq_half _ _ _ (evalDist_ctxtSimDistB kem total kemLeak)]
  simp

/-- **Theorem A.2** ([TripleRatchet]) of the RKEM-from-KEM construction: it is perfectly
(`ε = 0`) ratchet simulatable (Def. 5.5) with respect to `randLeak`, witnessed by the simulators
`ratchetSimulator` of [TripleRatchet, Fig. 27]. Holds for any KEM with total decapsulation
(`total`, already required by the construction), with no correctness or security assumption. -/
-- ANCHOR: RatchetSimulatable
theorem RatchetSimulatable (kem : KEMScheme ProbComp K PK SK C) (total : TotalDecaps kem)
    (kemLeak : kem.RandLeak) :
    (scheme kem total).RatchetSimulatable (leak := randLeak kem total kemLeak) 0
-- ANCHOR_END: RatchetSimulatable
    :=
  ⟨ratchetSimulator kem total kemLeak, fun baseA baseB updA updB ctxtA ctxtB =>
    ⟨(keyBaseSimAdvantage_eq_zero kem total kemLeak baseA baseB).le,
      (keyUpdSimAdvantage_eq_zero kem total kemLeak updA updB).le,
      (ctxtSimAdvantage_eq_zero kem total kemLeak ctxtA ctxtB).le⟩⟩

end Simulatability

end kemRKEM
