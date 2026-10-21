/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SecureMessaging.RKEM.FromKEM.Construction
import ToVCVio.CryptoFoundations.KeyEncapMech
import ToVCVio.EvalDist.Monad.Basic
import SecureMessaging.RKEM.RatchetSimulatabilityHelper

/-!
# RKEM from KEM — Ratchet Simulatability

This file proves perfect ratchet simulatability of the RKEM-from-KEM construction
of `SecureMessaging.RKEM.FromKEM.Construction`.

For every KEM `kem` over `ProbComp`, witness `total : kem.TotalDecaps`, and
randomness-leak package `kemLeak : kem.RandLeak`, the construction is perfectly
ratchet simulatable with respect to `randLeak kem total kemLeak`: the real and
simulated distributions coincide in each of the three simulatability games,
for both parties.

This establishes the perfect-simulatability conclusion of [TripleRatchet, Thm. A.2]
using corrected variants of the simulators in [TripleRatchet, Fig. 27], as detailed
below.

## Randomness leakage

Ratchet simulatability (Def. 5.5) hands the distinguisher the coins of fresh key generation and
of `REnc-P`, so it is stated relative to the construction's randomness-leak package `randLeak`
(see `SecureMessaging.RKEM.FromKEM.Construction`), built from a randomness-leak package
`kemLeak` of the underlying KEM.

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

[REFERENCES]

- [TripleRatchet] Dodis, Jost, Katsumata, Prest, Schmidt.
  *Triple Ratchet: A Bandwidth Efficient Hybrid-Secure Signal Protocol.*
  EUROCRYPT 2025, https://eprint.iacr.org/2025/078.pdf
-/

open ToVCVio KEMScheme RKEMScheme

universe u

namespace kemRKEM

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
theorem evalDistEq_keyBaseSimDistA (par : Unit) :
    (scheme kem total).keyBaseSimDistA (ratchetSimulator kem total kemLeak) par true =ᵈ
      (scheme kem total).keyBaseSimDistA (ratchetSimulator kem total kemLeak) par false := by
  simp only [RKEMScheme.keyBaseSimDistA, ratchetSimulator, rsimKey1, scheme, rkeygen,
    ← kemLeak.keygen_fst, bind_assoc, pure_bind, Bool.true_eq_false, ↓reduceIte]
  exact OracleComp.EvalDistEq.bind_const _ _

/-- As `evalDistEq_keyBaseSimDistA`, with the roles of `A` and `B` swapped. -/
theorem evalDistEq_keyBaseSimDistB (par : Unit) :
    (scheme kem total).keyBaseSimDistB (ratchetSimulator kem total kemLeak) par true =ᵈ
      (scheme kem total).keyBaseSimDistB (ratchetSimulator kem total kemLeak) par false :=
  evalDistEq_keyBaseSimDistA kem total kemLeak par

/-- **Updated-key simulatability** ([TripleRatchet, Fig. 11]) is perfect for the simulators of
Fig. 27: the simulated distribution `D^KeyUpdSim_{A,1}` equals the real `D^KeyUpdSim_{A,0}`. -/
theorem evalDistEq_keyUpdSimDistA (par : Unit) :
    (scheme kem total).keyUpdSimDistA (ratchetSimulator kem total kemLeak) par true =ᵈ
      (scheme kem total).keyUpdSimDistA (ratchetSimulator kem total kemLeak) par false := by
  simp only [RKEMScheme.keyUpdSimDistA, ratchetSimulator, rsimKey1, rsimKey2, randLeak,
    rencRleak, scheme, rdec, bind_assoc, pure_bind, Bool.true_eq_false, ↓reduceIte]
  refine EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ =>
    EvalDistEq.bind_right _ fun _ => ?_
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

/-- As `evalDistEq_keyUpdSimDistA`, with the roles of `A` and `B` swapped. -/
theorem evalDistEq_keyUpdSimDistB (par : Unit) :
    (scheme kem total).keyUpdSimDistB (ratchetSimulator kem total kemLeak) par true =ᵈ
      (scheme kem total).keyUpdSimDistB (ratchetSimulator kem total kemLeak) par false :=
  evalDistEq_keyUpdSimDistA kem total kemLeak par

/-- **Ciphertext simulatability** ([TripleRatchet, Fig. 12]) is perfect for the simulators of
Fig. 27: the simulated distribution `D^CtxtSim_{B,1}` equals the real `D^CtxtSim_{B,0}`. -/
theorem evalDistEq_ctxtSimDistB (par : Unit) :
    (scheme kem total).ctxtSimDistB (ratchetSimulator kem total kemLeak) par true =ᵈ
      (scheme kem total).ctxtSimDistB (ratchetSimulator kem total kemLeak) par false := by
  simp only [RKEMScheme.ctxtSimDistB, ratchetSimulator, rsimKey1, rsimCtxt, randLeak,
    renc, scheme, rdec, rkeygen, bind_assoc, pure_bind, Bool.true_eq_false, ↓reduceIte]
  refine EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun k => ?_
  -- Reorder the four draws `g, e, d, h` of the real side into `h, e, g, d`, the simulated order.
  refine (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun (e : C × K) =>
    OracleComp.EvalDistEq.bind_bind_swap (total.decapsTotal k.1.2 e.1) kem.keygen _).trans ?_
  refine (EvalDistEq.bind_right _ fun _ =>
    OracleComp.EvalDistEq.bind_bind_swap (kem.encaps k.1.1) kem.keygen _).trans ?_
  refine (OracleComp.EvalDistEq.bind_bind_swap kem.keygen kem.keygen _).trans ?_
  exact EvalDistEq.bind_right _ fun _ =>
    OracleComp.EvalDistEq.bind_bind_swap kem.keygen (kem.encaps k.1.1) _

/-- As `evalDistEq_ctxtSimDistB`, with the roles of `A` and `B` swapped. -/
theorem evalDistEq_ctxtSimDistA (par : Unit) :
    (scheme kem total).ctxtSimDistA (ratchetSimulator kem total kemLeak) par true =ᵈ
      (scheme kem total).ctxtSimDistA (ratchetSimulator kem total kemLeak) par false :=
  evalDistEq_ctxtSimDistB kem total kemLeak par

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
  RKEMScheme.ratchetSimulatable_zero_of_evalDist_eq _ (ratchetSimulator kem total kemLeak)
    (evalDistEq_keyBaseSimDistA kem total kemLeak) (evalDistEq_keyBaseSimDistB kem total kemLeak)
    (evalDistEq_keyUpdSimDistA kem total kemLeak) (evalDistEq_keyUpdSimDistB kem total kemLeak)
    (evalDistEq_ctxtSimDistA kem total kemLeak) (evalDistEq_ctxtSimDistB kem total kemLeak)

end Simulatability

end kemRKEM
