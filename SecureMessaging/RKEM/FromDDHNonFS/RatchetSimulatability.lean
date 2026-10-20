/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SecureMessaging.RKEM.FromDDHNonFS.Construction
import SecureMessaging.RKEM.RatchetSimulatabilityHelper

/-!
# RKEM from DDH (non-forward-secure) — Ratchet Simulatability

This file proves perfect ratchet simulatability of the non-forward-secure Diffie-Hellman RKEM of
`SecureMessaging.RKEM.FromDDHNonFS.Construction`, the non-forward-secure part of
[TripleRatchet, Thm. A.5]: with respect to `randLeak gen` and the simulators of
[TripleRatchet, Fig. 30], the real and simulated distributions coincide in each of the three
simulatability games, for both parties.

## Randomness leakage

Ratchet simulatability (Def. 5.5) hands the distinguisher the coins of fresh key generation and
of `REnc-P`, so it is stated relative to the construction's randomness-leak package `randLeak`
(see `SecureMessaging.RKEM.FromDDHNonFS.Construction`): the coins of key generation are the
sampled scalar, and those of the deterministic `REnc-P` are empty.

## Simulators

[TripleRatchet, Fig. 30], with `P̄` the peer of `P`:

```
RSimKey-P₁(ekP := X, dkP := x):   RSimKey-P₂(êkP̄ := Y, d̂kP̄ := y, aux₁ := x):
  aux₁ := x                         K := Y^x
  return (x, X, aux₁)               ctP̄ := (); rand₂ := ()
                                    return (ctP̄, K, K, rand₂)

RSimCtxt-P(êkP := X, êkP̄ := Y, d̂kP̄ := y):
  K := X^y
  ctP̄ := ()
  return (ctP̄, X, K, K)
```

The Lean simulators (`rsimKey1`, `rsimKey2`, `rsimCtxt`) follow the figure, except that
`RSimKey-P₁` returns `(êkP, d̂kP, aux₁) = (X, x, x)`, in the order of the `RatchetSimulator` field
(the figure writes `(x, X, aux₁)`).

The simulation is perfect as printed:

- `RSimKey-P₁` returns `P`'s fresh key pair as its updated one, exactly as `REnc-P` and `RDec-P̄`
  do, since the scheme leaves the keys unchanged.
- `RSimKey-P₂` returns `K = Y^x` twice. In the real distribution the peer computes
  `K' = X^y` with `X = g^x` and `Y = g^y`, so `K = K' = g^{xy}`: no correctness assumption is
  needed beyond the keys being honestly generated.
- `RSimCtxt-P` returns `ekP := êkP`. Since the scheme leaves the keys unchanged, `RDec-P̄` returns
  `ekP` as `êkP`, so the two coincide in the real distribution as well, and `K = X^y` is the
  common key `g^{xy}` there.

[REFERENCES]

- [TripleRatchet] Dodis, Jost, Katsumata, Prest, Schmidt.
  *Triple Ratchet: A Bandwidth Efficient Hybrid-Secure Signal Protocol.*
  EUROCRYPT 2025, https://eprint.iacr.org/2025/078.pdf
-/

open ToVCVio RKEMScheme

namespace ddhRKEM

variable {F : Type} [Field F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G]

section Simulators

/-- `RSimKey-P₁` of [TripleRatchet, Fig. 30]:

RSimKey-P₁(ekP := X, dkP := x):
  aux₁ := x
  return (X, x, aux₁)

The simulated updated key pair is `P`'s fresh key pair itself, as in the non-forward-secure
scheme. The figure returns `(x, X, aux₁)`; see the module docstring. -/
-- ANCHOR: rsimKey1
def rsimKey1 (_par : Unit) (ekSelf : G) (dkSelf : F) : ProbComp (G × F × F) := do
  let aux := dkSelf
  return (ekSelf, dkSelf, aux)
-- ANCHOR_END: rsimKey1

/-- `RSimKey-P₂` of [TripleRatchet, Fig. 30]:

RSimKey-P₂(êkP̄ := Y, d̂kP̄ := y, aux₁ := x):   -- d̂kP̄ is unused
  K     := Y^x
  ctP̄  := ()
  rand₂ := ()
  return (ctP̄, K, K, rand₂)

P̄ above corresponds to Peer below, while P corresponds to Self. -/
-- ANCHOR: rsimKey2
def rsimKey2 (_par : Unit) (ekPeerHat : G) (_dkPeerHat : F) (aux : F) :
    ProbComp (Unit × G × G × Unit) := do
  let dkSelf := aux
  let key := dkSelf • ekPeerHat
  let ctPeer := ()
  let rand₂ := ()
  return (ctPeer, key, key, rand₂)
-- ANCHOR_END: rsimKey2

/-- `RSimCtxt-P` of [TripleRatchet, Fig. 30]:

RSimCtxt-P(êkP := X, êkP̄ := Y, d̂kP̄ := y):   -- êkP̄ is unused
  K    := X^y
  ctP̄ := ()
  return (ctP̄, X, K, K)

P̄ above corresponds to Peer below, while P corresponds to Self. -/
-- ANCHOR: rsimCtxt
def rsimCtxt (_par : Unit) (ekSelfHat _ekPeerHat : G) (dkPeerHat : F) :
    ProbComp (Unit × G × G × G) := do
  let key := dkPeerHat • ekSelfHat
  let ctPeer := ()
  return (ctPeer, ekSelfHat, key, key)
-- ANCHOR_END: rsimCtxt

/-- The ratchet simulators of [TripleRatchet, Fig. 30] for the non-forward-secure DH RKEM, with
respect to `randLeak`. The auxiliary state `aux₁ = x` is `P`'s decapsulation key. As for the
construction itself, the simulators are the same for `A` and `B`. -/
-- ANCHOR: ratchetSimulator
def ratchetSimulator (gen : G) : (scheme (F := F) gen).RatchetSimulator (randLeak gen) where
  Aux := F
  rsimKeyA1 := rsimKey1
  rsimKeyA2 := rsimKey2
  rsimCtxtA := rsimCtxt
  rsimKeyB1 := rsimKey1
  rsimKeyB2 := rsimKey2
  rsimCtxtB := rsimCtxt
-- ANCHOR_END: ratchetSimulator

end Simulators

section Simulatability

variable (gen : G)

/-- **Base-key simulatability** ([TripleRatchet, Fig. 10]) is perfect for the simulators of
Fig. 30: the simulated distribution `D^KeyBaseSim_{A,1}` equals the real `D^KeyBaseSim_{A,0}`. -/
theorem evalDist_keyBaseSimDistA (par : Unit) :
    𝒟[(scheme (F := F) gen).keyBaseSimDistA (ratchetSimulator gen) par true] =
      𝒟[(scheme (F := F) gen).keyBaseSimDistA (ratchetSimulator gen) par false] := by
  simp [RKEMScheme.keyBaseSimDistA, ratchetSimulator, rsimKey1, scheme]

/-- As `evalDist_keyBaseSimDistA`, with the roles of `A` and `B` swapped. -/
theorem evalDist_keyBaseSimDistB (par : Unit) :
    𝒟[(scheme (F := F) gen).keyBaseSimDistB (ratchetSimulator gen) par true] =
      𝒟[(scheme (F := F) gen).keyBaseSimDistB (ratchetSimulator gen) par false] :=
  evalDist_keyBaseSimDistA gen par

/-- **Updated-key simulatability** ([TripleRatchet, Fig. 11]) is perfect for the simulators of
Fig. 30: the simulated distribution `D^KeyUpdSim_{A,1}` equals the real `D^KeyUpdSim_{A,0}`. -/
theorem evalDist_keyUpdSimDistA (par : Unit) :
    𝒟[(scheme (F := F) gen).keyUpdSimDistA (ratchetSimulator gen) par true] =
      𝒟[(scheme (F := F) gen).keyUpdSimDistA (ratchetSimulator gen) par false] := by
  simp [RKEMScheme.keyUpdSimDistA, ratchetSimulator, rsimKey1, rsimKey2, randLeak, rencRleak,
    rkeygenRleak, scheme, renc, rdec, smul_smul, mul_comm]

/-- As `evalDist_keyUpdSimDistA`, with the roles of `A` and `B` swapped. -/
theorem evalDist_keyUpdSimDistB (par : Unit) :
    𝒟[(scheme (F := F) gen).keyUpdSimDistB (ratchetSimulator gen) par true] =
      𝒟[(scheme (F := F) gen).keyUpdSimDistB (ratchetSimulator gen) par false] :=
  evalDist_keyUpdSimDistA gen par

/-- **Ciphertext simulatability** ([TripleRatchet, Fig. 12]) is perfect for the simulators of
Fig. 30: the simulated distribution `D^CtxtSim_{B,1}` equals the real `D^CtxtSim_{B,0}`. -/
theorem evalDist_ctxtSimDistB (par : Unit) :
    𝒟[(scheme (F := F) gen).ctxtSimDistB (ratchetSimulator gen) par true] =
      𝒟[(scheme (F := F) gen).ctxtSimDistB (ratchetSimulator gen) par false] := by
  simp [RKEMScheme.ctxtSimDistB, ratchetSimulator, rsimKey1, rsimCtxt, randLeak, rkeygenRleak,
    scheme, rkeygen, renc, rdec, smul_smul, mul_comm]

/-- As `evalDist_ctxtSimDistB`, with the roles of `A` and `B` swapped. -/
theorem evalDist_ctxtSimDistA (par : Unit) :
    𝒟[(scheme (F := F) gen).ctxtSimDistA (ratchetSimulator gen) par true] =
      𝒟[(scheme (F := F) gen).ctxtSimDistA (ratchetSimulator gen) par false] :=
  evalDist_ctxtSimDistB gen par

end Simulatability

/-- **Theorem A.5** ([TripleRatchet]), non-forward-secure part: the non-forward-secure DH RKEM is
perfectly (`ε = 0`) ratchet simulatable (Def. 5.5) with respect to `randLeak`, witnessed by the
simulators `ratchetSimulator` of [TripleRatchet, Fig. 30]. Holds unconditionally. -/
-- ANCHOR: RatchetSimulatable
theorem RatchetSimulatable (gen : G) :
    (scheme (F := F) gen).RatchetSimulatable (leak := randLeak gen) 0
-- ANCHOR_END: RatchetSimulatable
    :=
  RKEMScheme.ratchetSimulatable_zero_of_evalDist_eq _ (ratchetSimulator gen)
    (evalDist_keyBaseSimDistA gen) (evalDist_keyBaseSimDistB gen)
    (evalDist_keyUpdSimDistA gen) (evalDist_keyUpdSimDistB gen)
    (evalDist_ctxtSimDistA gen) (evalDist_ctxtSimDistB gen)

end ddhRKEM
