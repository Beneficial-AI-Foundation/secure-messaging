/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SecureMessaging.RKEM.Defs

/-!
# Ratcheting Key Encapsulation Mechanism from Diffie-Hellman

This file defines the non-forward-secure Diffie-Hellman RKEM of [TripleRatchet, Appendix A.3,
Fig. 28], i.e. the figure without its highlighted forward-secure modifications. Plugged into the
generic CKA construction of [TripleRatchet, Section 5.2], it yields the Double Ratchet CKA of
[ACD19] (compare `DDH.ddhCKA`).

## Group setup

As in `DiffieHellman` and `DDH.ddhCKA`, the cyclic group `G = ⟨g⟩` of prime order `q` is modelled
additively as a module `Module F G` over the scalar field `F` (playing `ℤ_q`), with a fixed
generator `gen : G`. The paper's `g^x` is `x • gen` and `Y^x` is `x • Y`.

## Construction

Public parameters are vacuous: the generator `gen` is a parameter of the construction, as for
`DDH.ddhCKA`. Encapsulation keys are group elements, decapsulation keys are scalars, ciphertexts
are empty (the peer already knows the sender's public value `g^x`, which is its encapsulation
key), and shared keys are group elements.

```
RKeyGen-P(par, mode):
  x ←$ ℤ_q
  (ekP, dkP) ← (g^x, x)
  return (ekP, dkP)

REnc-P(êkP̄ := Y, dkP := x):
  ctP̄ := ()                       -- empty ciphertext
  K   := Y^x
  d̂kP := x
  return (ctP̄, K, d̂kP)

RDec-P(d̂kP := x, ctP, ekP̄ := Y):
  K   := Y^x
  êkP̄ := Y
  return (K, êkP̄)
```

The algorithms are the same for `A` and `B`. Encapsulation and decapsulation are deterministic.

## Non-forward-secure shape

This is the non-forward-secure special case of [TripleRatchet, Remark 5.2]: fresh and updated key
generation coincide, `REnc-P` returns its input `dkP` unchanged as `d̂kP`, and `RDec-P` returns
its input `ekP̄` unchanged as `êkP̄`. Fig. 28's forward-secure variant instead sets
`d̂kP := x · H(K)` and `êkP̄ := Y^{H(K)}`.

Consequently the scheme is *not* FS-IND-CPA secure in the sense of
`RKEMScheme.FSINDCPASecure`: that game hands the adversary `d̂kA = x` along with `êkB = Y`, from
which it recomputes `K₀ = Y^x`. [TripleRatchet, Thm. A.4] only claims plain IND-CPA security
under DDH for this variant.

[REFERENCES]

- [TripleRatchet] Dodis, Jost, Katsumata, Prest, Schmidt.
  *Triple Ratchet: A Bandwidth Efficient Hybrid-Secure Signal Protocol.*
  EUROCRYPT 2025, https://eprint.iacr.org/2025/078.pdf
- [ACD19] Alwen, Coretti, Dodis.
  *The Double Ratchet: Security Notions, Proofs, and Modularization for the Signal Protocol.*
  EUROCRYPT 2019, https://eprint.iacr.org/2018/1037.pdf
-/

namespace ddhRKEM

variable {F : Type} [Field F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G]

/-- Fresh/updated ratcheting key generation for the DH construction: both distributions
coincide, sampling `x ←$ F` and returning `(x • gen, x)`.

RKeyGen-P(par, mode):
  x ←$ ℤ_q
  (ekP, dkP) ← (g^x, x)
  return (ekP, dkP)
-/
-- ANCHOR: rkeygen
def rkeygen (gen : G) (_par : Unit) : ProbComp (G × F) := do
  let x ← $ᵗ F
  return (x • gen, x)
-- ANCHOR_END: rkeygen

/-- DH-RKEM encapsulation. The ciphertext is empty, the shared key is `dkSelf • ekPeerHat`, and
the "updated" decapsulation key is `dkSelf` itself.

REnc-P(êkP̄ := Y, dkP := x):
  ctP̄ := ()
  K   := Y^x
  d̂kP := x
  return (ctP̄, K, d̂kP)

P̄ above corresponds to Peer below, while P corresponds to Self. -/
-- ANCHOR: renc
def renc (_par : Unit) (ekPeerHat : G) (dkSelf : F) : ProbComp (Unit × G × F) := do
  let ctPeer := ()
  let key := dkSelf • ekPeerHat
  let dkSelfHat := dkSelf
  return (ctPeer, key, dkSelfHat)
-- ANCHOR_END: renc

/-- DH-RKEM decapsulation. The ciphertext is ignored, the shared key is `dkSelfHat • ekPeer`,
and the "updated" peer encapsulation key is `ekPeer` itself.

RDec-P(d̂kP := x, ctP, ekP̄ := Y):
  K   := Y^x
  êkP̄ := Y
  return (K, êkP̄)

P̄ above corresponds to Peer below, while P corresponds to Self. -/
-- ANCHOR: rdec
def rdec (_par : Unit) (dkSelfHat : F) (_ctSelf : Unit) (ekPeer : G) : ProbComp (G × G) := do
  let key := dkSelfHat • ekPeer
  let ekPeerHat := ekPeer
  return (key, ekPeerHat)
-- ANCHOR_END: rdec

/-- Non-forward-secure Diffie-Hellman RKEM ([TripleRatchet, Appendix A.3, Fig. 28]) over a module
`Module F G` with generator `gen : G`. Public parameters are vacuous; encapsulation keys are group
elements, decapsulation keys are scalars, ciphertexts are empty and shared keys are group
elements. Fresh and updated key generation coincide, and `REnc-P`/`RDec-P` leave the keys
unchanged ([TripleRatchet, Remark 5.2]).

The encapsulation and decapsulation algorithms are the same for `A` and `B`. -/
-- ANCHOR: scheme
def scheme (gen : G) : RKEMScheme ProbComp Unit G F Unit G where
  rsetup := pure ()
  rkeygenAFresh := rkeygen gen
  rkeygenAUpdated := rkeygen gen
  rkeygenBFresh := rkeygen gen
  rkeygenBUpdated := rkeygen gen
  rencA := renc
  rdecA := rdec
  rencB := renc
  rdecB := rdec
-- ANCHOR_END: scheme

end ddhRKEM
