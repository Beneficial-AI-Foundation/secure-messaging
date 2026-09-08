/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SecureMessaging.RKEM.Defs
import VCVio.CryptoFoundations.KeyEncapMech

/-!
# Ratcheting Key Encapsulation Mechanism from a Key Encapsulation Mechanism

This file defines the generic construction of an RKEM scheme from a KEM, following
[TripleRatchet, Appendix A.1, Fig. 26].

## Construction

Public parameters are vacuous, and the ratcheting key spaces `EK`/`DK` are just the KEM's
own public/secret key spaces, with the fresh and updated key-generation distributions
coinciding: both are plain KEM key generation.

```
RKeyGen-P(par, mode):
  (ekP, dkP) ← KeyGen()
  return (ekP, dkP)

REnc-P(êkP̄, dkP):                 -- dkP is unused
  (ct, K)     ←$ Enc(êkP̄)
  (êkP, d̂kP)  ←  KeyGen()
  ctP̄        := (êkP, ct)
  return (ctP̄, K, d̂kP)

RDec-P(d̂kP, ctP, ekP̄):            -- ekP̄ input is unused
  parse (êkP̄, ct) ← ctP
  K ← Dec(d̂kP, ct)
  return (K, êkP̄)
```

[REFERENCES]

- [TripleRatchet] Dodis, Jost, Katsumata, Prest, Schmidt.
  *Triple Ratchet: A Bandwidth Efficient Hybrid-Secure Signal Protocol.*
  EUROCRYPT 2025, https://eprint.iacr.org/2025/078.pdf
-/

open KEMScheme

universe u

namespace kemRKEM

/-- Fresh/updated ratcheting key generation for the KEM construction: both distributions
coincide with the underlying KEM's own key generation. -/
def rkeygen {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C) : Unit → m (PK × SK) :=
  fun _ => kem.keygen

/-- KEM-RKEM encapsulation towards a peer's current encapsulation key `ekPeer`.
Encapsulates under `ekPeer`, then independently generates a fresh key pair for the
sender's own next round; the fresh public key is bundled into the ciphertext. The public
parameter and the sender's current decapsulation key are unused. -/
def renc {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C) (_par : Unit) (ekPeer : PK) (_dkSelf : SK) :
    m ((PK × C) × K × SK) := do
  let (ct, key) ← kem.encaps ekPeer
  let (ekSelfHat, dkSelfHat) ← kem.keygen
  return ((ekSelfHat, ct), key, dkSelfHat)

/-- KEM-RKEM decapsulation: parse the peer's freshly bundled public key out of the
ciphertext, decapsulate the underlying KEM ciphertext with the receiver's updated
decapsulation key, and return the peer's new public key as-is. The public parameter and
the `ekPeer` input, the receiver's previously-known peer key, are unused. -/
def rdec {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C) (_par : Unit) (dkSelfHat : SK) (ctSelf : PK × C) (_ekPeer : PK) :
    m (Option (K × PK)) := do
  let (ekPeerHat, ct) := ctSelf
  let res ← kem.decaps dkSelfHat ct
  match res with
  | none => return none
  | some k => return (k, ekPeerHat)

/-- Generic RKEM scheme induced by a KEM ([TripleRatchet, Appendix A.1, Fig. 26]). Public
parameters are vacuous; the ratcheting key spaces are the KEM's own key spaces, with fresh
and updated distributions coinciding; ciphertexts bundle a freshly generated public key
with the underlying KEM ciphertext.

The encapsulation and decapsulation algorithms are the same for `A` and `B`. -/
-- ANCHOR: scheme
def scheme {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C) : RKEMScheme m Unit PK SK (PK × C) K where
  rsetup := pure ()
  rkeygenAFresh := rkeygen kem
  rkeygenAUpdated := rkeygen kem
  rkeygenBFresh := rkeygen kem
  rkeygenBUpdated := rkeygen kem
  rencA := renc kem
  rdecA := rdec kem
  rencB := renc kem
  rdecB := rdec kem
-- ANCHOR_END: scheme

end kemRKEM
