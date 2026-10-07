/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SecureMessaging.RKEM.Defs
import VCVio.CryptoFoundations.KeyEncapMech
import ToVCVio.CryptoFoundations.KeyEncapMech

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

## Randomness leakage

Security notions that expose algorithm coins are stated relative to an `RKEMScheme.RandLeak`
package. `randLeak` builds one for the construction from a `KEMScheme.RandLeak` package
`kemLeak` of the underlying KEM: fresh key generation leaks the KEM key-generation coins, and
`REnc-P`, which runs `Enc` and then `KeyGen`, leaks the pair of their coins
(`KEMScheme.RandLeak.Rand`).

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
-- ANCHOR: rkeygen
def rkeygen {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C) : Unit → m (PK × SK) :=
  fun _ => kem.keygen
-- ANCHOR_END: rkeygen

/-- KEM-RKEM encapsulation:

REnc-P(êkP̄, dkP):                 -- dkP is unused
  (ct, K)     ←$ Enc(êkP̄)
  (êkP, d̂kP)  ←  KeyGen()
  ctP̄        := (êkP, ct)
  return (ctP̄, K, d̂kP)

P̄ above corresponds to Peer below, while P corresponds to Self.
-/
-- ANCHOR: renc
def renc {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C) (_par : Unit) (ekPeer : PK) (_dkSelf : SK) :
    m ((PK × C) × K × SK) := do
  let (ct, key) ← kem.encaps ekPeer
  let (ekSelfHat, dkSelfHat) ← kem.keygen
  return ((ekSelfHat, ct), key, dkSelfHat)
-- ANCHOR_END: renc

/-- KEM-RKEM decapsulation:

RDec-P(d̂kP, ctP, ekP̄):            -- ekP̄ input is unused
  parse (êkP̄, ct) ← ctP
  K ← Dec(d̂kP, ct)
  return (K, êkP̄)

P̄ above corresponds to Peer below, while P corresponds to Self. Goes through `total.decapsTotal`
rather than `kem.decaps` directly, so that the construction's own decapsulation is total too
(`RKEMScheme.rdecA`/`rdecB` never fail) with no `Option` in the data flow to justify away. -/
-- ANCHOR: rdec
def rdec {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C) (total : TotalDecaps kem)
    (_par : Unit) (dkSelfHat : SK) (ctSelf : PK × C) (_ekPeer : PK) :
    m (K × PK) := do
  let (ekPeerHat, ct) := ctSelf
  -- We have that kem.decaps dkSelfHat ct = some <$> decapsTotal dkSelfHat ct
  let key ← total.decapsTotal dkSelfHat ct
  return (key, ekPeerHat)
-- ANCHOR_END: rdec

/-- Generic RKEM scheme induced by a KEM ([TripleRatchet, Appendix A.1, Fig. 26]). Public
parameters are vacuous; the ratcheting key spaces are the KEM's own key spaces, with fresh
and updated distributions coinciding; ciphertexts bundle a freshly generated public key
with the underlying KEM ciphertext. Requires a witness `total` that `kem`'s decapsulation is
total, matching `RKEMScheme`'s decapsulation algorithms, which never fail.

The encapsulation and decapsulation algorithms are the same for `A` and `B`. -/
-- ANCHOR: scheme
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
-- ANCHOR_END: scheme

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

end kemRKEM
