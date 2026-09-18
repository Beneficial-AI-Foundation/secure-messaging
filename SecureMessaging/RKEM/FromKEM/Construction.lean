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

P̄ above corresponds to Peer below, while P corresponds to Self. Uses `total`, a witness that
`kem`'s decapsulation is total, so that the construction's own decapsulation can be total too
(`RKEMScheme.rdecA`/`rdecB` never fail). -/
-- ANCHOR: rdec
def rdec {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C) (total : TotalDecaps kem)
    (_par : Unit) (dkSelfHat : SK) (ctSelf : PK × C) (_ekPeer : PK) :
    m (K × PK) := do
  let (ekPeerHat, ct) := ctSelf
  let res ← kem.decaps dkSelfHat ct
  match res with
  | none => let key ← total.decapsTotal dkSelfHat ct
            return (key, ekPeerHat)
  | some key => return (key, ekPeerHat)
-- ANCHOR_END: rdec

def rdec' {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C) (total : TotalDecaps kem)
    (_par : Unit) (dkSelfHat : SK) (ctSelf : PK × C) (_ekPeer : PK) :
    m (K × PK) := do
  let (ekPeerHat, ct) := ctSelf
  let key ← total.decapsTotal dkSelfHat ct
  return (key, ekPeerHat)

/-- `rdec` and `rdec'` compute the same thing: since `kem.decaps` always agrees with
`some <$> total.decapsTotal` (`total.decaps_eq`), the `none` branch of `rdec` — which redundantly
calls `total.decapsTotal` again — is never taken. -/
theorem rdec_eq_rdec' {m : Type → Type u} [Monad m] [LawfulMonad m] {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C) (total : TotalDecaps kem)
    (par : Unit) (dkSelfHat : SK) (ctSelf : PK × C) (ekPeer : PK) :
    rdec kem total par dkSelfHat ctSelf ekPeer = rdec' kem total par dkSelfHat ctSelf ekPeer := by
  unfold rdec rdec'
  simp only [total.decaps_eq, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]

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

end kemRKEM
