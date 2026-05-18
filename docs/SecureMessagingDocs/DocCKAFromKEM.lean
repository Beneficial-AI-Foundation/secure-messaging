/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint
import SecureMessaging.CKA.FromKEM.Security
import SecureMessagingDocs.BlueprintTriptych
import SecureMessagingDocs.FreeMonadDiagram

/-!
# Continuous Key Agreement from a KEM

Companion notes for the Lean specification in
`SecureMessaging.CKA.FromKEM`.
-/

open Verso.Genre Manual
open Informal

#doc (Manual) "Continuous Key Agreement from a KEM" =>
%%%
tag := "cka_from_kem"
%%%

:::group "cka_from_kem"
The CKA-from-KEM specification from the Double Ratchet paper, Section 4.1.2.
:::

# What CKA Formalizes

Continuous key agreement, or CKA, is the public-key ratchet component of a
secure messaging protocol. Two parties alternate sending and receiving. Each
send produces a fresh epoch key and a public message; the matching receive
recovers the same epoch key and updates the receiver's state.

The security game in this project is passive and synchronous. The adversary can
ask the honest send and receive oracles to advance the alternating transcript,
can challenge one fixed epoch key, and can corrupt states or leak send
randomness only outside the challenge window. It cannot reorder, drop, or
modify messages.

The Lean interface is:

```
CKAScheme m IK St I Rho Rand
```

Here `IK` is initial shared key material, `St` is a party's local state, `I` is
an epoch key, `Rho` is a protocol message, and `Rand` is the send randomness
exposed by the randomness-leak oracle. The existing games in
`SecureMessaging.CKA.Defs` interpret adversaries as `OracleComp` programs over
typed oracle specs.

# Forward Secrecy and PCS

Forward secrecy, abbreviated FS, says that a state compromise now should not
reveal sufficiently old epoch keys. In the CKA game this delay is `DeltaFS`.
The generic KEM construction is stated with `DeltaFS = 0`: immediately after
the challenged send is past, later state exposure should not reveal that
challenged key.

Post-compromise security, abbreviated PCS, says that after a state compromise,
fresh honest communication should heal the ratchet. The paper's surrounding
CKA game excludes corruptions and bad-randomness leakage less than two epochs
before the challenge. The Lean predicate
`kemCKA.AdmissibleParams` records this as `2 <= DeltaPCS`.

# Diffie-Hellman and DDH

The Diffie-Hellman ratchet is the classical CKA construction used in Signal.
Textbooks often write a cyclic group multiplicatively, with generator `g` and
public values `g^a`, `g^b`. The shared secret is `(g^a)^b = (g^b)^a = g^(ab)`.

The Lean DDH construction in this repository uses additive/module notation:
there is a scalar field `F`, an additive group or module `G`, a generator
`gen : G`, and public values `a • gen`. The shared secret is
`b • (a • gen) = a • (b • gen)`.

The decisional Diffie-Hellman assumption, DDH, says that an adversary cannot
distinguish a real tuple

```
(gen, a • gen, b • gen, (a*b) • gen)
```

from a tuple where the last component is sampled independently. DDH is the
assumption behind the `SecureMessaging.CKA.FromDDH` construction. The KEM-based
construction in this chapter abstracts away from groups and scalars: it only
requires the key encapsulation interface.

# KEM and IND-CPA

A key encapsulation mechanism, or KEM, consists of:

```
keygen : m (PK × SK)
encaps : PK -> m (C × K)
decaps : SK -> C -> m (Option K)
```

`keygen` creates a public/secret key pair. `encaps pk` creates a ciphertext and
a fresh shared key for the holder of `pk`. `decaps sk c` recovers that shared
key, or fails.

IND-CPA security for a KEM is a real-or-random challenge. The adversary sees a
public key, then a challenge ciphertext and either the real encapsulated key or
a uniformly random key. It must guess which branch it is in. There is no
decapsulation oracle. This is the right assumption for the passive CKA model
used here: the CKA adversary sees honest messages and can corrupt states only
outside the challenge window, but it does not get chosen-ciphertext access.

# The KEM-to-CKA Construction

The Double Ratchet paper's Section 4.1.2 construction is:

```
initKeyGen:
  (pk0, sk0) <- KEM.keygen

initA(pk0, sk0):
  state := sendReady pk0

initB(pk0, sk0):
  state := recvReady sk0

send(sendReady pk):
  (c, key)   <- KEM.encaps pk
  (pk', sk') <- KEM.keygen
  message    := (c, pk')
  state'     := recvReady sk'
  output (key, message, state')

recv(recvReady sk, (c, pk')):
  key <- KEM.decaps sk c
  state' := sendReady pk'
  output (key, state')
```

The Lean state is phase-tagged:

```
inductive kemCKA.State (PK SK : Type) where
  | sendReady : PK -> State PK SK
  | recvReady : SK -> State PK SK
```

This tag is not cosmetic. It is the finite state machine of the ratchet. Send
uses the public-key view and returns a secret-key view; receive uses the
secret-key view and returns a public-key view. That is the state-update lens
that makes the alternating protocol readable in Lean.

# The Decapsulation Adapter

The generic `CKAScheme` interface has pure receive functions, while VCV-io's
`KEMScheme.decaps` is monadic. For ordinary KEMs, decapsulation is
deterministic, so the construction uses:

```
structure kemCKA.KEMForCKA (m : Type -> Type) [Monad m] (K PK SK C : Type) where
  toKEM : KEMScheme m K PK SK C
  decapsDet : SK -> C -> Option K
  decaps_eq : forall sk c, toKEM.decaps sk c = pure (decapsDet sk c)
```

This adapter is local to the CKA construction. It keeps the existing VCV-io KEM
API as the source of truth and avoids changing the shared CKA games in this PR.

# Randomness Leakage

The paper's CKA security game includes bad-randomness leakage for sends. The
current VCV-io KEM interface exposes probabilistic `keygen` and `encaps`, but
not explicit random coins. The KEM construction therefore instantiates
`Rand = Unit`.

This means the randomness-leak oracle is still present in the CKA game, but for
this construction it leaks no concrete coin value. A future explicit-randomness
KEM API, with operations such as `keygenWithRand` and `encapsWithRand`, could
replace `Unit` by the actual coin type without changing the surrounding CKA
oracle interface.

# VCV-io and the Poly Lens

VCV-io represents oracle syntax by a dependent family:

```
OracleSpec iota := iota -> Type
```

Mathematically, this is a polynomial signature

```
P(X) = sum (q : Q), X^(R q)
```

where `q` is an oracle query shape and `R q` is its response type. An adversary
is an `OracleComp` over that signature, i.e. the free monad of adaptive oracle
programs. A game supplies a `QueryImpl`, which is the interpreter for each
primitive query.

For CKA, the oracle polynomial contains send, receive, challenge, corrupt, and
randomness-leak query shapes. The KEM construction does not need a new
polynomial layer: it simply instantiates the generic CKA oracle polynomial with

```
St   = kemCKA.State PK SK
Rho  = C × PK
I    = K
Rand = Unit
```

The Poly viewpoint is useful here because it separates the interface shape
from the state-transforming semantics. The adversary only sees the oracle
polynomial; the KEM-to-CKA construction supplies one concrete interpreter of
that polynomial.

# Formal Statements

The Lean files provide:

```
kemCKA.scheme
kemCKA.correctness
kemCKA.AdmissibleParams
kemCKA.security_reduces_to_ind_cpa
```

`kemCKA.correctness` states that KEM perfect correctness implies probability-1
success in the CKA correctness experiment.

`kemCKA.security_reduces_to_ind_cpa` states that, for admissible challenge
parameters, every CKA adversary induces an IND-CPA adversary against the
underlying KEM whose advantage upper-bounds the CKA advantage. The theorem body
is intentionally `sorry`: constructing and proving the reduction is future
proof work, not part of the Issue #3 spec PR.
