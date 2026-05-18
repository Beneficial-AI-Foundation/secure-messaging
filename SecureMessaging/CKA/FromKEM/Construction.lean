/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.Defs
import VCVio.CryptoFoundations.KeyEncapMech

/-!
# Continuous Key Agreement from a Key Encapsulation Mechanism

This file defines the generic construction of a CKA scheme from a KEM, following
[ACD19, Section 4.1.2].

The paper construction is the public-key analogue of the Signal DH ratchet.
The CKA state alternates between:

* a public key, meaning the party is ready to send by encapsulating to that key;
* a secret key, meaning the party is ready to receive by decapsulating the next
  ciphertext.

On send, the party encapsulates under the stored public key to obtain the epoch
key and ciphertext, generates the next KEM key pair, sends the ciphertext
together with the new public key, and stores the new secret key. On receive,
the party decapsulates with the stored secret key, stores the received public
key, and outputs the recovered epoch key.

We use a `structure`, not a typeclass, for the KEM input. A concrete CKA
construction should be passed around explicitly in reductions and game
statements; there is no intended global canonical KEM for a type tuple
`(K, PK, SK, C)`.
-/

open OracleSpec OracleComp ENNReal

universe u

namespace kemCKA

/-- A KEM instance suitable for the current `CKAScheme` API.

VCV-io's `KEMScheme` already gives the mathematical KEM interface:
probabilistic key generation, probabilistic encapsulation, and monadic
decapsulation. The generic CKA interface in `SecureMessaging.CKA.Defs`, however,
has pure receive algorithms:

```
recvA : St -> Rho -> Option (I × St)
recvB : St -> Rho -> Option (I × St)
```

For ordinary KEMs, decapsulation is deterministic. We therefore keep the
upstream VCV-io `KEMScheme` as the source of truth and record a deterministic
decapsulation function together with the compatibility equation saying that the
monadic KEM decapsulation is just `pure` of that function.

This is a local adapter for [ACD19, Section 4.1.2], not a replacement KEM API.
-/
structure KEMForCKA (m : Type → Type u) [Monad m] (K PK SK C : Type) where
  /-- The underlying VCV-io KEM. -/
  toKEM : KEMScheme m K PK SK C
  /-- Deterministic decapsulation used by the pure CKA receive algorithm. -/
  decapsDet : SK → C → Option K
  /-- Compatibility with the monadic decapsulation exposed by `KEMScheme`. -/
  decaps_eq : ∀ sk c, toKEM.decaps sk c = pure (decapsDet sk c)

/-- Phase-tagged CKA state for the KEM construction.

`sendReady pk` means the party is holding the peer's current public key and can
produce the next epoch key by KEM encapsulation. `recvReady sk` means the party
is holding the secret key corresponding to a public key it previously sent and
can receive the next KEM ciphertext.

The tag is mathematically the phase bit of the alternating CKA protocol. It is
preferable to a bare sum `PK ⊕ SK` because it documents the lens-shaped state
update: send consumes a public-key view and produces a secret-key view; receive
consumes a secret-key view and produces a public-key view.
-/
inductive State (PK SK : Type) where
  | sendReady : PK → State PK SK
  | recvReady : SK → State PK SK

/-- CKA messages produced by the KEM construction.

The first component is the KEM ciphertext for the current epoch key. The second
component is the fresh KEM public key that the receiver stores for its next
send, exactly as in [ACD19, Section 4.1.2].
-/
abbrev Message (C PK : Type) := C × PK

/-- Initial shared key material for the KEM construction: a fresh key pair. -/
abbrev InitKey (PK SK : Type) := PK × SK

/-- Initialize the party that sends first with the public half of the initial
KEM key pair. -/
def initA {PK SK : Type} (ik : InitKey PK SK) : State PK SK :=
  .sendReady ik.1

/-- Initialize the party that receives first with the secret half of the initial
KEM key pair. -/
def initB {PK SK : Type} (ik : InitKey PK SK) : State PK SK :=
  .recvReady ik.2

/-- KEM-CKA send algorithm.

From a `sendReady pk` state:

1. encapsulate under `pk`, obtaining ciphertext `c` and epoch key `key`;
2. generate a fresh KEM key pair `(pk', sk')`;
3. send `(c, pk')`;
4. store `sk'`, so the next local action must be receive.

If called in a receive phase, the algorithm returns `none`; the surrounding CKA
game already enforces alternating communication, but this partiality keeps the
state machine total as a Lean function.
-/
def send {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMForCKA m K PK SK C) :
    State PK SK → m (Option (K × Message C PK × State PK SK))
  | .sendReady pk => do
      let (c, key) ← kem.toKEM.encaps pk
      let (pk', sk') ← kem.toKEM.keygen
      return some (key, (c, pk'), .recvReady sk')
  | .recvReady _ => return none

/-- Randomness-leaking KEM-CKA send algorithm.

The paper's CKA game has a bad-randomness oracle for sends. The current VCV-io
`KEMScheme` exposes probabilistic `keygen` and `encaps`, but it does not expose
their random coins as explicit inputs. Therefore the leaked randomness type for
this construction is `Unit`.

Future upstream-style explicit-randomness KEM APIs, for example
`keygenWithRand` and `encapsWithRand`, could replace this `Unit` by the actual
coin type while leaving the CKA game interface intact.
-/
def send_rleak {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMForCKA m K PK SK C) :
    State PK SK → m (Option (K × Message C PK × State PK SK × Unit)) := fun st => do
  match ← send kem st with
  | none => return none
  | some (key, msg, st') => return some (key, msg, st', ())

/-- KEM-CKA receive algorithm.

From a `recvReady sk` state and message `(c, pk')`, decapsulate `c` with `sk`.
If decapsulation succeeds, output the recovered epoch key and store `pk'`, so
the next local action must be send. If decapsulation fails, return `none`.
-/
def recv {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMForCKA m K PK SK C) :
    State PK SK → Message C PK → Option (K × State PK SK)
  | .recvReady sk, (c, pk') =>
      match kem.decapsDet sk c with
      | some key => some (key, .sendReady pk')
      | none => none
  | .sendReady _, _ => none

/-- Generic CKA scheme induced by a KEM.

The type parameters specialize the abstract CKA interface as follows:

* `IK = PK × SK`, the initial KEM key pair;
* `St = kemCKA.State PK SK`, a phase-tagged public/secret key state;
* `I = K`, the KEM shared key used as the CKA epoch key;
* `Rho = C × PK`, a KEM ciphertext plus the next public key;
* `Rand = Unit`, because current VCV-io KEMs do not expose explicit coins.

The send and receive algorithms are the same for A and B; only initialization
differs, with A starting from the public key and B from the secret key.
-/
def scheme {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMForCKA m K PK SK C) :
    CKAScheme m (InitKey PK SK) (State PK SK) K (Message C PK) Unit where
  initKeyGen := kem.toKEM.keygen
  initA := fun ik => return initA ik
  initB := fun ik => return initB ik
  sendA := send kem
  sendA_rleak := send_rleak kem
  recvA := recv kem
  sendB := send kem
  sendB_rleak := send_rleak kem
  recvB := recv kem

end kemCKA

/-- The concrete probabilistic CKA scheme obtained from a probabilistic KEM.

This is the instance used by the existing CKA correctness and security games,
which are currently specialized to `ProbComp`.
-/
abbrev kemCKA {K PK SK C : Type} (kem : kemCKA.KEMForCKA ProbComp K PK SK C) :
    CKAScheme ProbComp (kemCKA.InitKey PK SK) (kemCKA.State PK SK)
      K (kemCKA.Message C PK) Unit :=
  kemCKA.scheme kem
