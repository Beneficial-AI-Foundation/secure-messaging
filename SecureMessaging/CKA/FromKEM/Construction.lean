/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.Defs
import ToVCVio.CryptoFoundations.KeyEncapMech

/-!
# Continuous Key Agreement from a Key Encapsulation Mechanism

This file defines the generic construction of a CKA scheme from a KEM, following
[ACD19, Section 4.1.2]. "From a KEM" means a protocol transformer: given KEM
algorithms, instantiate the abstract `CKAScheme` interface by using KEM
encapsulation as the send step and KEM decapsulation as the receive step.
Here [ACD19] denotes Alwen, Coretti, and Dodis, *The Double Ratchet:
Security Notions, Proofs, and Modularization for the Signal Protocol*.

## Construction

The initial shared key material is one KEM key pair `(pk0, sk0)`. Party A
starts in state `sendReady pk0`, and party B starts in state `recvReady sk0`.
A protocol message is a pair `(c, pk')` of a KEM ciphertext and a fresh KEM
public key, and the epoch key is the KEM shared key. One A-to-B step:

```
Initial shared KEM key pair:

  A: sendReady pk0                      B: recvReady sk0

A sends:
  (c1, I1)    ← Enc(pk0)
  (pk1, sk1)  ← Gen()
  T1          := (c1, pk1)
  A state     := recvReady sk1

              ───────── T1 ─────────▶

B receives:
  parse T1 as (c1, pk1)
  I1          := Dec(sk0, c1)
  B state     := sendReady pk1
```

The construction uses the VCVio KEM interface, augmented with a witness that
the KEM decapsulation computation is represented by a pure deterministic
function (`KEMScheme.DeterministicDecaps`). The randomness leaked by one send
is described by a `KEMScheme.RandLeak` package, with
`KEMScheme.RandLeak.noLeak` covering KEMs that do not expose their coins.
-/

open OracleSpec OracleComp ENNReal KEMScheme

universe u

namespace kemCKA

/-- Phase-tagged CKA state for the KEM construction.

`sendReady pk` means the party holds the peer's current public key, and its
next local action is a send: encapsulate under `pk` to produce the next epoch
key. `recvReady sk` means the party holds the secret key matching the public
key it sent last, and its next local action is a receive: decapsulate the next
KEM ciphertext with `sk`. The constructor names record the phase of the
alternating CKA protocol in the type.
-/
inductive State (PK SK : Type) where
  | sendReady : PK → State PK SK
  | recvReady : SK → State PK SK

/-- CKA messages produced by the KEM construction.

The message contains the KEM ciphertext for the current epoch key and the
fresh KEM public key that the receiver stores for its next send.
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

If called outside the send phase, the algorithm returns `none`; under the
alternating CKA oracles this branch is unreachable for honest executions.
-/
def send {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C)
    (st : State PK SK) :
    m (Option (K × Message C PK × State PK SK)) :=
  match st with
  | .sendReady pk => do
      let (c, key) ← kem.encaps pk
      let (pk', sk') ← kem.keygen
      return some (key, (c, pk'), .recvReady sk')
  | .recvReady _ => return none

/-- Randomness-leaking KEM-CKA send algorithm.

Same state transition as `send`, built from a `RandLeak` package so that the
output also records the randomness of the two randomized KEM calls, as a pair
of type `RandLeak.Rand leak`.
-/
def send_rleak {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C)
    (leak : RandLeak kem)
    (st : State PK SK) :
    m (Option (K × Message C PK × State PK SK × leak.Rand)) :=
  match st with
  | .sendReady pk => do
      let ((c, key), rEnc) ← leak.encaps_rleak pk
      let ((pk', sk'), rKeygen) ← leak.keygen_rleak
      return some (key, (c, pk'), .recvReady sk', (rEnc, rKeygen))
  | .recvReady _ => return none

/-- KEM-CKA receive algorithm.

From a `recvReady sk` state and message `(c, pk')`, decapsulate `c` with `sk`.
If decapsulation succeeds, output the recovered epoch key and store `pk'`, so
the next local action must be send. If decapsulation fails, return `none`.
-/
def recv {m : Type → Type u} [Monad m] {K PK SK C : Type}
    {kem : KEMScheme m K PK SK C}
    (hDet : DeterministicDecaps kem)
    (st : State PK SK) (msg : Message C PK) :
    Option (K × State PK SK) :=
  match st with
  | .recvReady sk =>
      let (c, pk') := msg
      match hDet.decapsDet sk c with
      | some key => some (key, .sendReady pk')
      | none => none
  | .sendReady _ => none

/-- Generic CKA scheme induced by a KEM.

The type parameters specialize the abstract CKA interface as follows:

* `IK = PK × SK`, the initial KEM key pair;
* `St = kemCKA.State PK SK`, a phase-tagged public/secret key state;
* `I = K`, the KEM shared key used as the CKA epoch key;
* `Rho = C × PK`, the protocol-message space;
* `Rand = RandLeak.Rand leak`, the encapsulation and key-generation
  randomness leaked by one send.

The send and receive algorithms are the same for A and B; only initialization
differs, with A starting from the public key and B from the secret key. For a
KEM that does not expose its coins, instantiate `leak` with the trivial
package `RandLeak.noLeak kem`.
-/
-- ANCHOR: scheme
def scheme {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : RandLeak kem) :
    CKAScheme m (InitKey PK SK) (State PK SK) K (Message C PK) leak.Rand where
  initKeyGen := kem.keygen
  initA := fun ik => return initA ik
  initB := fun ik => return initB ik
  sendA := send kem
  sendA_rleak := send_rleak kem leak
  recvA := recv hDet
  sendB := send kem
  sendB_rleak := send_rleak kem leak
  recvB := recv hDet
-- ANCHOR_END: scheme

end kemCKA
