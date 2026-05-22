/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.Defs
import VCVio.CryptoFoundations.KeyEncapMech

/-!
# Continuous Key Agreement from a Key Encapsulation Mechanism

This file defines the generic construction of a CKA scheme from a KEM, following
[ACD19, Section 4.1.2]. "From a KEM" means a protocol transformer: given KEM
algorithms, instantiate the abstract `CKAScheme` interface by using KEM
encapsulation as the send step and KEM decapsulation as the receive step.
Here [ACD19] denotes Alwen, Coretti, and Dodis, *The Double Ratchet:
Security Notions, Proofs, and Modularization for the Signal Protocol*.

## Paper-to-Lean map

The paper writes the local CKA state as `γ`. In the KEM construction, `γ`
alternates between a public key and a secret key:

```
paper §4.1.2                         Lean
────────────────────────────────────────────────────────────
(pk, sk) ← Gen                       InitKey PK SK := PK × SK
CKA-Init-A(pk, sk) = pk              initA := State.sendReady pk
CKA-Init-B(pk, sk) = sk              initB := State.recvReady sk
state γ = pk                         State.sendReady pk
state γ = sk                         State.recvReady sk
T = (c, pk')                         Message C PK := C × PK
epoch key I                          K
```

The constructors `sendReady` and `recvReady` come directly from the two shapes
of `γ` in the paper. A bare sum `PK ⊕ SK` would store the same raw data, but the
constructor names record the protocol phase in the type: a public key is exactly
the state from which the next operation is send, and a secret key is exactly the
state from which the next operation is receive.

One A-to-B step has the following shape:

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
  I1          := Dec(sk0, c1)
  B state     := sendReady pk1
```

The construction takes an ordinary KEM together with an explicit witness that
its monadic decapsulation is represented by a deterministic function. This keeps
the KEM as the primitive object and records the extra restriction needed by the
pure CKA receive API.
-/

open OracleSpec OracleComp ENNReal

universe u

namespace kemCKA

/-- Deterministic decapsulation witness for a KEM used in the CKA construction.

The CKA receive API is deterministic, and the paper construction uses
decapsulation as a deterministic function of secret key and ciphertext. This is
not a separate protocol: it is the extra property and concrete function needed
to use an ordinary monadic `KEMScheme` as input to the pure CKA receive
algorithm.
-/
structure DeterministicDecaps
    {m : Type → Type u} [Monad m]
    {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C) where
  -- Deterministic decapsulation used by the pure CKA receive algorithm.
  decapsDet : SK → C → Option K
  -- Compatibility between deterministic decapsulation and the KEM's monadic decapsulation.
  decaps_eq : ∀ sk c, kem.decaps sk c = pure (decapsDet sk c)

/-- Randomness-leaking view of the randomized KEM algorithms used by KEM-CKA send.

The CKA security game has send-randomness leak oracles. For a KEM-based send,
the randomized computations are exactly encapsulation under the current public
key and generation of the next KEM key pair. This structure packages versions of
those two computations that also return their sampled randomness.

The projection laws say that if the leaked randomness is erased with `Prod.fst`,
the resulting computation is definitionally the ordinary KEM computation. Thus
the executable construction remains a KEM construction, while the richer CKA
game can expose the coins when a concrete KEM implementation provides them.
-/
structure KEMRandLeak
    {m : Type → Type u} [Monad m]
    {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C) where
  KeygenRand : Type
  EncapsRand : Type
  -- Key generation together with the randomness used to sample the key pair.
  keygen_rleak : m ((PK × SK) × KeygenRand)
  -- Encapsulation together with the randomness used to sample the ciphertext/key.
  encaps_rleak : PK → m ((C × K) × EncapsRand)
  -- Erasing the leaked key-generation randomness recovers ordinary key generation.
  keygen_eq : Prod.fst <$> keygen_rleak = kem.keygen
  -- Erasing the leaked encapsulation randomness recovers ordinary encapsulation.
  encaps_eq : ∀ pk, Prod.fst <$> encaps_rleak pk = kem.encaps pk

namespace KEMRandLeak

variable {m : Type → Type u} [Monad m] {K PK SK C : Type}
  {kem : KEMScheme m K PK SK C}

/-- Distribution-level key-generation equality induced by `KEMRandLeak.keygen_eq`. -/
theorem keygen_evalDist_eq (runtime : ProbCompRuntime m)
    (leak : KEMRandLeak kem) :
    runtime.evalDist (Prod.fst <$> leak.keygen_rleak) =
      runtime.evalDist kem.keygen := by
  rw [leak.keygen_eq]

/-- Distribution-level encapsulation equality induced by `KEMRandLeak.encaps_eq`. -/
theorem encaps_evalDist_eq (runtime : ProbCompRuntime m)
    (leak : KEMRandLeak kem) (pk : PK) :
    runtime.evalDist (Prod.fst <$> leak.encaps_rleak pk) =
      runtime.evalDist (kem.encaps pk) := by
  rw [leak.encaps_eq pk]

end KEMRandLeak

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

The paper's CKA game has a bad-randomness oracle for sends. The current KEM
interface exposes probabilistic `keygen` and `encaps`, but it does not expose
their random coins as explicit inputs. Therefore the leaked randomness type for
this construction is `Unit`.

Future upstream-style explicit-randomness KEM APIs, for example
`keygenWithRand` and `encapsWithRand`, could replace this `Unit` by the actual
coin type while leaving the CKA game interface intact.
-/
def send_rleak {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C)
    (st : State PK SK) :
    m (Option (K × Message C PK × State PK SK × Unit)) := do
  match ← send kem st with
  | none => return none
  | some (key, msg, st') => return some (key, msg, st', ())

/-- KEM-CKA send algorithm with explicit KEM randomness leakage.

This is the same state transition as `send`, but it uses a `KEMRandLeak` package
so the send-randomness component records both KEM encapsulation randomness and
fresh key-generation randomness. The order `(EncapsRand × KeygenRand)` follows
the operational order of the send algorithm in [ACD19, Section 4.1.2].
-/
def send_rleakWithLeak {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C)
    (leak : KEMRandLeak kem)
    (st : State PK SK) :
    m (Option
      (K × Message C PK × State PK SK ×
        (leak.EncapsRand × leak.KeygenRand))) :=
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
* `Rho = C × PK`, a KEM ciphertext plus the next public key;
* `Rand = Unit`, because the KEM interface does not expose explicit coins.

The send and receive algorithms are the same for A and B; only initialization
differs, with A starting from the public key and B from the secret key.
-/
def scheme {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C)
    (hDet : DeterministicDecaps kem) :
    CKAScheme m (InitKey PK SK) (State PK SK) K (Message C PK) Unit where
  initKeyGen := kem.keygen
  initA := fun ik => return initA ik
  initB := fun ik => return initB ik
  sendA := send kem
  sendA_rleak := send_rleak kem
  recvA := recv hDet
  sendB := send kem
  sendB_rleak := send_rleak kem
  recvB := recv hDet

/-- Generic CKA scheme induced by a KEM with explicit send-randomness leakage.

This specializes `Rand` to the pair of randomness values used by a KEM-CKA send:
encapsulation randomness for the current epoch key and key-generation randomness
for the next KEM public/secret key pair. The non-leaking send and receive fields
are identical to `scheme`; only `sendA_rleak` and `sendB_rleak` use the richer
leaking KEM interface.
-/
def schemeWithLeak {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem) :
    CKAScheme m (InitKey PK SK) (State PK SK) K (Message C PK)
      (leak.EncapsRand × leak.KeygenRand) where
  initKeyGen := kem.keygen
  initA := fun ik => return initA ik
  initB := fun ik => return initB ik
  sendA := send kem
  sendA_rleak := send_rleakWithLeak kem leak
  recvA := recv hDet
  sendB := send kem
  sendB_rleak := send_rleakWithLeak kem leak
  recvB := recv hDet

end kemCKA

/-- The concrete probabilistic CKA scheme obtained from a probabilistic KEM and
a deterministic decapsulation witness.

This is the instance used by the existing CKA correctness and security games,
which are currently specialized to `ProbComp`.
-/
abbrev kemCKA {K PK SK C : Type}
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kemCKA.DeterministicDecaps kem) :
    CKAScheme ProbComp (kemCKA.InitKey PK SK) (kemCKA.State PK SK)
      K (kemCKA.Message C PK) Unit :=
  kemCKA.scheme kem hDet
