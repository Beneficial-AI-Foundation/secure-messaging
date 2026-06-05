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
function (`DeterministicDecaps`). The randomness leaked by one send is
described by a `KEMRandLeak` package, with `KEMRandLeak.unit` covering KEMs
that do not expose their coins.
-/

open OracleSpec OracleComp ENNReal

universe u

namespace kemCKA

/-- Witness that a KEM's decapsulation is represented by a pure deterministic
function, as required by the deterministic CKA receive API.
-/
structure DeterministicDecaps
    {m : Type → Type u} [Monad m]
    {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C) where
  -- Deterministic decapsulation used by the pure CKA receive algorithm.
  decapsDet : SK → C → Option K
  -- `decapsDet` agrees with the KEM's monadic decapsulation.
  decaps_eq : ∀ sk c, kem.decaps sk c = pure (decapsDet sk c)

/-- Randomness-leaking versions of the two randomized KEM algorithms used by a
KEM-CKA send: key generation and encapsulation.

`keygen_rleak` and `encaps_rleak` return the ordinary KEM output together with
the randomness they sampled, so the CKA security game can answer
send-randomness leak queries. The fields `keygen_fst` and `encaps_fst` say
that the ordinary KEM computations are the first component of the
randomness-returning ones.
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
  -- First component: the ordinary key generation is the first component
  -- of `keygen_rleak`.
  keygen_fst : Prod.fst <$> keygen_rleak = kem.keygen
  -- First component: ordinary encapsulation is the first component of
  -- `encaps_rleak pk`.
  encaps_fst : ∀ pk, Prod.fst <$> encaps_rleak pk = kem.encaps pk

namespace KEMRandLeak

/-- Send-randomness type induced by a leak package: the combined randomness of
the two randomized KEM calls in one KEM-CKA send. The component order
`EncapsRand × KeygenRand` follows the operational order of the send algorithm,
which encapsulates before generating the next key pair.
-/
abbrev Rand {m : Type → Type u} [Monad m] {K PK SK C : Type}
    {kem : KEMScheme m K PK SK C} (leak : KEMRandLeak kem) : Type :=
  leak.EncapsRand × leak.KeygenRand

/-- The trivial randomness-leak package: both leak types are `Unit` and the
leaking computations are the ordinary KEM computations. It instantiates the
construction for KEMs that do not expose their coins: one CKA send built from
this package leaks only `((), ())`, one `()` for each of the two randomized
KEM calls, so the leak oracles reveal nothing to the adversary. This is a
weaker no-leak model; the ACD19-facing security statement quantifies over an
arbitrary leak package instead of defaulting to this trivial one.
-/
def unit {m : Type → Type u} [Monad m] [LawfulMonad m] {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C) : KEMRandLeak kem where
  KeygenRand := Unit
  EncapsRand := Unit
  keygen_rleak := (·, ()) <$> kem.keygen
  encaps_rleak := fun pk => (·, ()) <$> kem.encaps pk
  keygen_fst := by simp
  encaps_fst := fun pk => by simp

end KEMRandLeak

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

Same state transition as `send`, built from a `KEMRandLeak` package so that
the output also records the randomness of the two randomized KEM calls, as a
pair of type `KEMRandLeak.Rand leak`.
-/
def send_rleak {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C)
    (leak : KEMRandLeak kem)
    (st : State PK SK) :
    m (Option (K × Message C PK × State PK SK × leak.Rand)) :=
  match st with
  | .sendReady pk => do
      let ((c, key), rEnc) ← leak.encaps_rleak pk
      let ((pk', sk'), rKeygen) ← leak.keygen_rleak
      return some (key, (c, pk'), .recvReady sk', (rEnc, rKeygen))
  | .recvReady _ => return none

/-- Project a randomness-leaking send output to the ordinary send output. -/
def sendWithRandFst {K PK SK C Rand : Type}
    (out? : Option (K × Message C PK × State PK SK × Rand)) :
    Option (K × Message C PK × State PK SK) :=
  out?.map fun | (key, msg, st, _rand) => (key, msg, st)

-- Taking the first component inside the continuation is the same as mapping
-- `Prod.fst` over the bound computation; used to lift `keygen_fst` and
-- `encaps_fst`.
private theorem bind_fst_eq
    {m : Type → Type u} [Monad m] [LawfulMonad m]
    {α β γ : Type} (x : m (α × β)) (f : α → m γ) :
    (x >>= fun y => f y.1) = ((Prod.fst <$> x) >>= f) := by
  simp

/-- The randomness-leaking send agrees with the ordinary send after projecting
away the leaked sender randomness. This lifts the `KEMRandLeak` fields
`encaps_fst` and `keygen_fst` to the CKA send algorithm.
-/
theorem send_rleak_fst_eq_send
    {m : Type → Type u} [Monad m] [LawfulMonad m]
    {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C)
    (leak : KEMRandLeak kem)
    (st : State PK SK) :
    sendWithRandFst <$> send_rleak kem leak st = send kem st := by
  cases st with
  | sendReady pk =>
      simp only [send, send_rleak]
      rw [map_bind, ← leak.encaps_fst pk, ← leak.keygen_fst, ← bind_fst_eq]
      refine bind_congr fun ⟨⟨c, key⟩, rEnc⟩ => ?_
      simp only [map_bind]
      rw [← bind_fst_eq]
      refine bind_congr fun ⟨⟨pk', sk'⟩, rKeygen⟩ => ?_
      simp [sendWithRandFst]
  | recvReady sk => simp [send, send_rleak, sendWithRandFst]

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
* `Rand = KEMRandLeak.Rand leak`, the encapsulation and key-generation
  randomness leaked by one send.

The send and receive algorithms are the same for A and B; only initialization
differs, with A starting from the public key and B from the secret key. For a
KEM that does not expose its coins, instantiate `leak` with the trivial
package `KEMRandLeak.unit kem`.
-/
def scheme {m : Type → Type u} [Monad m] {K PK SK C : Type}
    (kem : KEMScheme m K PK SK C)
    (hDet : DeterministicDecaps kem)
    (leak : KEMRandLeak kem) :
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

end kemCKA
