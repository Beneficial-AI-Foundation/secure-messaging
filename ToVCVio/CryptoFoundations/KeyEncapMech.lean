import VCVio.CryptoFoundations.KeyEncapMech

/-!
# KEM Deterministic Decapsulation and Randomness Leaks

Two helper structures for protocols built from a `KEMScheme`.

`KEMScheme.DeterministicDecaps` is a witness that the KEM decapsulation
computation is represented by a pure deterministic function, as required by
protocols whose receive algorithm is a pure function.

`KEMScheme.RandLeak` provides randomness-leaking versions of the two
randomized KEM algorithms, key generation and encapsulation, for security
games in which the adversary can ask for the coins of a past operation.
`KEMScheme.RandLeak.noLeak` is the trivial package for KEMs that do not
expose their coins.
-/

universe u

namespace KEMScheme

variable {m : Type → Type u} [Monad m] {K PK SK C : Type}

/-- Witness that a KEM's decapsulation is represented by a pure deterministic
function. -/
structure DeterministicDecaps (kem : KEMScheme m K PK SK C) where
  /-- Deterministic decapsulation, usable from pure code. -/
  decapsDet : SK → C → Option K
  /-- `decapsDet` agrees with the KEM's monadic decapsulation. -/
  decaps_eq : ∀ sk c, kem.decaps sk c = pure (decapsDet sk c)

/-- Randomness-leaking versions of the two randomized KEM algorithms: key
generation and encapsulation.

`keygen_rleak` and `encaps_rleak` return the ordinary KEM output together with
the randomness they sampled, so that a security game can answer
randomness-leak queries. The fields `keygen_fst` and `encaps_fst` say that the
ordinary KEM computations are the first component of the randomness-returning
ones.
-/
structure RandLeak (kem : KEMScheme m K PK SK C) where
  /-- Randomness space of one key generation. -/
  KeygenRand : Type
  /-- Randomness space of one encapsulation. -/
  EncapsRand : Type
  /-- Key generation together with the randomness used to sample the key pair. -/
  keygen_rleak : m ((PK × SK) × KeygenRand)
  /-- Encapsulation together with the randomness used to sample the
  ciphertext/key. -/
  encaps_rleak : PK → m ((C × K) × EncapsRand)
  /-- First component: the ordinary key generation is the first component of
  `keygen_rleak`. -/
  keygen_fst :
    (do
      let out ← keygen_rleak
      pure out.1) = kem.keygen
  /-- First component: ordinary encapsulation is the first component of
  `encaps_rleak pk`. -/
  encaps_fst : ∀ pk,
    (do
      let out ← encaps_rleak pk
      pure out.1) = kem.encaps pk

namespace RandLeak

/-- The combined randomness of the two randomized KEM calls in one protocol
step built from a leak package. The component order `EncapsRand × KeygenRand`
matches a step that encapsulates first and then generates a fresh key pair.
-/
abbrev Rand {kem : KEMScheme m K PK SK C} (leak : RandLeak kem) : Type :=
  leak.EncapsRand × leak.KeygenRand

/-- The trivial randomness-leak package: both leak types are `Unit` and the
leaking computations are the ordinary KEM computations. It covers KEMs that do
not expose their coins: every leaking call returns `()` as its randomness, so
leak oracles reveal nothing to the adversary. This is a weaker no-leak model;
a security statement built on a leak package quantifies over an arbitrary
supplied package rather than defaulting to this trivial one.
-/
def noLeak [LawfulMonad m] (kem : KEMScheme m K PK SK C) : RandLeak kem where
  KeygenRand := Unit
  EncapsRand := Unit
  keygen_rleak := do
    let out ← kem.keygen
    pure (out, ())
  encaps_rleak := fun pk => do
    let out ← kem.encaps pk
    pure (out, ())
  keygen_fst := by simp
  encaps_fst := fun pk => by simp

end RandLeak

end KEMScheme
