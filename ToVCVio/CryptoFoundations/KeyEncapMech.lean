/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import VCVio.CryptoFoundations.KeyEncapMech

/-!
# KEM Deterministic Decapsulation, Randomness Leaks, and Quantitative Correctness

Helper definitions for protocols built from a `KEMScheme`.

`KEMScheme.DeterministicDecaps` is a witness that the KEM decapsulation
computation is represented by a pure deterministic function, as required by
protocols whose receive algorithm is a pure function.

`KEMScheme.RandLeak` provides randomness-leaking versions of the two
randomized KEM algorithms, key generation and encapsulation, for security
games in which the adversary can ask for the coins of a past operation.
`KEMScheme.RandLeak.noLeak` is the trivial package for KEMs that do not
expose their coins.

`KEMScheme.correctnessError` is the probability that honest decapsulation
fails, and `KEMScheme.deltaCorrect` bounds it by a given `delta`. Both refine
`KEMScheme.PerfectlyCorrect`, which is the case of error `0`.
-/

open ENNReal

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

`keygenRleak` and `encapsRleak` return the ordinary KEM output together with
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
  keygenRleak : m ((PK × SK) × KeygenRand)
  /-- Encapsulation together with the randomness used to sample the
  ciphertext/key. -/
  encapsRleak : PK → m ((C × K) × EncapsRand)
  /-- First component: the ordinary key generation is the first component of
  `keygenRleak`. -/
  keygen_fst :
    (do
      let out ← keygenRleak
      pure out.1) = kem.keygen
  /-- First component: ordinary encapsulation is the first component of
  `encapsRleak pk`. -/
  encaps_fst : ∀ pk,
    (do
      let out ← encapsRleak pk
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
  keygenRleak := do
    let out ← kem.keygen
    pure (out, ())
  encapsRleak := fun pk => do
    let out ← kem.encaps pk
    pure (out, ())
  keygen_fst := by simp
  encaps_fst := fun pk => by simp

end RandLeak

section Correctness

variable [DecidableEq K]

/-- Correctness error of `kem` under `runtime`: the probability that the correctness experiment
`KEMScheme.CorrectExp` returns `false`, that is, the probability that decapsulating an honestly
generated encapsulation does not return the encapsulated key.

This refines `KEMScheme.PerfectlyCorrect`, which is the case where the error is `0`. -/
noncomputable def correctnessError (kem : KEMScheme m K PK SK C)
    (runtime : ProbCompRuntime m) : ℝ≥0∞ :=
  Pr[= false | runtime.evalDist kem.CorrectExp]

/-- `delta`-correctness of `kem` under `runtime`: the correctness error is at most `delta`. -/
-- ANCHOR: deltaCorrect
def deltaCorrect (kem : KEMScheme m K PK SK C)
    (runtime : ProbCompRuntime m) (delta : ℝ≥0∞) : Prop :=
  kem.correctnessError runtime ≤ delta
-- ANCHOR_END: deltaCorrect

end Correctness

end KEMScheme
