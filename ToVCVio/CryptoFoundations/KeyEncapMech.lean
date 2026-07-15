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

For the honest correctness experiment, put

`ε = 1 - Pr[CorrectExp = true]`.

`KEMScheme.correctnessError` is this missing success mass and
`KEMScheme.deltaCorrect` is the assertion `ε ≤ δ`.  Defining error by missing
success mass, rather than only by `Pr[CorrectExp = false]`, also counts the
mass assigned to executions that produce no Boolean result—for example, a
failed or nonterminating computation.  Consequently `ε = 0` is exactly
`KEMScheme.PerfectlyCorrect`, even when the runtime's output measure has total
mass below one.  On a total runtime every execution produces a Boolean output, so
`ε = Pr[CorrectExp = false]`.
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

/-- Correctness error of `kem` under `runtime`, defined as missing success mass:

`1 - Pr[CorrectExp = true]`.

The successful event is that decapsulation of an honestly generated
encapsulation returns the encapsulated key.  This definition counts both a
`false` result and the mass of executions that fail or do not terminate.  If
the experiment is total, it equals `Pr[CorrectExp = false]`. -/
noncomputable def correctnessError (kem : KEMScheme m K PK SK C)
    (runtime : ProbCompRuntime m) : ℝ≥0∞ :=
  1 - Pr[= true | runtime.evalDist kem.CorrectExp]

/-- Zero correctness error is equivalent to VCV-io's perfect-correctness
statement, without a totality assumption on the runtime. -/
theorem correctnessError_eq_zero_iff_perfectlyCorrect
    (kem : KEMScheme m K PK SK C) (runtime : ProbCompRuntime m) :
    kem.correctnessError runtime = 0 ↔ kem.PerfectlyCorrect runtime := by
  rw [correctnessError, PerfectlyCorrect, tsub_eq_zero_iff_le]
  exact ⟨fun h => le_antisymm probOutput_le_one h, fun h => h.ge⟩

/-- Missing success mass decomposes exactly as the probability of returning
`false` plus the failure/nontermination mass of the evaluated experiment. -/
theorem correctnessError_eq_probOutput_false_add_probFailure
    (kem : KEMScheme m K PK SK C) (runtime : ProbCompRuntime m) :
    kem.correctnessError runtime =
      Pr[= false | runtime.evalDist kem.CorrectExp] +
        Pr[⊥ | runtime.evalDist kem.CorrectExp] := by
  rw [correctnessError]
  symm
  refine ENNReal.eq_sub_of_add_eq probOutput_ne_top ?_
  have htotal := tsum_probOutput_add_probFailure
    (runtime.evalDist kem.CorrectExp)
  simpa only [tsum_fintype, Fintype.sum_bool, add_assoc, add_left_comm,
    add_comm] using htotal

/-- If the evaluated correctness experiment has no failure/nontermination
mass, missing success mass is exactly the probability of returning `false`. -/
theorem correctnessError_eq_probOutput_false_of_probFailure_eq_zero
    (kem : KEMScheme m K PK SK C) (runtime : ProbCompRuntime m)
    (hfail : Pr[⊥ | runtime.evalDist kem.CorrectExp] = 0) :
    kem.correctnessError runtime =
      Pr[= false | runtime.evalDist kem.CorrectExp] := by
  rw [correctnessError_eq_probOutput_false_add_probFailure, hfail, add_zero]

/-- `delta`-correctness of `kem` under `runtime`: the correctness error is at most `delta`. -/
-- ANCHOR: deltaCorrect
def deltaCorrect (kem : KEMScheme m K PK SK C)
    (runtime : ProbCompRuntime m) (delta : ℝ≥0∞) : Prop :=
  kem.correctnessError runtime ≤ delta
-- ANCHOR_END: deltaCorrect

end Correctness

end KEMScheme
