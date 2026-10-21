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

`ε = 1 - Pr[correctnessExperiment = true]`.

`KEMScheme.correctnessError` is this missing success mass and
`KEMScheme.deltaCorrect` is the assertion `ε ≤ δ`.  Defining error by missing
success mass, rather than only by `Pr[correctnessExperiment = false]`, also counts the
mass assigned to executions that produce no Boolean result—for example, a
failed or nonterminating computation.  Consequently `ε = 0` is exactly
`KEMScheme.PerfectlyCorrect`, even when the runtime's output measure has total
mass below one.  On a total runtime every execution produces a Boolean output, so
`ε = Pr[correctnessExperiment = false]`.
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

/-- Witness that a KEM's decapsulation never fails: it always recovers *some* key, though not
necessarily the encapsulated one. -/
structure TotalDecaps (kem : KEMScheme m K PK SK C) where
  /-- Decapsulation, repackaged with its `Option` wrapper removed. -/
  decapsTotal : SK → C → m K
  /-- `decapsTotal` agrees with the KEM's own decapsulation, up to the removed `Option` wrapper. -/
  decaps_eq : ∀ sk c, kem.decaps sk c = some <$> decapsTotal sk c

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

`1 - Pr[correctnessExperiment = true]`.

The successful event is that decapsulation of an honestly generated
encapsulation returns the encapsulated key.  This definition counts both a
`false` result and the mass of executions that fail or do not terminate.  If
the experiment is total, it equals `Pr[correctnessExperiment = false]`. -/
noncomputable def correctnessError (kem : KEMScheme m K PK SK C)
    (runtime : ProbCompRuntime m) : ℝ≥0∞ :=
  1 - runtime.evalDist kem.correctnessExperiment {true}

/-- Zero correctness error is equivalent to VCV-io's perfect-correctness
statement, without a totality assumption on the runtime. -/
theorem correctnessError_eq_zero_iff_perfectlyCorrect
    (kem : KEMScheme m K PK SK C) (runtime : ProbCompRuntime m) :
    kem.correctnessError runtime = 0 ↔ kem.PerfectlyCorrect runtime := by
  rw [correctnessError, PerfectlyCorrect, tsub_eq_zero_iff_le]
  exact ⟨fun h => le_antisymm ((MeasureTheory.measure_mono (Set.subset_univ _)).trans
    (runtime.evalDist_apply_univ_le_one _)) h, fun h => h.ge⟩

/-- Missing success mass decomposes exactly as the probability of returning
`false` plus the failure/nontermination mass of the evaluated experiment. -/
theorem correctnessError_eq_evalDist_false_add_prFail
    (kem : KEMScheme m K PK SK C) (runtime : ProbCompRuntime m) :
    kem.correctnessError runtime =
      runtime.evalDist kem.correctnessExperiment {false} +
        runtime.prFail kem.correctnessExperiment := by
  set μ := runtime.evalDist kem.correctnessExperiment
  have huniv : μ {true} + μ {false} = μ Set.univ :=
    MeasureTheory.Measure.apply_true_add_apply_false μ
  have hle : μ {true} + μ {false} ≤ 1 := huniv ▸ runtime.evalDist_apply_univ_le_one _
  rw [correctnessError, ProbCompRuntime.prFail, SemanticsVia.prFail]
  change 1 - μ {true} = μ {false} + (1 - μ Set.univ)
  rw [← huniv]
  refine (ENNReal.eq_sub_of_add_eq (MeasureTheory.measure_ne_top μ _) ?_).symm
  rw [add_comm, ← add_assoc, add_tsub_cancel_of_le hle]

/-- If the evaluated correctness experiment has no failure/nontermination
mass, missing success mass is exactly the probability of returning `false`. -/
theorem correctnessError_eq_evalDist_false_of_prFail_eq_zero
    (kem : KEMScheme m K PK SK C) (runtime : ProbCompRuntime m)
    (hfail : runtime.prFail kem.correctnessExperiment = 0) :
    kem.correctnessError runtime = runtime.evalDist kem.correctnessExperiment {false} := by
  rw [correctnessError_eq_evalDist_false_add_prFail, hfail, add_zero]

/-- For a `ProbComp` KEM, the correctness error is exactly the probability that the
correctness experiment returns `false`, since `ProbComp` never fails. -/
theorem correctnessError_probComp_eq_prEvent_false (kem : KEMScheme ProbComp K PK SK C) :
    kem.correctnessError ProbCompRuntime.probComp =
      Pr{let x ← kem.correctnessExperiment}[x = false] := by
  rw [correctnessError_eq_evalDist_false_of_prFail_eq_zero, ProbCompRuntime.probComp_evalDist,
    prEvent_eq_evalDist_singleton]
  rw [ProbCompRuntime.prFail, SemanticsVia.prFail, ← ProbCompRuntime.evalDist,
    MeasureTheory.measure_univ, tsub_self]

/-- A pointwise bound on the events of two continuations survives a common draw. -/
private lemma prEvent_bind_le_prEvent_bind [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] {α : Type} (mx : m α) (f g : α → m Prop)
    (h : ∀ a, prEvent (f a) ≤ prEvent (g a)) : prEvent (mx >>= f) ≤ prEvent (mx >>= g) := by
  simpa only [id_map] using
    prEvent_bind_mono_of_forall_le mx f g id id fun a => by simpa only [id_map] using h a

/-- Decapsulating an honestly-generated ciphertext fails no more often than `kem`'s own
correctness experiment returns `false`: whenever decapsulation returns `none`, it certainly
doesn't recover the encapsulated key. -/
theorem prEvent_none_decaps_le_prEvent_false_correctnessExperiment [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] (kem : KEMScheme m K PK SK C) :
    Pr{let x ← do let (pk, sk) ← kem.keygen; let (c, _k) ← kem.encaps pk; kem.decaps sk c}[
        x = (none : Option K)] ≤
      Pr{let x ← kem.correctnessExperiment}[x = false] := by
  unfold KEMScheme.correctnessExperiment
  simp only [map_bind, map_pure]
  refine prEvent_bind_le_prEvent_bind _ _ _ fun _ => ?_
  refine prEvent_bind_le_prEvent_bind _ _ _ fun _ => ?_
  refine prEvent_bind_le_prEvent_bind _ _ _ fun r => ?_
  rcases r with _ | k'
  · simp only [prEvent_pure_prop, ↓reduceIte, reduceCtorEq, decide_false, Std.le_refl]
  · simp only [reduceCtorEq, prEvent_pure_prop, ↓reduceIte, zero_le]

/-- `delta`-correctness of `kem` under `runtime`: the correctness error is at most `delta`. -/
-- ANCHOR: deltaCorrect
def deltaCorrect (kem : KEMScheme m K PK SK C)
    (runtime : ProbCompRuntime m) (delta : ℝ≥0∞) : Prop :=
  kem.correctnessError runtime ≤ delta
-- ANCHOR_END: deltaCorrect

/-- If `kem` is `delta`-correct under `runtime`, its correctness experiment returns `false` with
probability at most `delta`: missing success mass only grows by adding the (nonnegative)
failure/nontermination mass on top of `Pr[correctnessExperiment = false]`. -/
theorem evalDist_false_correctnessExperiment_le_of_deltaCorrect
    (kem : KEMScheme m K PK SK C) (runtime : ProbCompRuntime m) {delta : ℝ≥0∞}
    (h : kem.deltaCorrect runtime delta) :
    runtime.evalDist kem.correctnessExperiment {false} ≤ delta :=
  le_self_add.trans
    ((correctnessError_eq_evalDist_false_add_prFail kem runtime).symm.le.trans h)

end Correctness

end KEMScheme
