/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Construction
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-!
# Opp-UniKEM-CKA — Conditional KEM Error

This file isolates the probabilistic fact about the KEM that is needed by the
protocol proof.  An on/off encapsulation is sampled in three stages: a key
pair, an offline state and ciphertext, and finally an online ciphertext and
key.  The factorization axiom identifies the joint distribution of these
three stages with ordinary KEM encapsulation.

Write

* `χ(pk, sk, st, ct₀)` for the correctness error after the
  key pair and offline result have both been fixed;
* `φ(pk, sk)` for the expectation of `χ` over a fresh offline result; and
* `ψ(st, ct₀)` for the expectation of `χ` over a fresh key pair.

These are conditional correctness errors: an explicit key mismatch and
missing probability mass are both counted as error.  They are not pointwise
bounds by the global KEM error.  Their essential properties are the two tower
identities

`E_keypair[φ] = ε_KEM` and `E_offline[ψ] = ε_KEM`,

together with the corresponding online identity expressing `χ` as the
expected failure indicator.  Thus whichever side samples the first component
of a fresh protocol epoch, its expected residual error is exactly the KEM's
average correctness error.  The factorization theorem identifies the staged
experiment with the standard KEM correctness experiment, so a `δ`-correct KEM
bounds this common error by `δ`.
-/

open OracleSpec OracleComp ENNReal KEMScheme

namespace oppUniKemCKA

universe u

variable {K PK SK C : Type}

/-! ## Factorized KEM correctness -/

/-- The KEM correctness experiment written in the three phases used by the
Opp-UniKEM protocol: key generation, offline encapsulation, and online
encapsulation. -/
def factorCorrectExp [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) : ProbComp Bool := do
  let (pk, sk) ← kem.keygen
  let (st, ct0) ← onoff.encapsOff
  let (ct1, key) ← onoff.encapsOn st pk
  pure (decide
    (hDet.decapsDet sk (onoff.split.symm (ct0, ct1)) = some key))

/-- On/off factorization and deterministic decapsulation make the factorized
experiment distributionally identical to the ordinary KEM correctness
experiment. -/
theorem factorCorrectExp_eq_correctExp [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) :
    factorCorrectExp kem onoff hDet = kem.CorrectExp := by
  unfold factorCorrectExp KEMScheme.CorrectExp
  simp_rw [onoff.factor, hDet.decaps_eq]
  simp only [bind_assoc, pure_bind]

/-- `kem.deltaCorrect δ` bounds failure of the factorized experiment used by
one complete Opp-UniKEM epoch. -/
theorem factorCorrectExp_failure_le_of_deltaCorrect [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) (δ : ℝ≥0∞)
    (hδ : kem.deltaCorrect ProbCompRuntime.probComp δ) :
    Pr[= false | factorCorrectExp kem onoff hDet] ≤ δ := by
  unfold KEMScheme.deltaCorrect at hδ
  calc
    Pr[= false | factorCorrectExp kem onoff hDet] =
        Pr[= false | kem.CorrectExp] := by rw [factorCorrectExp_eq_correctExp]
    _ ≤ Pr[= false | kem.CorrectExp] + Pr[⊥ | kem.CorrectExp] :=
      le_add_right le_rfl
    _ = kem.correctnessError ProbCompRuntime.probComp := by
      symm
      exact KEMScheme.correctnessError_eq_probOutput_false_add_probFailure
        kem ProbCompRuntime.probComp
    _ ≤ δ := hδ

/-- The total correctness error of the factorized experiment.  Missing mass
is charged as an error, just as it is in `KEMScheme.correctnessError`. -/
noncomputable def factorCorrectnessError [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) : ℝ≥0∞ :=
  Pr[= false | factorCorrectExp kem onoff hDet] +
    Pr[⊥ | factorCorrectExp kem onoff hDet]

/-- Factorization identifies the total staged error with the ordinary KEM
correctness error, including any missing mass. -/
theorem factorCorrectnessError_eq [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) :
    factorCorrectnessError kem onoff hDet =
      kem.correctnessError ProbCompRuntime.probComp := by
  rw [factorCorrectnessError, factorCorrectExp_eq_correctExp]
  exact (KEMScheme.correctnessError_eq_probOutput_false_add_probFailure
    kem ProbCompRuntime.probComp).symm

/-- A `δ`-correct KEM bounds the total error of the factorized experiment. -/
theorem factorCorrectnessError_le_of_deltaCorrect [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) (δ : ℝ≥0∞)
    (hδ : kem.deltaCorrect ProbCompRuntime.probComp δ) :
    factorCorrectnessError kem onoff hDet ≤ δ := by
  rw [factorCorrectnessError_eq]
  exact hδ

/-! ### Conditional KEM-failure potentials

The KEM correctness error is an average over all three independent samples.
Once a protocol epoch has sampled only a key pair or only an offline
encapsulation, its remaining conditional correctness error need not be at
most the original average.  The following potentials retain that conditional
probability.  Their tower identities are what permits an adaptive protocol
execution to be charged only when it starts a fresh epoch. -/

private def onlineCorrectExp [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) (pk : PK) (sk : SK)
    (st : onoff.St) (ct0 : onoff.C₀) : ProbComp Bool := do
  let (ct1, key) ← onoff.encapsOn st pk
  pure (decide
    (hDet.decapsDet sk (onoff.split.symm (ct0, ct1)) = some key))

/-- The conditional KEM correctness error after both the key pair and the
offline encapsulation have been fixed. -/
noncomputable def failureAfterBoth [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) (pk : PK) (sk : SK)
    (st : onoff.St) (ct0 : onoff.C₀) : ℝ≥0∞ :=
  Pr[= false | onlineCorrectExp kem onoff hDet pk sk st ct0] +
    Pr[⊥ | onlineCorrectExp kem onoff hDet pk sk st ct0]

/-- The residual KEM correctness error after fixing a key pair and averaging
over the offline and online encapsulation stages. -/
noncomputable def failureAfterKeypair [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) (pk : PK) (sk : SK) : ℝ≥0∞ :=
  Pr[⊥ | onoff.encapsOff] +
    ∑' off : onoff.St × onoff.C₀,
      Pr[= off | onoff.encapsOff] *
        failureAfterBoth kem onoff hDet pk sk off.1 off.2

/-- The residual KEM correctness error after fixing an offline result and
averaging over key generation and online encapsulation. -/
noncomputable def failureAfterOff [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) (st : onoff.St) (ct0 : onoff.C₀) : ℝ≥0∞ :=
  Pr[⊥ | kem.keygen] +
    ∑' kp : PK × SK, Pr[= kp | kem.keygen] *
      failureAfterBoth kem onoff hDet kp.1 kp.2 st ct0

private lemma boolError_bind {A : Type} (oa : ProbComp A)
    (ob : A → ProbComp Bool) :
    Pr[= false | oa >>= ob] + Pr[⊥ | oa >>= ob] =
      Pr[⊥ | oa] + ∑' a, Pr[= a | oa] *
        (Pr[= false | ob a] + Pr[⊥ | ob a]) := by
  rw [probOutput_bind_eq_tsum, probFailure_bind_eq_add_tsum]
  calc
    (∑' a, Pr[= a | oa] * Pr[= false | ob a]) +
          (Pr[⊥ | oa] + ∑' a, Pr[= a | oa] * Pr[⊥ | ob a]) =
        Pr[⊥ | oa] +
          ((∑' a, Pr[= a | oa] * Pr[= false | ob a]) +
            ∑' a, Pr[= a | oa] * Pr[⊥ | ob a]) := by ac_rfl
    _ = Pr[⊥ | oa] + ∑' a, Pr[= a | oa] *
          (Pr[= false | ob a] + Pr[⊥ | ob a]) := by
      congr 1
      rw [← ENNReal.tsum_add]
      refine tsum_congr fun a => ?_
      rw [mul_add]

private lemma boolError_le_one (oa : ProbComp Bool) :
    Pr[= false | oa] + Pr[⊥ | oa] ≤ 1 := by
  calc
    Pr[= false | oa] + Pr[⊥ | oa] ≤
        (∑' b : Bool, Pr[= b | oa]) + Pr[⊥ | oa] := by
      exact add_le_add (ENNReal.le_tsum false) le_rfl
    _ = 1 := tsum_probOutput_add_probFailure oa

/-- Tower identity obtained by conditioning the factorized experiment on its
key pair. -/
lemma factor_failure_tower_keypair [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) :
    factorCorrectnessError kem onoff hDet =
      Pr[⊥ | kem.keygen] +
        ∑' kp : PK × SK, Pr[= kp | kem.keygen] *
          failureAfterKeypair kem onoff hDet kp.1 kp.2 := by
  unfold factorCorrectnessError factorCorrectExp failureAfterKeypair
  rw [boolError_bind]
  congr 1
  refine tsum_congr fun kp => ?_
  congr 1
  unfold failureAfterBoth onlineCorrectExp
  rw [boolError_bind]

/-- Tower identity obtained by conditioning the factorized experiment on its
offline result. -/
lemma factor_failure_tower_off [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) :
    factorCorrectnessError kem onoff hDet =
      Pr[⊥ | onoff.encapsOff] +
        ∑' off : onoff.St × onoff.C₀, Pr[= off | onoff.encapsOff] *
          failureAfterOff kem onoff hDet off.1 off.2 := by
  let reordered : ProbComp Bool := do
    let (st, ct0) ← onoff.encapsOff
    let (pk, sk) ← kem.keygen
    onlineCorrectExp kem onoff hDet pk sk st ct0
  have hreorder :
      evalDist (factorCorrectExp kem onoff hDet) = evalDist reordered := by
    unfold factorCorrectExp reordered
    simpa only using
      (OracleComp.DeferredSampling.evalDist_bind_comm kem.keygen onoff.encapsOff
        (fun kp off => onlineCorrectExp kem onoff hDet kp.1 kp.2 off.1 off.2))
  have hfalse : Pr[= false | factorCorrectExp kem onoff hDet] =
      Pr[= false | reordered] := by
    exact congrArg (fun d : SPMF Bool => d false) hreorder
  have hfail : Pr[⊥ | factorCorrectExp kem onoff hDet] =
      Pr[⊥ | reordered] := by
    exact congrArg (fun d : SPMF Bool => d.run none) hreorder
  rw [factorCorrectnessError, hfalse, hfail]
  unfold reordered failureAfterOff
  rw [boolError_bind]
  congr 1
  refine tsum_congr fun off => ?_
  congr 1
  unfold failureAfterBoth onlineCorrectExp
  rw [boolError_bind]

lemma failureAfterKeypair_le_one [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) (pk : PK) (sk : SK) :
    failureAfterKeypair kem onoff hDet pk sk ≤ 1 := by
  unfold failureAfterKeypair failureAfterBoth
  calc
    Pr[⊥ | onoff.encapsOff] + ∑' off : onoff.St × onoff.C₀,
        Pr[= off | onoff.encapsOff] *
          (Pr[= false | onlineCorrectExp kem onoff hDet pk sk off.1 off.2] +
            Pr[⊥ | onlineCorrectExp kem onoff hDet pk sk off.1 off.2]) ≤
        Pr[⊥ | onoff.encapsOff] +
          ∑' off : onoff.St × onoff.C₀, Pr[= off | onoff.encapsOff] * 1 := by
      exact add_le_add le_rfl (ENNReal.tsum_le_tsum fun off =>
        mul_le_mul' le_rfl (boolError_le_one _))
    _ = 1 := by
      simp only [mul_one]
      exact probFailure_add_tsum_probOutput onoff.encapsOff

lemma failureAfterOff_le_one [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) (st : onoff.St) (ct0 : onoff.C₀) :
    failureAfterOff kem onoff hDet st ct0 ≤ 1 := by
  unfold failureAfterOff failureAfterBoth
  calc
    Pr[⊥ | kem.keygen] + ∑' kp : PK × SK, Pr[= kp | kem.keygen] *
        (Pr[= false | onlineCorrectExp kem onoff hDet kp.1 kp.2 st ct0] +
          Pr[⊥ | onlineCorrectExp kem onoff hDet kp.1 kp.2 st ct0]) ≤
        Pr[⊥ | kem.keygen] +
          ∑' kp : PK × SK, Pr[= kp | kem.keygen] * 1 := by
      exact add_le_add le_rfl (ENNReal.tsum_le_tsum fun kp =>
        mul_le_mul' le_rfl (boolError_le_one _))
    _ = 1 := by
      simp only [mul_one]
      exact probFailure_add_tsum_probOutput kem.keygen

lemma failureAfterBoth_le_one [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) (pk : PK) (sk : SK)
    (st : onoff.St) (ct0 : onoff.C₀) :
    failureAfterBoth kem onoff hDet pk sk st ct0 ≤ 1 := by
  unfold failureAfterBoth
  exact boolError_le_one _

/-- Online tower identity: the conditional error after the first two stages is
the expected indicator of online decapsulation failure. -/
lemma failureAfterBoth_eq_indicator [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) (pk : PK) (sk : SK)
    (st : onoff.St) (ct0 : onoff.C₀) :
    failureAfterBoth kem onoff hDet pk sk st ct0 =
      Pr[⊥ | onoff.encapsOn st pk] +
        ∑' out : onoff.C₁ × K, Pr[= out | onoff.encapsOn st pk] *
          if hDet.decapsDet sk (onoff.split.symm (ct0, out.1)) ≠ some out.2
          then 1 else 0 := by
  unfold failureAfterBoth onlineCorrectExp
  rw [probOutput_bind_eq_tsum, probFailure_bind_eq_add_tsum]
  simp only [probFailure_pure, mul_zero, tsum_zero, add_zero]
  rw [add_comm]
  refine congrArg (fun x : ℝ≥0∞ => Pr[⊥ | onoff.encapsOn st pk] + x) ?_
  refine tsum_congr fun out => ?_
  by_cases hgood : hDet.decapsDet sk (onoff.split.symm (ct0, out.1)) = some out.2
  · simp [hgood]
  · simp [hgood]

end oppUniKemCKA
