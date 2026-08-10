/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.OnOffKEM.Defs
import ToVCVio.OracleComp.ExpectedPayoff
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-!
# On/Off KEM — Correctness Error by Sampling Stage

This file decomposes the correctness error of an on/off KEM according to the
stages of its encapsulation algorithm.

Let `kem` be a KEM scheme, `onoff` an on/off factorization of its encapsulation
algorithm, and `hDet` a deterministic implementation of decapsulation.  The
factorization expresses honest encapsulation in two parts:

* `onoff.encapsOff` produces state `st` and the offline ciphertext part `ct₀`
  without using a public key;
* `onoff.encapsOn st pk` uses `st` and a public key `pk` to produce the online
  ciphertext part `ct₁` and the encapsulated key `k`.

The equivalence `onoff.split : C ≃ C₀ × C₁` identifies a KEM ciphertext with
its offline and online parts.  Its inverse joins `(ct₀, ct₁)` into the
ciphertext passed to decapsulation.

## Staged correctness experiment

The experiment `factorCorrectExp` runs key generation and both encapsulation
stages, then checks whether decapsulation recovers the encapsulated key:

```text
factorCorrectExp := do
  (pk, sk) ← kem.keygen
  (st, ct₀) ← onoff.encapsOff
  (ct₁, k) ← onoff.encapsOn st pk
  return hDet.decapsDet sk (onoff.split.symm (ct₀, ct₁)) = some k
```

The theorem `factorCorrectExp_eq_correctExp` proves that this staged experiment
is equal, as a `ProbComp` program, to the standard KEM correctness experiment
`kem.CorrectExp`.  The theorem `factorCorrectnessError_eq` therefore identifies
its total error

```text
ε := Pr[factorCorrectExp = false] + Pr[factorCorrectExp = ⊥]
```

with `kem.correctnessError ProbCompRuntime.probComp`.

For `X : ProbComp α`, `Pr[X = x]` is the probability that `X` returns `x`, and
`Pr[X = ⊥]` is its missing probability mass—the probability that evaluating
`X` produces no output.  Missing mass counts as correctness error throughout
this file.

## Errors after fixed samples

To describe the contribution of each sampling stage, we fix the outputs of one
or both of the first two computations and measure the error in the computations
that remain:

* `failureAfterBoth` (`χ(pk, sk, st, ct₀)`) fixes the key pair and the offline
  sample, then measures the error of online encapsulation;
* `failureAfterKeypair` (`φ(pk, sk)`) fixes the key pair and averages
  `failureAfterBoth` over offline encapsulation;
* `failureAfterOff` (`ψ(st, ct₀)`) fixes the offline sample and averages
  `failureAfterBoth` over key generation.

These quantities use the displayed values as parameters.  They do not
condition the original experiment on an event or divide by the probability of
the fixed values.  They are therefore defined even for values that their
samplers never return; such values receive zero weight when the errors are
averaged.

Writing

```text
KG       := kem.keygen
OFF      := onoff.encapsOff
ON st pk := onoff.encapsOn st pk,
```

the three errors are

```text
χ(pk, sk, st, ct₀) := Pr[ON st pk = ⊥]
    + Σ (ct₁, k), Pr[ON st pk = (ct₁, k)] ·
        (if hDet.decapsDet sk (onoff.split.symm (ct₀, ct₁)) ≠ some k then 1 else 0)

φ(pk, sk)  := Pr[OFF = ⊥]
    + Σ (st, ct₀), Pr[OFF = (st, ct₀)] · χ(pk, sk, st, ct₀)

ψ(st, ct₀) := Pr[KG = ⊥]
    + Σ (pk, sk), Pr[KG = (pk, sk)] · χ(pk, sk, st, ct₀).
```

## Averaging identities and bounds

Key generation and offline encapsulation do not depend on each other's output.
The total error can consequently be obtained by averaging in either order:

* `factorCorrectnessError_eq_avg_keypair` proves
  `ε = Pr[KG = ⊥] + Σ (pk, sk), Pr[KG = (pk, sk)] · φ(pk, sk)`;
* `factorCorrectnessError_eq_avg_off` proves
  `ε = Pr[OFF = ⊥] + Σ (st, ct₀), Pr[OFF = (st, ct₀)] · ψ(st, ct₀)`.

The lemmas `failureAfterBoth_le_one`, `failureAfterKeypair_le_one`, and
`failureAfterOff_le_one` prove that each of these errors is at most `1`.
-/

open OracleSpec OracleComp ENNReal

namespace KEMScheme

variable {K PK SK C : Type}

/-! ## Staged correctness experiment -/

/-- The KEM correctness experiment expressed through the on/off factorization.
It samples `(pk, sk) ← kem.keygen`, `(st, ct₀) ← onoff.encapsOff`, and
`(ct₁, k) ← onoff.encapsOn st pk`, then returns whether decapsulating the
joined ciphertext recovers `k`:
`hDet.decapsDet sk (onoff.split.symm (ct₀, ct₁)) = some k`. -/
def factorCorrectExp [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) : ProbComp Bool := do
  let (pk, sk) ← kem.keygen
  let (st, ct0) ← onoff.encapsOff
  let (ct1, key) ← onoff.encapsOn st pk
  pure (decide
    (hDet.decapsDet sk (onoff.split.symm (ct0, ct1)) = some key))

/-- `factorCorrectExp` and the ordinary KEM correctness experiment
`kem.CorrectExp` are equal as programs, by the factorization law
`onoff.factor` and determinism of decapsulation (`hDet.decaps_eq`). -/
theorem factorCorrectExp_eq_correctExp [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) :
    factorCorrectExp kem onoff hDet = kem.CorrectExp := by
  unfold factorCorrectExp KEMScheme.CorrectExp
  simp_rw [onoff.factor, hDet.decaps_eq]
  simp only [bind_assoc, pure_bind]

/-- The total correctness error of `factorCorrectExp`: the probability of a
`false` result plus the missing probability mass, as in
`KEMScheme.correctnessError`. -/
noncomputable def factorCorrectnessError [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) : ℝ≥0∞ :=
  Pr[= false | factorCorrectExp kem onoff hDet] +
    Pr[⊥ | factorCorrectExp kem onoff hDet]

/-- The error of the staged experiment equals the standard correctness error
of `kem` under the `ProbComp` runtime. -/
theorem factorCorrectnessError_eq [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) :
    factorCorrectnessError kem onoff hDet =
      kem.correctnessError ProbCompRuntime.probComp := by
  rw [factorCorrectnessError, factorCorrectExp_eq_correctExp]
  exact (KEMScheme.correctnessError_eq_probOutput_false_add_probFailure
    kem ProbCompRuntime.probComp).symm

/-! ### Errors after fixed samples

The following errors hold already chosen sample values fixed and measure the
error in the remaining sampling stages.  The error for one particular fixed
sample may exceed the total error `ε`; averaging over the sampler that produced
the fixed value recovers `ε`, as shown by the identities below. -/

/-- The remaining online stage after fixing `pk`, `sk`, `st`, and `ct₀`.
It samples `(ct₁, k) ← onoff.encapsOn st pk` and returns whether
`hDet.decapsDet sk (onoff.split.symm (ct₀, ct₁)) = some k`. -/
private def onlineCorrectExp [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) (pk : PK) (sk : SK)
    (st : onoff.St) (ct0 : onoff.C₀) : ProbComp Bool := do
  let (ct1, key) ← onoff.encapsOn st pk
  pure (decide
    (hDet.decapsDet sk (onoff.split.symm (ct0, ct1)) = some key))

/-- `χ(pk, sk, st, ct₀)`, the KEM correctness error after fixing the key
pair and the offline sample: the probability that
`(ct₁, k) ← onoff.encapsOn st pk` gives
`hDet.decapsDet sk (onoff.split.symm (ct₀, ct₁)) ≠ some k`, plus the
sampler's missing probability mass. -/
noncomputable def failureAfterBoth [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) (pk : PK) (sk : SK)
    (st : onoff.St) (ct0 : onoff.C₀) : ℝ≥0∞ :=
  Pr[= false | onlineCorrectExp kem onoff hDet pk sk st ct0] +
    Pr[⊥ | onlineCorrectExp kem onoff hDet pk sk st ct0]

/-- `φ(pk, sk)`, the KEM correctness error after fixing the key pair:
the average of `failureAfterBoth` over
`(st, ct₀) ← onoff.encapsOff`, plus the sampler's missing probability mass. -/
noncomputable def failureAfterKeypair [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) (pk : PK) (sk : SK) : ℝ≥0∞ :=
  Pr[⊥ | onoff.encapsOff] +
    ∑' off : onoff.St × onoff.C₀,
      Pr[= off | onoff.encapsOff] *
        failureAfterBoth kem onoff hDet pk sk off.1 off.2

/-- `ψ(st, ct₀)`, the KEM correctness error after fixing the offline sample:
the average of `failureAfterBoth` over
`(pk, sk) ← kem.keygen`, plus the sampler's missing probability mass. -/
noncomputable def failureAfterOff [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) (st : onoff.St) (ct0 : onoff.C₀) : ℝ≥0∞ :=
  Pr[⊥ | kem.keygen] +
    ∑' kp : PK × SK, Pr[= kp | kem.keygen] *
      failureAfterBoth kem onoff hDet kp.1 kp.2 st ct0

/-- The total staged correctness error is the missing mass of `kem.keygen`
plus the probability-weighted average of `failureAfterKeypair` over its
returned key pairs. -/
lemma factorCorrectnessError_eq_avg_keypair [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) :
    factorCorrectnessError kem onoff hDet =
      Pr[⊥ | kem.keygen] +
        ∑' kp : PK × SK, Pr[= kp | kem.keygen] *
          failureAfterKeypair kem onoff hDet kp.1 kp.2 := by
  unfold factorCorrectnessError factorCorrectExp failureAfterKeypair
  rw [probOutput_false_add_probFailure_bind]
  congr 1
  refine tsum_congr fun kp => ?_
  congr 1
  unfold failureAfterBoth onlineCorrectExp
  rw [probOutput_false_add_probFailure_bind]

/-- The total staged correctness error is the missing mass of
`onoff.encapsOff` plus the probability-weighted average of `failureAfterOff`
over its returned offline samples. -/
lemma factorCorrectnessError_eq_avg_off [DecidableEq K]
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
  rw [probOutput_false_add_probFailure_bind]
  congr 1
  refine tsum_congr fun off => ?_
  congr 1
  unfold failureAfterBoth onlineCorrectExp
  rw [probOutput_false_add_probFailure_bind]

/-- `failureAfterKeypair` is at most `1`. -/
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
        mul_le_mul' le_rfl (probOutput_false_add_probFailure_le_one _))
    _ = 1 := by
      simp only [mul_one]
      exact probFailure_add_tsum_probOutput onoff.encapsOff

/-- `failureAfterOff` is at most `1`. -/
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
        mul_le_mul' le_rfl (probOutput_false_add_probFailure_le_one _))
    _ = 1 := by
      simp only [mul_one]
      exact probFailure_add_tsum_probOutput kem.keygen

/-- `failureAfterBoth` is at most `1`. -/
lemma failureAfterBoth_le_one [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) (pk : PK) (sk : SK)
    (st : onoff.St) (ct0 : onoff.C₀) :
    failureAfterBoth kem onoff hDet pk sk st ct0 ≤ 1 := by
  unfold failureAfterBoth
  exact probOutput_false_add_probFailure_le_one _

/-- `failureAfterBoth` is the missing mass of `onoff.encapsOn st pk` plus,
for every returned `(ct₁, k)`, its probability multiplied by the indicator
that decapsulation does not recover `k`. -/
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

end KEMScheme
