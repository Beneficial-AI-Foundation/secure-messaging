/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.OnOffKEM.Defs
import ToVCVio.OracleComp.ExpectedRisk
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-!
# On/Off KEM — Correctness Error by Sampling Stage

This file establishes two related results for an on/off KEM:

* its factorized (offline / online) encapsulation gives a staged correctness experiment equal to
  the standard KEM correctness experiment;
* its correctness error can be decomposed by fixing the key-pair sample, the offline sample,
  or both, then averaging the remaining error.

Together they let a protocol proof track residual KEM correctness risk against the
samples already drawn, then average back to the ordinary `correctnessError`.


# Context

Let `kem` be a KEM scheme and `onoff` an on/off factorization of its encapsulation
algorithm:

* `onoff.encapsOff` produces state `st` and the offline ciphertext part `ct₀`
  without using a public key;
* `onoff.encapsOn st pk` uses `st` and a public key `pk` to produce the online
  ciphertext part `ct₁` and the encapsulated key `k`.

The equivalence `onoff.split : C ≃ C₀ × C₁` identifies a KEM ciphertext with
its offline and online parts.  Its inverse joins `(ct₀, ct₁)` into the
ciphertext passed to decapsulation.

We denote by `Pr[X = x]` the probability that `X : ProbComp α` returns `x`,
and by `Pr[X = ⊥]` its missing probability mass.

The standard KEM correctness error is defined as:

```text
kem.correctnessError ProbCompRuntime.probComp
  = 1 - Pr[kem.CorrectExp = true]
  = Pr[kem.CorrectExp = false] + Pr[kem.CorrectExp = ⊥].
```

## 1. Staged correctness experiment

The experiment `factorCorrectExp` runs key generation and both encapsulation
stages, then checks whether decapsulation recovers the encapsulated key:

```text
factorCorrectExp := do
  (pk, sk) ← kem.keygen
  (st, ct₀) ← onoff.encapsOff
  (ct₁, k) ← onoff.encapsOn st pk
  return hDet.decapsDet sk (onoff.split.symm (ct₀, ct₁)) = some k
```

Here, `hDet` records the additional assumption that decapsulation is
deterministic.

The theorem `factorCorrectExp_eq_correctExp` proves that this staged experiment
is equal to the standard KEM correctness experiment `kem.CorrectExp`.

The theorem `factorCorrectnessError_eq` is a corollary showing the errors
in the two experiments are equal.

## 2. Stage-specific error decomposition

The stage-specific errors fix outputs of one or both of the first two sampling
stages and measure the error that remains:

* `failureAfterBoth` (`χ`) — the online encapsulation error after fixing the
  key pair and offline sample;
* `failureAfterKeypair` (`φ`) — the average of `χ` over offline encapsulation
  after fixing the key pair;
* `failureAfterOff` (`ψ`) — the average of `χ` over key generation after
  fixing the offline sample.

Each function treats its arguments as fixed inputs and counts missing
probability mass as error.

Writing `KG := kem.keygen` and `OFF := onoff.encapsOff`, the total KEM error
`ε` has two equivalent decompositions:

* `factorCorrectnessError_eq_avg_keypair` proves
  `ε = Pr[KG = ⊥] + Σ (pk, sk), Pr[KG = (pk, sk)] · φ(pk, sk)`;
* `factorCorrectnessError_eq_avg_off` proves
  `ε = Pr[OFF = ⊥] + Σ (st, ct₀), Pr[OFF = (st, ct₀)] · ψ(st, ct₀)`.
-/

open OracleSpec OracleComp ENNReal

namespace KEMScheme

variable {K PK SK C : Type}

/-! ## 1. Staged correctness experiment -/

/-- The KEM correctness experiment expressed through the on/off factorization.
It samples `(pk, sk) ← kem.keygen`, `(st, ct₀) ← onoff.encapsOff`, and
`(ct₁, k) ← onoff.encapsOn st pk`, then returns whether decapsulating the
joined ciphertext recovers `k`. -/
def factorCorrectExp [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) : ProbComp Bool := do
  let (pk, sk) ← kem.keygen
  let (st, ct0) ← onoff.encapsOff
  let (ct1, key) ← onoff.encapsOn st pk
  pure (decide
    (hDet.decapsDet sk (onoff.split.symm (ct0, ct1)) = some key))

/-- `factorCorrectExp` and the ordinary KEM correctness experiment
`kem.CorrectExp` are equal as programs. -/
theorem factorCorrectExp_eq_correctExp [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) :
    factorCorrectExp kem onoff hDet = kem.CorrectExp := by
  unfold factorCorrectExp KEMScheme.CorrectExp
  simp_rw [onoff.factor, hDet.decaps_eq]
  simp only [bind_assoc, pure_bind]

/-- The total correctness error of `factorCorrectExp`: the probability of a
`false` result plus the missing probability mass. -/
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

/-! ### 2. Stage-specific error decomposition -/

/-- The online correctness experiment after fixing `pk`, `sk`, `st`, and
`ct₀`.  It samples `(ct₁, k) ← onoff.encapsOn st pk` and returns whether
decapsulation recovers `k`. -/
private def onlineCorrectExp [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) (pk : PK) (sk : SK)
    (st : onoff.St) (ct0 : onoff.C₀) : ProbComp Bool := do
  let (ct1, key) ← onoff.encapsOn st pk
  pure (decide
    (hDet.decapsDet sk (onoff.split.symm (ct0, ct1)) = some key))

/-- `χ(pk, sk, st, ct₀)`, the correctness error of `onlineCorrectExp` after
fixing the key pair and offline sample.
It is the probability (taken over random choices in `onoff.encapsOn`) that the
experiment returns `false` plus the probability that it produces no output. -/
noncomputable def failureAfterBoth [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) (pk : PK) (sk : SK)
    (st : onoff.St) (ct0 : onoff.C₀) : ℝ≥0∞ :=
  Pr[= false | onlineCorrectExp kem onoff hDet pk sk st ct0] +
    Pr[⊥ | onlineCorrectExp kem onoff hDet pk sk st ct0]

/-- `φ(pk, sk)`, the correctness error after fixing the key pair.  It is the
missing probability mass of `onoff.encapsOff` plus the probability-weighted average of
`failureAfterBoth` over its returned offline samples. -/
noncomputable def failureAfterKeypair [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) (pk : PK) (sk : SK) : ℝ≥0∞ :=
  Pr[⊥ | onoff.encapsOff] +
    ∑' off : onoff.St × onoff.C₀,
      Pr[= off | onoff.encapsOff] *
        failureAfterBoth kem onoff hDet pk sk off.1 off.2

/-- `ψ(st, ct₀)`, the correctness error after fixing the offline sample.  It is
the missing probability mass of `kem.keygen` plus the probability-weighted average of
`failureAfterBoth` over its returned key pairs. -/
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
