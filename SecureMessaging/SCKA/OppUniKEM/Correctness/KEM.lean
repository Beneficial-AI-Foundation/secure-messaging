/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Construction
import ToVCVio.OracleComp.ExpectedPayoff
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-!
# Opp-UniKEM-CKA — Conditional KEM Error

One Opp-UniKEM epoch runs a single KEM instance in three sampling stages:
party A draws a key pair, party B draws the offline part of an
encapsulation and later its online part.  This module considers that KEM
instance in isolation: its total correctness error, its conditional errors
after some of the samples are fixed, and the averaging identities relating
the two, in the form used by `Correctness.Reduction`.

Let `kem` be a KEM scheme, `onoff` an on/off factorization for it, and
`hDet` a deterministic decapsulation witness.  The three samples are

```text
(pk, sk) ← KG,   (st, ct₀) ← OFF,   (ct₁, k) ← ON st pk,   where

KG       := kem.keygen
OFF      := onoff.encapsOff
ON st pk := onoff.encapsOn st pk,
```

and the epoch fails when decapsulation misses the key:

```text
bad(sk, ct₀, ct₁, k) := hDet.decapsDet sk (join (ct₀, ct₁)) ≠ some k,
join := onoff.split⁻¹ : C₀ × C₁ → C.     -- the inverse of the on/off split
```

For `X : ProbComp α`, `Pr[X = x]` is an output probability and `Pr[X = ⊥]`
is the missing probability mass.

## Staged experiment

The experiment `F` (`factorCorrectExp`) draws the three samples and tests
failure:

```text
F := do  (pk, sk) ← KG;  (st, ct₀) ← OFF;  (ct₁, k) ← ON st pk
         return ¬bad(sk, ct₀, ct₁, k)
```

We show (`factorCorrectExp_eq_correctExp`) that `F` and the ordinary KEM
correctness experiment `kem.CorrectExp` — sample a key pair, encapsulate,
check that decapsulation returns the key — are equal as programs, so in
particular produce the same output distribution.  This uses:

* `onoff.factor` — sampling `OFF` then `ON st pk` and joining the two
  ciphertext parts is, as a program, equal to `kem.encaps pk`;
* `hDet.decaps_eq` — decapsulation is the deterministic function
  `hDet.decapsDet`.

Hence the total error of `F` (`factorCorrectnessError`)

```text
ε := Pr[F = false] + Pr[F = ⊥]
```

equals `kem.correctnessError` (`factorCorrectnessError_eq`).

## Conditional errors

`F`'s first two samples are independent.  Fixing one or both of them and
drawing the rest defines

```text
χ(pk, sk, st, ct₀) := Pr[ON st pk = ⊥]
    + Σ (ct₁, k), Pr[ON st pk = (ct₁, k)] · (if bad(sk, ct₀, ct₁, k) then 1 else 0)

φ(pk, sk)  := Pr[OFF = ⊥] + Σ (st, ct₀), Pr[OFF = (st, ct₀)] · χ(pk, sk, st, ct₀)

ψ(st, ct₀) := Pr[KG = ⊥]  + Σ (pk, sk),  Pr[KG = (pk, sk)]  · χ(pk, sk, st, ct₀)
```

— in Lean `failureAfterBoth`, `failureAfterKeypair`, `failureAfterOff`: the
residual failure probability after fixing both first-stage samples, only the
key pair, or only the offline sample.

## Averaging identities

We prove, for `ε` the total error of `F` defined above:

* `factor_failure_tower_keypair` —
  `ε = Pr[KG = ⊥] + Σ (pk, sk), Pr[KG = (pk, sk)] · φ(pk, sk)`;
* `factor_failure_tower_off` —
  `ε = Pr[OFF = ⊥] + Σ (st, ct₀), Pr[OFF = (st, ct₀)] · ψ(st, ct₀)`;
* `failureAfterBoth_le_one`, `failureAfterKeypair_le_one`,
  `failureAfterOff_le_one` — `χ, φ, ψ ≤ 1`.
-/

open OracleSpec OracleComp ENNReal KEMScheme

namespace oppUniKemCKA

universe u

variable {K PK SK C : Type}

/-! ## Staged KEM correctness experiment -/

/-- The KEM correctness experiment staged as in the Opp-UniKEM protocol:
sample `(pk, sk) ← kem.keygen`, `(st, ct₀) ← onoff.encapsOff`, and
`(ct₁, k) ← onoff.encapsOn st pk`, and return whether decapsulating the
joined ciphertext recovers the key:
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

/-- `factorCorrectnessError` equals `kem.correctnessError`. -/
theorem factorCorrectnessError_eq [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) :
    factorCorrectnessError kem onoff hDet =
      kem.correctnessError ProbCompRuntime.probComp := by
  rw [factorCorrectnessError, factorCorrectExp_eq_correctExp]
  exact (KEMScheme.correctnessError_eq_probOutput_false_add_probFailure
    kem ProbCompRuntime.probComp).symm

/-! ### Conditional KEM errors

The conditional error of an epoch that has drawn only its key pair or only
its offline sample may exceed `ε`; only its average over the fixed sample
is `ε` (the identities below). -/

/-- The online stage of `factorCorrectExp` with `pk`, `sk`, `st`, `ct₀`
fixed: sample `(ct₁, k) ← onoff.encapsOn st pk` and return whether
`hDet.decapsDet sk (onoff.split.symm (ct₀, ct₁)) = some k`. -/
private def onlineCorrectExp [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) (pk : PK) (sk : SK)
    (st : onoff.St) (ct0 : onoff.C₀) : ProbComp Bool := do
  let (ct1, key) ← onoff.encapsOn st pk
  pure (decide
    (hDet.decapsDet sk (onoff.split.symm (ct0, ct1)) = some key))

/-- `χ(pk, sk, st, ct₀)`, the conditional KEM correctness error with the
key pair and the offline sample fixed: the probability that
`(ct₁, k) ← onoff.encapsOn st pk` gives
`hDet.decapsDet sk (onoff.split.symm (ct₀, ct₁)) ≠ some k`, plus the
sampler's missing probability mass. -/
noncomputable def failureAfterBoth [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) (pk : PK) (sk : SK)
    (st : onoff.St) (ct0 : onoff.C₀) : ℝ≥0∞ :=
  Pr[= false | onlineCorrectExp kem onoff hDet pk sk st ct0] +
    Pr[⊥ | onlineCorrectExp kem onoff hDet pk sk st ct0]

/-- `φ(pk, sk)`, the conditional KEM correctness error with the key pair
fixed: the average of `failureAfterBoth` over `(st, ct₀) ← onoff.encapsOff`,
plus the sampler's missing probability mass. -/
noncomputable def failureAfterKeypair [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) (pk : PK) (sk : SK) : ℝ≥0∞ :=
  Pr[⊥ | onoff.encapsOff] +
    ∑' off : onoff.St × onoff.C₀,
      Pr[= off | onoff.encapsOff] *
        failureAfterBoth kem onoff hDet pk sk off.1 off.2

/-- `ψ(st, ct₀)`, the conditional KEM correctness error with the offline
sample fixed: the average of `failureAfterBoth` over
`(pk, sk) ← kem.keygen`, plus the sampler's missing probability mass. -/
noncomputable def failureAfterOff [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem) (st : onoff.St) (ct0 : onoff.C₀) : ℝ≥0∞ :=
  Pr[⊥ | kem.keygen] +
    ∑' kp : PK × SK, Pr[= kp | kem.keygen] *
      failureAfterBoth kem onoff hDet kp.1 kp.2 st ct0

/-- Averaging `failureAfterKeypair` over `kem.keygen` gives
`factorCorrectnessError`. -/
lemma factor_failure_tower_keypair [DecidableEq K]
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

/-- Averaging `failureAfterOff` over `onoff.encapsOff` gives
`factorCorrectnessError`. -/
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

/-- `failureAfterBoth` equals the missing probability mass of
`onoff.encapsOn st pk` plus the sum, over its outcomes `(ct₁, k)`, of their
probabilities when decapsulation fails on them. -/
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
