/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.EvalDist

/-!
# Failure-Aware Expected Payoff

For a probabilistic computation `oa : ProbComp A` and a function
`f : A → ℝ≥0∞`, define

```text
expectedPayoff oa f := Pr[oa = ⊥] + Σ a, Pr[oa = a] · f(a).
```

This assigns payoff `1` to a missing output and payoff `f(a)` to a returned
value `a`.  When `f(a) ≤ 1` for every `a`, the missing-output payoff is the
maximum payoff and can be interpreted as maximum penalty.

If `f(a)` bounds the probability of eventual failure from a state `a`, then
`expectedPayoff oa f` combines failure of `oa` itself with the expected
remaining failure probability after a returned output.

## Proved properties

Relative to the monad structure of `ProbComp`:

* `expectedPayoff_pure` — a deterministic computation has the payoff assigned
  to its output;
* `expectedPayoff_bind` — sequential composition adds the first computation's
  missing mass to the average continuation payoff;
* `expectedPayoff_map` — mapping outputs is equivalent to composing the payoff
  function with the map;
* `expectedPayoff_mono` — increasing every output payoff cannot decrease the
  expected payoff;
* `expectedPayoff_le_one` — payoffs bounded by `1` have expected payoff at
  most `1`;
* `expectedPayoff_le_const_of_support` — without missing mass, a bound on every
  possible output payoff bounds the expectation;
* `expectedPayoff_add_const_le` — adding `c` to every returned-output payoff
  increases the expectation by at most `c`.

For a Boolean computation `oc`, assigning payoff `0` to `true` and `1` to
`false` gives its false-or-missing mass:

```text
Pr[oc = false] + Pr[oc = ⊥].
```

The final two lemmas describe this quantity under sequential composition and
show that it is at most `1`.
-/

open OracleSpec ENNReal

namespace OracleComp

/-- Failure-aware expectation of `payoff`: a missing output contributes `1`,
while a returned value `a` contributes `payoff a`. -/
noncomputable def expectedPayoff {A : Type}
    (oa : ProbComp A) (payoff : A → ℝ≥0∞) : ℝ≥0∞ :=
  Pr[⊥ | oa] + ∑' a, Pr[= a | oa] * payoff a

/-- A computation that deterministically returns `a` has payoff `payoff a`. -/
lemma expectedPayoff_pure {A : Type} (a : A) (payoff : A → ℝ≥0∞) :
    expectedPayoff (pure a : ProbComp A) payoff = payoff a := by
  unfold expectedPayoff
  simp only [probFailure_pure, zero_add]
  rw [tsum_eq_single a]
  · simp
  · intro b hba
    simp [hba]

/-- Sequential composition adds the first computation's missing mass to the
average continuation payoff. -/
lemma expectedPayoff_bind {A B : Type} (oa : ProbComp A)
    (ob : A → ProbComp B) (payoff : B → ℝ≥0∞) :
    expectedPayoff (oa >>= ob) payoff =
      Pr[⊥ | oa] + ∑' a, Pr[= a | oa] * expectedPayoff (ob a) payoff := by
  unfold expectedPayoff
  rw [probFailure_bind_eq_add_tsum]
  have hout :
      (∑' b, Pr[= b | oa >>= ob] * payoff b) =
        ∑' b, ∑' a, Pr[= a | oa] * Pr[= b | ob a] * payoff b := by
    refine tsum_congr fun b => ?_
    rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_right]
  calc
    (Pr[⊥ | oa] + ∑' a, Pr[= a | oa] * Pr[⊥ | ob a]) +
        ∑' b, Pr[= b | oa >>= ob] * payoff b =
        Pr[⊥ | oa] + ((∑' a, Pr[= a | oa] * Pr[⊥ | ob a]) +
          ∑' b, ∑' a, Pr[= a | oa] * Pr[= b | ob a] * payoff b) := by
      rw [hout]
      ac_rfl
    _ = Pr[⊥ | oa] + ((∑' a, Pr[= a | oa] * Pr[⊥ | ob a]) +
        ∑' a, ∑' b, Pr[= a | oa] * Pr[= b | ob a] * payoff b) := by
      rw [ENNReal.tsum_comm]
    _ = Pr[⊥ | oa] + ∑' a, Pr[= a | oa] *
        (Pr[⊥ | ob a] + ∑' b, Pr[= b | ob a] * payoff b) := by
      congr 1
      rw [← ENNReal.tsum_add]
      refine tsum_congr fun a => ?_
      rw [mul_add]
      simp_rw [mul_assoc]
      rw [ENNReal.tsum_mul_left]

/-- Applying `f` to each output before evaluating `payoff` is equivalent to
evaluating `payoff (f a)` on the original output. -/
lemma expectedPayoff_map {A B : Type} (f : A → B) (oa : ProbComp A)
    (payoff : B → ℝ≥0∞) :
    expectedPayoff (f <$> oa) payoff = expectedPayoff oa (fun a => payoff (f a)) := by
  rw [map_eq_bind_pure_comp, expectedPayoff_bind]
  simp only [Function.comp_apply, expectedPayoff_pure]
  rfl

/-- Increasing every returned-output payoff cannot decrease its expectation. -/
lemma expectedPayoff_mono {A : Type} (oa : ProbComp A)
    (f g : A → ℝ≥0∞) (hfg : ∀ a, f a ≤ g a) :
    expectedPayoff oa f ≤ expectedPayoff oa g := by
  unfold expectedPayoff
  exact add_le_add le_rfl
    (ENNReal.tsum_le_tsum fun a => mul_le_mul' le_rfl (hfg a))

/-- If every returned-output payoff is at most `1`, so is its failure-aware
expectation. -/
lemma expectedPayoff_le_one {A : Type} (oa : ProbComp A)
    (f : A → ℝ≥0∞) (hf : ∀ a, f a ≤ 1) :
    expectedPayoff oa f ≤ 1 := by
  calc
    expectedPayoff oa f ≤ expectedPayoff oa (fun _ => 1) :=
      expectedPayoff_mono oa f (fun _ => 1) hf
    _ = 1 := by simp [expectedPayoff]

/-- If `oa` has no missing mass and every possible output has payoff at most
`c`, then its expected payoff is at most `c`. -/
lemma expectedPayoff_le_const_of_support {A : Type} (oa : ProbComp A)
    (f : A → ℝ≥0∞) (c : ℝ≥0∞) (hnf : Pr[⊥ | oa] = 0)
    (hf : ∀ a ∈ support oa, f a ≤ c) :
    expectedPayoff oa f ≤ c := by
  unfold expectedPayoff
  rw [hnf, zero_add]
  calc
    (∑' a, Pr[= a | oa] * f a) ≤ ∑' a, Pr[= a | oa] * c := by
      refine ENNReal.tsum_le_tsum fun a => ?_
      by_cases ha : a ∈ support oa
      · exact mul_le_mul' le_rfl (hf a ha)
      · simp [(probOutput_eq_zero_iff _ _).2 ha]
    _ = (∑' a, Pr[= a | oa]) * c := ENNReal.tsum_mul_right
    _ ≤ 1 * c := mul_le_mul' tsum_probOutput_le_one le_rfl
    _ = c := one_mul c

/-- Adding `c` to every returned-output payoff increases the failure-aware
expectation by at most `c`. -/
lemma expectedPayoff_add_const_le {A : Type} (oa : ProbComp A)
    (f : A → ℝ≥0∞) (c : ℝ≥0∞) :
    expectedPayoff oa (fun a => f a + c) ≤ expectedPayoff oa f + c := by
  unfold expectedPayoff
  calc
    Pr[⊥ | oa] + (∑' a, Pr[= a | oa] * (f a + c)) =
        (Pr[⊥ | oa] + ∑' a, Pr[= a | oa] * f a) +
          ∑' a, Pr[= a | oa] * c := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add]
      ac_rfl
    _ = (Pr[⊥ | oa] + ∑' a, Pr[= a | oa] * f a) +
        (∑' a, Pr[= a | oa]) * c := by
      rw [ENNReal.tsum_mul_right]
    _ ≤ (Pr[⊥ | oa] + ∑' a, Pr[= a | oa] * f a) + 1 * c := by
      exact add_le_add le_rfl (mul_le_mul' tsum_probOutput_le_one le_rfl)
    _ = (Pr[⊥ | oa] + ∑' a, Pr[= a | oa] * f a) + c := by rw [one_mul]

/-- The false-or-missing mass of sequential composition is the first
computation's missing mass plus the average false-or-missing mass of the
second. -/
lemma probOutput_false_add_probFailure_bind {A : Type} (oa : ProbComp A)
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

/-- The false-or-missing mass of a Boolean computation is at most `1`. -/
lemma probOutput_false_add_probFailure_le_one (oa : ProbComp Bool) :
    Pr[= false | oa] + Pr[⊥ | oa] ≤ 1 := by
  calc
    Pr[= false | oa] + Pr[⊥ | oa] ≤
        (∑' b : Bool, Pr[= b | oa]) + Pr[⊥ | oa] := by
      exact add_le_add (ENNReal.le_tsum false) le_rfl
    _ = 1 := tsum_probOutput_add_probFailure oa

end OracleComp
