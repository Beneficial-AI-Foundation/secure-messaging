/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.EvalDist.Sum

/-!
# Failure-Aware Expected Payoff

For a probabilistic computation `oa : ProbComp A` and a function
`f : A → ℝ≥0∞`, define

```text
expectedPayoff oa f := prFail oa + Σ a, Pr[oa = a] · f(a).
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
* `probEvent_le_expectedPayoff` — an event on which every payoff is at least
  `1` has probability at most the expected payoff;
* `expectedPayoff_le_const_of_support` — without missing mass, a bound on every
  possible output payoff bounds the expectation;
* `expectedPayoff_add_const_le` — adding `c` to every returned-output payoff
  increases the expectation by at most `c`.

For a Boolean computation `oc`, assigning payoff `0` to `true` and `1` to
`false` gives its false-or-missing mass:

```text
Pr[oc = false] + prFail oc.
```

The final two lemmas describe this quantity under sequential composition and
show that it is at most `1`.

Under VCVio's measure semantics a `ProbComp` never fails, so `prFail` is `0`
(`OracleComp.prFail_eq_zero`); the missing-mass terms are kept so that the
statements read the same as for a failing monad.
-/

open OracleSpec ENNReal

namespace OracleComp

/-- Failure-aware expectation of `payoff`: a missing output contributes `1`,
while a returned value `a` contributes `payoff a`. -/
noncomputable def expectedPayoff {A : Type}
    (oa : ProbComp A) (payoff : A → ℝ≥0∞) : ℝ≥0∞ :=
  prFail oa + ∑' a, Pr{let x ← oa}[x = a] * payoff a

/-- A computation that deterministically returns `a` has payoff `payoff a`. -/
lemma expectedPayoff_pure {A : Type} (a : A) (payoff : A → ℝ≥0∞) :
    expectedPayoff (pure a : ProbComp A) payoff = payoff a := by
  simp only [expectedPayoff, prFail_eq_zero, zero_add]
  exact tsum_prEvent_pure_mul a payoff

/-- Sequential composition adds the first computation's missing mass to the
average continuation payoff. -/
lemma expectedPayoff_bind {A B : Type} (oa : ProbComp A)
    (ob : A → ProbComp B) (payoff : B → ℝ≥0∞) :
    expectedPayoff (oa >>= ob) payoff =
      prFail oa + ∑' a, Pr{let x ← oa}[x = a] * expectedPayoff (ob a) payoff := by
  simp only [expectedPayoff, prFail_eq_zero, zero_add]
  exact tsum_prEvent_bind_mul oa ob payoff

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

/-- An event on which every payoff is at least `1` has probability at most the expected
payoff. -/
lemma probEvent_le_expectedPayoff {A : Type} (oa : ProbComp A) (p : A → Prop)
    (f : A → ℝ≥0∞) (hf : ∀ a, p a → 1 ≤ f a) :
    Pr{let x ← oa}[p x] ≤ expectedPayoff oa f :=
  (prEvent_le_tsum_prEvent_mul_cost oa p f hf).trans le_add_self

/-- If `oa` has no missing mass and every possible output has payoff at most
`c`, then its expected payoff is at most `c`. -/
lemma expectedPayoff_le_const_of_support {A : Type} (oa : ProbComp A)
    (f : A → ℝ≥0∞) (c : ℝ≥0∞) (hnf : prFail oa = 0)
    (hf : ∀ a ∈ support oa, f a ≤ c) :
    expectedPayoff oa f ≤ c := by
  unfold expectedPayoff
  rw [hnf, zero_add]
  calc
    (∑' a, Pr{let x ← oa}[x = a] * f a) ≤ ∑' a, Pr{let x ← oa}[x = a] * c := by
      refine ENNReal.tsum_le_tsum fun a => ?_
      by_cases ha : a ∈ support oa
      · exact mul_le_mul' le_rfl (hf a ha)
      · simp only [prEvent_eq_zero_of_not_mem_support oa ha, zero_mul, le_refl]
    _ = (∑' a, Pr{let x ← oa}[x = a]) * c := ENNReal.tsum_mul_right
    _ ≤ 1 * c := mul_le_mul' (OracleComp.tsum_prEvent_le_one _) le_rfl
    _ = c := one_mul c

/-- Adding `c` to every returned-output payoff increases the failure-aware
expectation by at most `c`. -/
lemma expectedPayoff_add_const_le {A : Type} (oa : ProbComp A)
    (f : A → ℝ≥0∞) (c : ℝ≥0∞) :
    expectedPayoff oa (fun a => f a + c) ≤ expectedPayoff oa f + c := by
  unfold expectedPayoff
  calc
    prFail oa + (∑' a, Pr{let x ← oa}[x = a] * (f a + c)) =
        (prFail oa + ∑' a, Pr{let x ← oa}[x = a] * f a) +
          ∑' a, Pr{let x ← oa}[x = a] * c := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add]
      ac_rfl
    _ = (prFail oa + ∑' a, Pr{let x ← oa}[x = a] * f a) +
        (∑' a, Pr{let x ← oa}[x = a]) * c := by
      rw [ENNReal.tsum_mul_right]
    _ ≤ (prFail oa + ∑' a, Pr{let x ← oa}[x = a] * f a) + 1 * c := by
      exact add_le_add le_rfl (mul_le_mul' (OracleComp.tsum_prEvent_le_one _) le_rfl)
    _ = (prFail oa + ∑' a, Pr{let x ← oa}[x = a] * f a) + c := by rw [one_mul]

/-- The false-or-missing mass of sequential composition is the first
computation's missing mass plus the average false-or-missing mass of the
second. -/
lemma probOutput_false_add_probFailure_bind {A : Type} (oa : ProbComp A)
    (ob : A → ProbComp Bool) :
    Pr{let x ← oa >>= ob}[x = false] + prFail (oa >>= ob) =
      prFail oa + ∑' a, Pr{let x ← oa}[x = a] *
        (Pr{let x ← ob a}[x = false] + prFail (ob a)) := by
  simp only [prFail_eq_zero, zero_add, add_zero]
  exact prEvent_bind_eq_tsum oa ob _

/-- The false-or-missing mass of a Boolean computation is at most `1`. -/
lemma probOutput_false_add_probFailure_le_one (oa : ProbComp Bool) :
    Pr{let x ← oa}[x = false] + prFail oa ≤ 1 := by
  rw [prFail_eq_zero, add_zero]
  exact (ENNReal.le_tsum (f := fun b => Pr{let x ← oa}[x = b]) false).trans
    (tsum_prEvent_le_one oa)

end OracleComp
