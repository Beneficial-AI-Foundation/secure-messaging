/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.EvalDist

/-!
# Failure-Aware Expected Payoff

## Definition

For a probabilistic computation `oa : ProbComp A` and a payoff
`f : A → ℝ≥0∞`, define

```text
E_{x ← oa}[f(x)] := Pr[oa = ⊥] + Σ x, Pr[oa = x] · f(x),
```

where `Pr[oa = ⊥]` is the missing probability mass.  The definition allows
arbitrary payoffs, but for the failure-risk interpretation below we assume
`f(x) ≤ 1` for every `x`.

The first term assigns payoff `1` to a missing output.  The sum is the
expected payoff over returned values.  Under the assumption `f ≤ 1`, a
missing output therefore has the worst possible payoff.

## Failure-Probability Interpretation

In a game-based proof, an output `x` may be the state after one oracle call,
and `f(x)` an upper bound on the probability of eventual failure from that
state.  Then `E_{x ← oa}[f(x)]` combines two sources of failure probability:

* the call produces no next state, which counts as failure; or
* the call produces `x`, leaving future risk `f(x)`.

If a call from state `s` satisfies

```text
E_{x ← oa}[f(x)] ≤ f(s) + ε,
```

then it increases expected risk by at most `ε`.  Iterating this inequality
for `q` calls gives the bound `f(s₀) + q · ε`; when `f(s₀) = 0`, this is
`q · ε`.

## Basic Laws

Recall that `pure a` returns `a` with probability one, `oa >>= ob` samples
`x ← oa` and runs `ob x`, and `g <$> oa` applies `g` to the output of
`oa`.

We prove:

* `expectedPayoff_pure` — `E_{x ← pure a}[f(x)] = f(a)`:
  a deterministic return has payoff `f(a)`;

* `expectedPayoff_bind` —
  `E_{y ← oa >>= ob}[f(y)] = Pr[oa = ⊥] + Σ x, Pr[oa = x] · E_{y ← ob x}[f(y)]`:
  sequential composition averages the second step's expected payoff over the
  first step's outputs;

* `expectedPayoff_map` — `E_{y ← g <$> oa}[f(y)] = E_{x ← oa}[f(g(x))]`:
  mapping an output is equivalent to composing its payoff;

* `expectedPayoff_mono` — `f ≤ g` implies `E_{x ← oa}[f(x)] ≤ E_{x ← oa}[g(x)]`:
  increasing every output's payoff cannot decrease the expected payoff;

* `expectedPayoff_le_one` — `f ≤ 1` implies `E_{x ← oa}[f(x)] ≤ 1`;
  payoffs bounded by `1` have expected payoff at most `1`;

* `expectedPayoff_le_const_of_support` —
  `Pr[oa = ⊥] = 0` and `f ≤ c` on `supp(oa)` imply `E_{x ← oa}[f(x)] ≤ c`:
  without missing mass, a bound on the supported payoffs bounds the expected payoff;

* `expectedPayoff_add_const_le` — `E_{x ← oa}[f(x) + c] ≤ E_{x ← oa}[f(x)] + c`:
  adding `c` to every output's payoff increases the expected payoff by at most `c`.

For a Boolean computation `oc : ProbComp Bool`, write
`m(oc) := Pr[oc = false] + Pr[oc = ⊥]` for its false-or-missing mass.

We prove, for `oa : ProbComp A` and `ob : A → ProbComp Bool`:

* `probOutput_false_add_probFailure_bind` —
  `m(oa >>= ob) = Pr[oa = ⊥] + Σ x, Pr[oa = x] · m(ob x)`:
  sequential composition combines the first step's missing mass with the
  average false-or-missing mass of the second step;

* `probOutput_false_add_probFailure_le_one` — `m(oc) ≤ 1`:
  the false-or-missing mass is at most `1`.
-/

open OracleSpec ENNReal

namespace OracleComp

/-- `Pr[⊥ | oa] + Σ' a, Pr[= a | oa] · payoff a`: the expectation of
`payoff` over the outputs of `oa`, weighting the missing probability mass
with unit payoff `1`. -/
noncomputable def expectedPayoff {A : Type}
    (oa : ProbComp A) (payoff : A → ℝ≥0∞) : ℝ≥0∞ :=
  Pr[⊥ | oa] + ∑' a, Pr[= a | oa] * payoff a

/-- `expectedPayoff (pure a) payoff = payoff a`. -/
lemma expectedPayoff_pure {A : Type} (a : A) (payoff : A → ℝ≥0∞) :
    expectedPayoff (pure a : ProbComp A) payoff = payoff a := by
  unfold expectedPayoff
  simp only [probFailure_pure, zero_add]
  rw [tsum_eq_single a]
  · simp
  · intro b hba
    simp [hba]

/-- The expected payoff of `oa >>= ob` is `oa`'s missing mass plus the
average over `oa`'s outputs of the expected payoff of `ob`. -/
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

/-- `expectedPayoff (f <$> oa) payoff = expectedPayoff oa (payoff ∘ f)`. -/
lemma expectedPayoff_map {A B : Type} (f : A → B) (oa : ProbComp A)
    (payoff : B → ℝ≥0∞) :
    expectedPayoff (f <$> oa) payoff = expectedPayoff oa (fun a => payoff (f a)) := by
  rw [map_eq_bind_pure_comp, expectedPayoff_bind]
  simp only [Function.comp_apply, expectedPayoff_pure]
  rfl

/-- `expectedPayoff` is monotone in the payoff. -/
lemma expectedPayoff_mono {A : Type} (oa : ProbComp A)
    (f g : A → ℝ≥0∞) (hfg : ∀ a, f a ≤ g a) :
    expectedPayoff oa f ≤ expectedPayoff oa g := by
  unfold expectedPayoff
  exact add_le_add le_rfl
    (ENNReal.tsum_le_tsum fun a => mul_le_mul' le_rfl (hfg a))

/-- A payoff bounded by `1` has expected payoff at most `1`. -/
lemma expectedPayoff_le_one {A : Type} (oa : ProbComp A)
    (f : A → ℝ≥0∞) (hf : ∀ a, f a ≤ 1) :
    expectedPayoff oa f ≤ 1 := by
  calc
    expectedPayoff oa f ≤ expectedPayoff oa (fun _ => 1) :=
      expectedPayoff_mono oa f (fun _ => 1) hf
    _ = 1 := by simp [expectedPayoff]

/-- For a computation without missing mass, a payoff bounded by `c` on the
support has expected payoff at most `c`. -/
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

/-- Shifting the payoff by a constant shifts the expected payoff by at most
that constant. -/
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

/-- The false-or-missing mass of `oa >>= ob` is `oa`'s missing mass plus
the average over `oa`'s outputs of the false-or-missing mass of `ob`. -/
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

/-- `Pr[= false | oa] + Pr[⊥ | oa] ≤ 1` for a Boolean computation. -/
lemma probOutput_false_add_probFailure_le_one (oa : ProbComp Bool) :
    Pr[= false | oa] + Pr[⊥ | oa] ≤ 1 := by
  calc
    Pr[= false | oa] + Pr[⊥ | oa] ≤
        (∑' b : Bool, Pr[= b | oa]) + Pr[⊥ | oa] := by
      exact add_le_add (ENNReal.le_tsum false) le_rfl
    _ = 1 := tsum_probOutput_add_probFailure oa

end OracleComp
