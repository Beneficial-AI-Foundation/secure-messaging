/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.EvalDist

/-!
# Failure-Aware Expected Risk

## Risk functions

A *risk* on a type `A` is a function `f : A → ℝ≥0∞` such that `f a ≤ 1` for
every `a`.  The intended meaning is that `f a` upper-bounds a failure
probability at outcome `a`.

## Definition

For `oa : ProbComp A` and a risk `f` on `A`, define

```text
expectedRisk oa f  =  E_{x ← oa}[f(x)]
                   := Pr[oa = ⊥] + Σ_x Pr[oa = x] · f(x).
```

The failure probability `Pr[oa = ⊥]` is assigned a maximum risk value `1`.

## Interpretation

If `f(x)` bounds the probability of eventual failure from a state `x`
produced by one step `oa`, then `E_{x ← oa}[f(x)]` accounts for:

* failure of the step (`oa` returns `⊥`, charged `1`); and
* continuation risk `f(x)` when the step returns `x`.

If for every state `s` one has `E_{x ← oa_s}[f(x)] ≤ f(s) + ε`, then after
`q` steps from an initial state `s₀` the expected risk is at most
`f(s₀) + q · ε` (and `q · ε` when `f(s₀) = 0`).

## Proved properties

Relative to the monad structure of `ProbComp` (`pure`, bind `>>=`, map `<$>`), we show:

* `expectedRisk_pure` —
  `E_{x ← pure a}[f(x)] = f(a)`:
  a deterministic computation has exactly the risk assigned to its output;
* `expectedRisk_bind` —
  `E_{y ← oa >>= ob}[f(y)] =
     Pr[oa = ⊥] + Σ_x Pr[oa = x] · E_{y ← ob x}[f(y)]`:
  sequential composition averages the risk of the second computation over
  outputs of the first;
* `expectedRisk_map` —
  `E_{y ← g <$> oa}[f(y)] = E_{x ← oa}[(f ∘ g)(x)]`:
  transforming an output is equivalent to transforming its risk function;
* `expectedRisk_mono` —
  `f ≤ g` pointwise implies `E_{x ← oa}[f(x)] ≤ E_{x ← oa}[g(x)]`:
  increasing every output risk cannot decrease the expected risk;
* `expectedRisk_le_one` —
  `E_{x ← oa}[f(x)] ≤ 1`:
  expected risk is bounded by 1;
* `expectedRisk_le_const_of_support` —
  `Pr[oa = ⊥] = 0` and `f ≤ c` on `support oa` imply
  `E_{x ← oa}[f(x)] ≤ c`:
  when the computation always returns, a bound on every possible output
  bounds its expected risk;
* `expectedRisk_add_const_le` —
  `expectedRiskOfFun oa (fun x ↦ f(x) + c) ≤ expectedRisk oa f + c`:
  adding `c` to each returned-output risk increases the expectation by at
  most `c`.

For a Boolean computation `oc`, assign risk `0` to `true` and risk `1` to
`false`. Its overall expected risk is

`m(oc) := E_{b ← oc}[if b then 0 else 1] = Pr[oc = false] + Pr[oc = ⊥]`.

* `probOutput_false_add_probFailure_bind` — for all `oa : ProbComp A` and
  `ob : A → ProbComp Bool`,
  `m(oa >>= ob) = Pr[oa = ⊥] + Σ_x Pr[oa = x] · m(ob x)`:
  sequential composition averages the second computation's false-or-missing
  mass over outputs of the first;
* `probOutput_false_add_probFailure_le_one` — for all `oc : ProbComp Bool`,
  `m(oc) ≤ 1`:
  false-or-missing mass is at most the total probability mass.
-/

open OracleSpec ENNReal

namespace OracleComp

/-- A risk on `A` assigns each value a failure-probability bound at most `1`. -/
structure Risk (A : Type) where
  /-- Underlying function. -/
  toFun : A → ℝ≥0∞
  /-- Proof that every assigned risk is at most `1`. -/
  le_one : ∀ a, toFun a ≤ 1

namespace Risk

/-- Coerce a risk to its underlying function. -/
instance {A : Type} : CoeFun (Risk A) (fun _ => A → ℝ≥0∞) where
  coe := Risk.toFun

/-- Given a risk `f` on `B` and a function `g : A → B`, `f.comp g` is the
risk on `A` that assigns each `a` the risk of `g a`. -/
def comp {A B : Type} (f : Risk B) (g : A → B) : Risk A where
  toFun := fun a => f.toFun (g a)
  le_one := fun a => f.le_one (g a)

/-- The constant risk with value `c`, given `c ≤ 1`. -/
def const {A : Type} (c : ℝ≥0∞) (hc : c ≤ 1) : Risk A where
  toFun := fun _ => c
  le_one := fun _ => hc

/-- As a function, `f.comp g` assigns each `a` the risk `f (g a)`. -/
@[simp] lemma coe_comp {A B : Type} (f : Risk B) (g : A → B) :
    ⇑(f.comp g) = fun a => f (g a) := rfl

/-- As a function, `const c hc` assigns the risk `c` to every input. -/
@[simp] lemma coe_const {A : Type} (c : ℝ≥0∞) (hc : c ≤ 1) :
    ⇑(const (A := A) c hc) = fun _ => c := rfl

end Risk

/-- Failure-aware expectation for an arbitrary function `g`: a missing output
contributes `1`, while a returned value `a` contributes `g a`. -/
noncomputable def expectedRiskOfFun {A : Type}
    (oa : ProbComp A) (g : A → ℝ≥0∞) : ℝ≥0∞ :=
  Pr[⊥ | oa] + ∑' a, Pr[= a | oa] * g a

/-- Expected risk of running `oa`: a missing output contributes `1`, while a
returned value `a` contributes `f a`. -/
noncomputable def expectedRisk {A : Type}
    (oa : ProbComp A) (f : Risk A) : ℝ≥0∞ :=
  expectedRiskOfFun oa f

/-- Viewing a risk as an ordinary function does not change its expected value. -/
theorem expectedRisk_eq_ofFun {A : Type}
    (oa : ProbComp A) (f : Risk A) :
    expectedRisk oa f = expectedRiskOfFun oa f := rfl

/-- A computation that deterministically returns `a` has expected value `g a`. -/
lemma expectedRiskOfFun_pure {A : Type} (a : A) (g : A → ℝ≥0∞) :
    expectedRiskOfFun (pure a : ProbComp A) g = g a := by
  unfold expectedRiskOfFun
  simp only [probFailure_pure, zero_add]
  rw [tsum_eq_single a]
  · simp
  · intro b hba
    simp [hba]

/-- A deterministic computation has exactly the risk assigned to its output. -/
lemma expectedRisk_pure {A : Type} (a : A) (f : Risk A) :
    expectedRisk (pure a : ProbComp A) f = f a :=
  expectedRiskOfFun_pure a f

/-- Sequential composition adds the first computation's missing mass to the
average continuation value. -/
lemma expectedRiskOfFun_bind {A B : Type} (oa : ProbComp A)
    (ob : A → ProbComp B) (g : B → ℝ≥0∞) :
    expectedRiskOfFun (oa >>= ob) g =
      Pr[⊥ | oa] + ∑' a, Pr[= a | oa] * expectedRiskOfFun (ob a) g := by
  unfold expectedRiskOfFun
  rw [probFailure_bind_eq_add_tsum]
  have hout :
      (∑' b, Pr[= b | oa >>= ob] * g b) =
        ∑' b, ∑' a, Pr[= a | oa] * Pr[= b | ob a] * g b := by
    refine tsum_congr fun b => ?_
    rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_right]
  calc
    (Pr[⊥ | oa] + ∑' a, Pr[= a | oa] * Pr[⊥ | ob a]) +
        ∑' b, Pr[= b | oa >>= ob] * g b =
        Pr[⊥ | oa] + ((∑' a, Pr[= a | oa] * Pr[⊥ | ob a]) +
          ∑' b, ∑' a, Pr[= a | oa] * Pr[= b | ob a] * g b) := by
      rw [hout]
      ac_rfl
    _ = Pr[⊥ | oa] + ((∑' a, Pr[= a | oa] * Pr[⊥ | ob a]) +
        ∑' a, ∑' b, Pr[= a | oa] * Pr[= b | ob a] * g b) := by
      rw [ENNReal.tsum_comm]
    _ = Pr[⊥ | oa] + ∑' a, Pr[= a | oa] *
        (Pr[⊥ | ob a] + ∑' b, Pr[= b | ob a] * g b) := by
      congr 1
      rw [← ENNReal.tsum_add]
      refine tsum_congr fun a => ?_
      rw [mul_add]
      simp_rw [mul_assoc]
      rw [ENNReal.tsum_mul_left]

/-- The expected risk of sequential composition is the first computation's
missing mass plus the average risk of continuing from its outputs. -/
lemma expectedRisk_bind {A B : Type} (oa : ProbComp A)
    (ob : A → ProbComp B) (f : Risk B) :
    expectedRisk (oa >>= ob) f =
      Pr[⊥ | oa] + ∑' a, Pr[= a | oa] * expectedRisk (ob a) f :=
  expectedRiskOfFun_bind oa ob f

/-- Applying `g` to each output before evaluating `h` is equivalent to
evaluating `h (g a)` on the original output. -/
lemma expectedRiskOfFun_map {A B : Type} (g : A → B) (oa : ProbComp A)
    (h : B → ℝ≥0∞) :
    expectedRiskOfFun (g <$> oa) h =
      expectedRiskOfFun oa (fun a => h (g a)) := by
  rw [map_eq_bind_pure_comp, expectedRiskOfFun_bind]
  simp only [Function.comp_apply, expectedRiskOfFun_pure]
  rfl

/-- Measuring risk after mapping outputs is equivalent to accounting for the
map in the risk function. -/
lemma expectedRisk_map {A B : Type} (g : A → B) (oa : ProbComp A)
    (f : Risk B) :
    expectedRisk (g <$> oa) f = expectedRisk oa (f.comp g) := by
  unfold expectedRisk
  rw [expectedRiskOfFun_map]
  rfl

/-- Increasing every returned-output value cannot decrease its failure-aware
expectation. -/
lemma expectedRiskOfFun_mono {A : Type} (oa : ProbComp A)
    (f g : A → ℝ≥0∞) (hfg : ∀ a, f a ≤ g a) :
    expectedRiskOfFun oa f ≤ expectedRiskOfFun oa g := by
  unfold expectedRiskOfFun
  exact add_le_add le_rfl
    (ENNReal.tsum_le_tsum fun a => mul_le_mul' le_rfl (hfg a))

/-- Increasing the risk assigned to every output cannot decrease expected
risk. -/
lemma expectedRisk_mono {A : Type} (oa : ProbComp A)
    (f g : Risk A) (hfg : ∀ a, f a ≤ g a) :
    expectedRisk oa f ≤ expectedRisk oa g :=
  expectedRiskOfFun_mono oa f g hfg

/-- If every returned-output value is at most `1`, so is its failure-aware
expectation. -/
lemma expectedRiskOfFun_le_one {A : Type} (oa : ProbComp A)
    (g : A → ℝ≥0∞) (hg : ∀ a, g a ≤ 1) :
    expectedRiskOfFun oa g ≤ 1 := by
  calc
    expectedRiskOfFun oa g ≤ expectedRiskOfFun oa (fun _ => 1) :=
      expectedRiskOfFun_mono oa g (fun _ => 1) hg
    _ = 1 := by simp [expectedRiskOfFun]

/-- Expected risk is at most `1`. -/
lemma expectedRisk_le_one {A : Type} (oa : ProbComp A) (f : Risk A) :
    expectedRisk oa f ≤ 1 :=
  expectedRiskOfFun_le_one oa f f.le_one

/-- If `oa` has no missing mass and every possible returned-output value is at
most `c`, then its failure-aware expectation is at most `c`. -/
lemma expectedRiskOfFun_le_const_of_support {A : Type} (oa : ProbComp A)
    (g : A → ℝ≥0∞) (c : ℝ≥0∞) (hnf : Pr[⊥ | oa] = 0)
    (hg : ∀ a ∈ support oa, g a ≤ c) :
    expectedRiskOfFun oa g ≤ c := by
  unfold expectedRiskOfFun
  rw [hnf, zero_add]
  calc
    (∑' a, Pr[= a | oa] * g a) ≤ ∑' a, Pr[= a | oa] * c := by
      refine ENNReal.tsum_le_tsum fun a => ?_
      by_cases ha : a ∈ support oa
      · exact mul_le_mul' le_rfl (hg a ha)
      · simp [(probOutput_eq_zero_iff _ _).2 ha]
    _ = (∑' a, Pr[= a | oa]) * c := ENNReal.tsum_mul_right
    _ ≤ 1 * c := mul_le_mul' tsum_probOutput_le_one le_rfl
    _ = c := one_mul c

/-- If `oa` has no missing mass and every possible output has risk at most
`c`, then its expected risk is at most `c`. -/
lemma expectedRisk_le_const_of_support {A : Type} (oa : ProbComp A)
    (f : Risk A) (c : ℝ≥0∞) (hnf : Pr[⊥ | oa] = 0)
    (hf : ∀ a ∈ support oa, f a ≤ c) :
    expectedRisk oa f ≤ c :=
  expectedRiskOfFun_le_const_of_support oa f c hnf hf

/-- Adding `c` to every returned-output value increases the failure-aware
expectation by at most `c`. -/
lemma expectedRiskOfFun_add_const_le {A : Type} (oa : ProbComp A)
    (f : A → ℝ≥0∞) (c : ℝ≥0∞) :
    expectedRiskOfFun oa (fun a => f a + c) ≤ expectedRiskOfFun oa f + c := by
  unfold expectedRiskOfFun
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

/-- Adding `c` to every returned-output risk increases the expectation by at
most `c`.  The shifted function need not itself be a `Risk`. -/
lemma expectedRisk_add_const_le {A : Type} (oa : ProbComp A)
    (f : Risk A) (c : ℝ≥0∞) :
    expectedRiskOfFun oa (fun a => f a + c) ≤ expectedRisk oa f + c :=
  expectedRiskOfFun_add_const_le oa f c

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
