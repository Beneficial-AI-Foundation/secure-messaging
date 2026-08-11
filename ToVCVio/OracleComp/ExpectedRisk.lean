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

The failure probability `Pr[oa = ⊥]` is assigned a risk value `1`.  Given `f ≤ 1`,
this value is a least upper bound of the range of `f`, and corresponds to
treating failure of `oa` as certain failure of the event bounded by `f`.

The same formula on an arbitrary integrand `g : A → ℝ≥0∞` (not necessarily
bounded by `1`) is `expectedRiskOfFun oa g`.  It appears as an intermediate
quantity; the risk interpretation applies only when the integrand is a
`Risk`.

## Interpretation

If `f(x)` bounds the probability of eventual failure from a state `x`
produced by one step `oa`, then `E_{x ← oa}[f(x)]` accounts for:

* failure of the step (`oa` returns `⊥`, charged `1`); and
* continuation risk `f(x)` when the step returns `x`.

If a step from state `s` satisfies `E_{x ← oa}[f(x)] ≤ f(s) + ε`, then the
expected risk increases by at most `ε`.  Iterating over `q` such steps yields
`f(s₀) + q · ε` (and `q · ε` when `f(s₀) = 0`).

## Laws

Relative to the monad structure of `ProbComp`
(`pure`, bind `>>=`, map `<$>`):

* `expectedRisk_pure` —
  `E_{x ← pure a}[f(x)] = f(a)`;
* `expectedRisk_bind` —
  `E_{y ← oa >>= ob}[f(y)] =
     Pr[oa = ⊥] + Σ_x Pr[oa = x] · E_{y ← ob x}[f(y)]`;
* `expectedRisk_map` —
  `E_{y ← g <$> oa}[f(y)] = E_{x ← oa}[(f ∘ g)(x)]`;
* `expectedRisk_mono` —
  `f ≤ g` pointwise implies `E_{x ← oa}[f(x)] ≤ E_{x ← oa}[g(x)]`;
* `expectedRisk_le_one` —
  `E_{x ← oa}[f(x)] ≤ 1`;
* `expectedRisk_le_const_of_support` —
  `Pr[oa = ⊥] = 0` and `f ≤ c` on `support oa` imply `E_{x ← oa}[f(x)] ≤ c`;
* `expectedRisk_add_const_le` —
  `expectedRiskOfFun oa (fun x ↦ f(x) + c) ≤ expectedRisk oa f + c`.

For `oc : ProbComp Bool`, write
`m(oc) := Pr[oc = false] + Pr[oc = ⊥]` for the false-or-failure mass.
Then `m(oc) = expectedRiskOfFun oc (fun b ↦ if b then 0 else 1)`, and the
integrand is a risk.  For `oa : ProbComp A` and `ob : A → ProbComp Bool`:

* `probOutput_false_add_probFailure_bind` —
  `m(oa >>= ob) = Pr[oa = ⊥] + Σ_x Pr[oa = x] · m(ob x)`;
* `probOutput_false_add_probFailure_le_one` —
  `m(oc) ≤ 1`.
-/

open OracleSpec ENNReal

namespace OracleComp

/-- A risk on `A`: a function `A → ℝ≥0∞` bounded above by `1`, intended as a
pointwise failure-probability bound. -/
structure Risk (A : Type) where
  /-- Underlying function. -/
  toFun : A → ℝ≥0∞
  /-- Pointwise bound `toFun a ≤ 1`. -/
  le_one : ∀ a, toFun a ≤ 1

namespace Risk

instance {A : Type} : CoeFun (Risk A) (fun _ => A → ℝ≥0∞) where
  coe := Risk.toFun

/-- Precomposition: `(f.comp g) a = f (g a)`. -/
def comp {A B : Type} (f : Risk B) (g : A → B) : Risk A where
  toFun := fun a => f.toFun (g a)
  le_one := fun a => f.le_one (g a)

/-- The constant risk with value `c`, given `c ≤ 1`. -/
def const {A : Type} (c : ℝ≥0∞) (hc : c ≤ 1) : Risk A where
  toFun := fun _ => c
  le_one := fun _ => hc

end Risk

/-- Unrestricted failure-aware expectation of an integrand `g : A → ℝ≥0∞`:
`Pr[⊥ | oa] + Σ' a, Pr[= a | oa] · g a`, charging failure value `1`.
Prefer `expectedRisk` when `g` is a `Risk`. -/
noncomputable def expectedRiskOfFun {A : Type}
    (oa : ProbComp A) (g : A → ℝ≥0∞) : ℝ≥0∞ :=
  Pr[⊥ | oa] + ∑' a, Pr[= a | oa] * g a

/-- Failure-aware expected risk of `f` under `oa`.
Equals `expectedRiskOfFun oa f`; the `Risk` argument records `f ≤ 1`. -/
noncomputable def expectedRisk {A : Type}
    (oa : ProbComp A) (f : Risk A) : ℝ≥0∞ :=
  expectedRiskOfFun oa f

theorem expectedRisk_eq_ofFun {A : Type}
    (oa : ProbComp A) (f : Risk A) :
    expectedRisk oa f = expectedRiskOfFun oa f := rfl

/-- `expectedRiskOfFun (pure a) g = g a`. -/
lemma expectedRiskOfFun_pure {A : Type} (a : A) (g : A → ℝ≥0∞) :
    expectedRiskOfFun (pure a : ProbComp A) g = g a := by
  unfold expectedRiskOfFun
  simp only [probFailure_pure, zero_add]
  rw [tsum_eq_single a]
  · simp
  · intro b hba
    simp [hba]

/-- `expectedRisk (pure a) f = f a`. -/
lemma expectedRisk_pure {A : Type} (a : A) (f : Risk A) :
    expectedRisk (pure a : ProbComp A) f = f a :=
  expectedRiskOfFun_pure a f

/-- `expectedRiskOfFun (oa >>= ob) g =
Pr[⊥ | oa] + Σ' a, Pr[= a | oa] · expectedRiskOfFun (ob a) g`. -/
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

/-- `expectedRisk (oa >>= ob) f =
Pr[⊥ | oa] + Σ' a, Pr[= a | oa] · expectedRisk (ob a) f`. -/
lemma expectedRisk_bind {A B : Type} (oa : ProbComp A)
    (ob : A → ProbComp B) (f : Risk B) :
    expectedRisk (oa >>= ob) f =
      Pr[⊥ | oa] + ∑' a, Pr[= a | oa] * expectedRisk (ob a) f :=
  expectedRiskOfFun_bind oa ob f

/-- `expectedRiskOfFun (g <$> oa) h = expectedRiskOfFun oa (h ∘ g)`. -/
lemma expectedRiskOfFun_map {A B : Type} (g : A → B) (oa : ProbComp A)
    (h : B → ℝ≥0∞) :
    expectedRiskOfFun (g <$> oa) h =
      expectedRiskOfFun oa (fun a => h (g a)) := by
  rw [map_eq_bind_pure_comp, expectedRiskOfFun_bind]
  simp only [Function.comp_apply, expectedRiskOfFun_pure]
  rfl

/-- `expectedRisk (g <$> oa) f = expectedRisk oa (f.comp g)`. -/
lemma expectedRisk_map {A B : Type} (g : A → B) (oa : ProbComp A)
    (f : Risk B) :
    expectedRisk (g <$> oa) f = expectedRisk oa (f.comp g) := by
  unfold expectedRisk
  rw [expectedRiskOfFun_map]
  rfl

/-- Monotonicity for unrestricted integrands. -/
lemma expectedRiskOfFun_mono {A : Type} (oa : ProbComp A)
    (f g : A → ℝ≥0∞) (hfg : ∀ a, f a ≤ g a) :
    expectedRiskOfFun oa f ≤ expectedRiskOfFun oa g := by
  unfold expectedRiskOfFun
  exact add_le_add le_rfl
    (ENNReal.tsum_le_tsum fun a => mul_le_mul' le_rfl (hfg a))

/-- Monotonicity: `f ≤ g` pointwise implies
`expectedRisk oa f ≤ expectedRisk oa g`. -/
lemma expectedRisk_mono {A : Type} (oa : ProbComp A)
    (f g : Risk A) (hfg : ∀ a, f a ≤ g a) :
    expectedRisk oa f ≤ expectedRisk oa g :=
  expectedRiskOfFun_mono oa f g hfg

/-- If `g ≤ 1` pointwise, then `expectedRiskOfFun oa g ≤ 1`. -/
lemma expectedRiskOfFun_le_one {A : Type} (oa : ProbComp A)
    (g : A → ℝ≥0∞) (hg : ∀ a, g a ≤ 1) :
    expectedRiskOfFun oa g ≤ 1 := by
  calc
    expectedRiskOfFun oa g ≤ expectedRiskOfFun oa (fun _ => 1) :=
      expectedRiskOfFun_mono oa g (fun _ => 1) hg
    _ = 1 := by simp [expectedRiskOfFun]

/-- `expectedRisk oa f ≤ 1`. -/
lemma expectedRisk_le_one {A : Type} (oa : ProbComp A) (f : Risk A) :
    expectedRisk oa f ≤ 1 :=
  expectedRiskOfFun_le_one oa f f.le_one

/-- If `Pr[⊥ | oa] = 0` and `g ≤ c` on `support oa`, then
`expectedRiskOfFun oa g ≤ c`. -/
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

/-- If `Pr[⊥ | oa] = 0` and `f ≤ c` on `support oa`, then
`expectedRisk oa f ≤ c`. -/
lemma expectedRisk_le_const_of_support {A : Type} (oa : ProbComp A)
    (f : Risk A) (c : ℝ≥0∞) (hnf : Pr[⊥ | oa] = 0)
    (hf : ∀ a ∈ support oa, f a ≤ c) :
    expectedRisk oa f ≤ c :=
  expectedRiskOfFun_le_const_of_support oa f c hnf hf

/-- `expectedRiskOfFun oa (fun a ↦ f a + c) ≤ expectedRiskOfFun oa f + c`. -/
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

/-- Adding a constant to the integrand increases the failure-aware expectation
by at most that constant.  The left-hand side uses `expectedRiskOfFun` because
`fun a ↦ f a + c` need not be a `Risk`. -/
lemma expectedRisk_add_const_le {A : Type} (oa : ProbComp A)
    (f : Risk A) (c : ℝ≥0∞) :
    expectedRiskOfFun oa (fun a => f a + c) ≤ expectedRisk oa f + c :=
  expectedRiskOfFun_add_const_le oa f c

/-- False-or-failure mass after bind:
`m(oa >>= ob) = Pr[⊥ | oa] + Σ' a, Pr[= a | oa] · m(ob a)`. -/
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

/-- `Pr[= false | oa] + Pr[⊥ | oa] ≤ 1`. -/
lemma probOutput_false_add_probFailure_le_one (oa : ProbComp Bool) :
    Pr[= false | oa] + Pr[⊥ | oa] ≤ 1 := by
  calc
    Pr[= false | oa] + Pr[⊥ | oa] ≤
        (∑' b : Bool, Pr[= b | oa]) + Pr[⊥ | oa] := by
      exact add_le_add (ENNReal.le_tsum false) le_rfl
    _ = 1 := tsum_probOutput_add_probFailure oa

end OracleComp
