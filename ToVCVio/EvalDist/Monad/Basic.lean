/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import VCVio.EvalDist.Monad.Basic
import VCVio.EvalDist.Bool
import VCVio.OracleComp.Constructions.SampleableType
import ToMathlib.MeasureTheory.Measure.Bool

/-!
# `EvalDist` point-probability transport

Generic point-probability (`Pr[= x | _]`) facts that hold for any monad with an
evaluation distribution.

* `probOutput_bind_of_const'` drops the missing-mass factor from
  `probOutput_bind_of_const` for a never-failing outer computation (`[NeverFail mx]`);
* `abs_probOutput_true_not_map_gap_eq` absorbs a final Boolean negation into the
  absolute two-branch gap (for never-failing computations);
* `probOutput_true_uniformBool_bind_not` relabels a uniform challenge-bit sample by negation,
  absorbing a `Bool` negation on the final comparison in the process — the "flip the challenge
  bit" step of hybrid arguments;
* `toReal_boolDist_evalDist` reads VCVio's `ℝ≥0∞` Boolean distance as the real absolute gap of
  `true`-output probabilities;
* `probOutput_uniformBool_branch_toReal_sub_half` writes the centred success probability of a
  uniform-bit branch game as half the gap between the branches;
* the four `probOutput_*_sample_*_param_eq` lemmas couple two or three eager
  `uniformSample` draws over `ProbComp`.
-/

open scoped ENNReal

namespace ToVCVio

universe u v

variable {α : Type u} {m : Type u → Type v} [Monad m]

/-- `probOutput_bind_of_const` for a never-failing outer computation: the missing-mass factor
`1 - Pr[⊥ | mx]` is always exactly `1`. -/
lemma probOutput_bind_of_const' [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadAttach m] [EvalDistCompatible m]
    {β : Type u} (mx : m α) [NeverFail mx] {my : α → m β}
    {y : β} {r : ℝ≥0∞} (h : ∀ x ∈ support mx, Pr[= y | my x] = r) :
    Pr[= y | mx >>= my] = r := by
  rw [probOutput_bind_of_const mx h, NeverFail.probFailure_eq_zero]
  simp

/-- A final `(! ·)` map turns `true`-output probability into `false`-output
probability, so the absolute two-branch gap is unchanged by negating both
branches. For never-failing computations this is where a `Bool`-orientation
reversal disappears. -/
lemma abs_probOutput_true_not_map_gap_eq {n : Type → Type*}
    [Monad n] [LawfulMonad n] [MonadLiftT n PMF] [LawfulMonadLiftT n PMF] (mx my : n Bool) :
    |(Pr[= true | (! ·) <$> mx]).toReal -
      (Pr[= true | (! ·) <$> my]).toReal| =
    |(Pr[= true | mx]).toReal - (Pr[= true | my]).toReal| := by
  simp [probOutput_false_eq_sub]
  ring_nf
  rw [show -Pr[= true | my].toReal + Pr[= true | mx].toReal =
      Pr[= true | mx].toReal - Pr[= true | my].toReal by ring]
  exact abs_sub_comm (Pr[= true | my].toReal) (Pr[= true | mx].toReal)

/-- Relabeling a uniform coin flip by negation, together with negating which side of the final
comparison is complemented, doesn't change the success probability:

Pr[b ← {0; 1}; b' ← f(b) | b == !b'] = Pr[b ← {0; 1}; b' ← f(!b) | b == b']

Feeding `f` the coin `b` and comparing against `!b'` is the same as feeding `f` the negated coin
`!b` and comparing directly against `b'`. This is the general fact underlying the "flip the
challenge bit" step of hybrid arguments.
-/
lemma probOutput_true_uniformBool_bind_not (f : Bool → ProbComp Bool) :
    Pr[= true | do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let b' ← f b
        pure (b == !b')] =
      Pr[= true | do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let b' ← f !b
        pure (b == b')] := by
  rw [probOutput_bind_uniformBool, probOutput_bind_uniformBool]
  have h1 : Pr[= true | f true >>= fun b' => (pure (true == !b') : ProbComp Bool)] =
      Pr[= false | f true] := by
    have heq : (f true >>= fun b' => (pure (true == !b') : ProbComp Bool)) = (!·) <$> f true := by
      rw [map_eq_bind_pure_comp]; congr 1; funext b'; cases b' <;> rfl
    rw [heq, probOutput_not_map]
  have h2 : Pr[= true | f false >>= fun b' => (pure (false == !b') : ProbComp Bool)] =
      Pr[= true | f false] := by
    have heq : (f false >>= fun b' => (pure (false == !b') : ProbComp Bool)) = f false := by
      conv_rhs => rw [← bind_pure (f false)]
      congr 1; funext b'; cases b' <;> rfl
    rw [heq]
  have h3 : Pr[= true | f (!true) >>= fun b' => (pure (true == b') : ProbComp Bool)] =
      Pr[= true | f false] := by
    have heq : (f (!true) >>= fun b' => (pure (true == b') : ProbComp Bool)) = f false := by
      conv_rhs => rw [← bind_pure (f false)]
      congr 1; funext b'; cases b' <;> rfl
    rw [heq]
  have h4 : Pr[= true | f (!false) >>= fun b' => (pure (false == b') : ProbComp Bool)] =
      Pr[= false | f true] := by
    have heq : (f (!false) >>= fun b' => (pure (false == b') : ProbComp Bool)) =
        (!·) <$> f true := by
      rw [map_eq_bind_pure_comp]; congr 1; funext b'; cases b' <;> rfl
    rw [heq, probOutput_not_map]
  rw [h1, h2, h3, h4, add_comm]

/-- Guessing a uniformly random bit after branching between `real` and `rand` decomposes into
the difference of the branch success probabilities. -/
-- Drop once the CKA/RKEM bounds move to `ℝ≥0∞` (v4.35 bump).
lemma probOutput_uniformBool_branch_toReal_sub_half (real rand : ProbComp Bool) :
    (Pr[= true | do
      let b ← ($ᵗ Bool)
      let z ← if b then real else rand
      pure (b == z)]).toReal - 1 / 2 =
    ((Pr[= true | real]).toReal - (Pr[= true | rand]).toReal) / 2 := by
  have hformula : Pr[= true | do
      let b ← ($ᵗ Bool)
      let z ← if b then real else rand
      pure (b == z)] = (Pr[= true | real] + Pr[= false | rand]) / 2 := by
    rw [probOutput_bind_uniformBool]
    simp
  have hfalseAsSub : Pr[= false | rand] = 1 - Pr[= true | rand] := by
    rw [← (by simp : Pr[= true | rand] + Pr[= false | rand] = 1),
      ENNReal.add_sub_cancel_left probOutput_ne_top]
  rw [hformula, ENNReal.toReal_div,
    ENNReal.toReal_add probOutput_ne_top probOutput_ne_top,
    hfalseAsSub, ENNReal.toReal_sub_of_le probOutput_le_one ENNReal.one_ne_top]
  simp only [ENNReal.toReal_one, ENNReal.toReal_ofNat]
  ring

/-- The real form of VCVio's Boolean distance between two `ProbComp Bool` games is the absolute
gap of their `true`-output probabilities. -/
lemma toReal_boolDist_evalDist (mx my : ProbComp Bool) :
    ((𝒟[mx]).boolDist 𝒟[my]).toReal =
      |(Pr[= true | mx]).toReal - (Pr[= true | my]).toReal| := by
  rw [MeasureTheory.Measure.toReal_boolDist, evalDist_apply_singleton, evalDist_apply_singleton]

/-- Active-parameter coupling for two independent samples.

Fix
* `lazy : A → B → A → ProbComp Y`,
* `base : A → ProbComp Y`,
* `y : Y`.

Assume, for every `x : A`,

`Pr[= y | base x]
 = Pr[= y | do b ← $ᵗ B; a ← $ᵗ A; lazy a b x]`,

and, for every `x b a`,

`Pr[= y | lazy a b x] = Pr[= y | lazy x b x]`.

Then

`Pr[= y | do b ← $ᵗ B; a ← $ᵗ A; lazy a b a]
 = Pr[= y | do x ← $ᵗ A; base x]`. -/
lemma probOutput_two_sample_active_param_eq
    {activeType passiveType outputType : Type 0}
    [SampleableType activeType] [SampleableType passiveType]
    (lazy : activeType → passiveType → activeType → ProbComp outputType)
    (base : activeType → ProbComp outputType) (y : outputType)
    (h_ih : ∀ x,
      Pr[= y | base x] = Pr[= y | do
        let passive ← ($ᵗ passiveType : ProbComp passiveType)
        let active ← ($ᵗ activeType : ProbComp activeType)
        lazy active passive x])
    (h_indep : ∀ x passive active,
      Pr[= y | lazy active passive x] = Pr[= y | lazy x passive x]) :
    Pr[= y | do
      let passive ← ($ᵗ passiveType : ProbComp passiveType)
      let active ← ($ᵗ activeType : ProbComp activeType)
      lazy active passive active] =
    Pr[= y | do
      let x ← ($ᵗ activeType : ProbComp activeType)
      base x] := by
  have eq_ih : Pr[= y | do
        let x ← ($ᵗ activeType : ProbComp activeType)
        base x] =
      Pr[= y | do
        let x ← ($ᵗ activeType : ProbComp activeType)
        let passive ← ($ᵗ passiveType : ProbComp passiveType)
        let active ← ($ᵗ activeType : ProbComp activeType)
        lazy active passive x] := by
    refine probOutput_bind_congr' _ y fun x => ?_
    exact h_ih x
  have eq_indep : Pr[= y | do
        let x ← ($ᵗ activeType : ProbComp activeType)
        let passive ← ($ᵗ passiveType : ProbComp passiveType)
        let active ← ($ᵗ activeType : ProbComp activeType)
        lazy active passive x] =
      Pr[= y | do
        let x ← ($ᵗ activeType : ProbComp activeType)
        let passive ← ($ᵗ passiveType : ProbComp passiveType)
        lazy x passive x] := by
    refine probOutput_bind_congr' _ y fun x => ?_
    refine probOutput_bind_congr' _ y fun passive => ?_
    exact probOutput_bind_of_const' _ fun active _ => h_indep x passive active
  have eq_swap : Pr[= y | do
        let x ← ($ᵗ activeType : ProbComp activeType)
        let passive ← ($ᵗ passiveType : ProbComp passiveType)
        lazy x passive x] =
      Pr[= y | do
        let passive ← ($ᵗ passiveType : ProbComp passiveType)
        let x ← ($ᵗ activeType : ProbComp activeType)
        lazy x passive x] :=
    probOutput_bind_bind_swap
      (mx := ($ᵗ activeType : ProbComp activeType))
      (my := ($ᵗ passiveType : ProbComp passiveType))
      (f := fun x passive => lazy x passive x) (z := y)
  rw [eq_ih, eq_indep, eq_swap]

/-- Second-parameter coupling for two independent samples.

Fix
* `lazy : A → B → B → ProbComp Y`,
* `base : B → ProbComp Y`,
* `y : Y`.

Assume, for every `x : B`,

`Pr[= y | base x]
 = Pr[= y | do second ← $ᵗ B; first ← $ᵗ A; lazy first second x]`,

and, for every `x first second`,

`Pr[= y | lazy first second x] = Pr[= y | lazy first x x]`.

Then

`Pr[= y | do second ← $ᵗ B; first ← $ᵗ A; lazy first second second]
 = Pr[= y | do x ← $ᵗ B; base x]`. -/
lemma probOutput_two_sample_second_param_eq
    {firstType secondType outputType : Type 0}
    [SampleableType firstType] [SampleableType secondType]
    (lazy : firstType → secondType → secondType → ProbComp outputType)
    (base : secondType → ProbComp outputType) (y : outputType)
    (h_ih : ∀ x,
      Pr[= y | base x] = Pr[= y | do
        let second ← ($ᵗ secondType : ProbComp secondType)
        let first ← ($ᵗ firstType : ProbComp firstType)
        lazy first second x])
    (h_indep : ∀ x first second,
      Pr[= y | lazy first second x] = Pr[= y | lazy first x x]) :
    Pr[= y | do
      let second ← ($ᵗ secondType : ProbComp secondType)
      let first ← ($ᵗ firstType : ProbComp firstType)
      lazy first second second] =
    Pr[= y | do
      let x ← ($ᵗ secondType : ProbComp secondType)
      base x] := by
  have eq_ih : Pr[= y | do
        let x ← ($ᵗ secondType : ProbComp secondType)
        base x] =
      Pr[= y | do
        let x ← ($ᵗ secondType : ProbComp secondType)
        let second ← ($ᵗ secondType : ProbComp secondType)
        let first ← ($ᵗ firstType : ProbComp firstType)
        lazy first second x] := by
    refine probOutput_bind_congr' _ y fun x => ?_
    exact h_ih x
  have eq_indep : Pr[= y | do
        let x ← ($ᵗ secondType : ProbComp secondType)
        let second ← ($ᵗ secondType : ProbComp secondType)
        let first ← ($ᵗ firstType : ProbComp firstType)
        lazy first second x] =
      Pr[= y | do
        let x ← ($ᵗ secondType : ProbComp secondType)
        let first ← ($ᵗ firstType : ProbComp firstType)
        lazy first x x] := by
    refine probOutput_bind_congr' _ y fun x => ?_
    rw [probOutput_bind_bind_swap
      (mx := ($ᵗ secondType : ProbComp secondType))
      (my := ($ᵗ firstType : ProbComp firstType))
      (f := fun second first => lazy first second x) (z := y)]
    refine probOutput_bind_congr' _ y fun first => ?_
    exact probOutput_bind_of_const' _ fun second _ => h_indep x first second
  have eq_swap : Pr[= y | do
        let x ← ($ᵗ secondType : ProbComp secondType)
        let first ← ($ᵗ firstType : ProbComp firstType)
        lazy first x x] =
      Pr[= y | do
        let second ← ($ᵗ secondType : ProbComp secondType)
        let first ← ($ᵗ firstType : ProbComp firstType)
        lazy first second second] := by
    rfl
  rw [eq_ih, eq_indep, eq_swap]

/-- Active-parameter coupling for three independent samples.

Fix
* `lazy : A → B → C → A → ProbComp Y`,
* `base : A → ProbComp Y`,
* `y : Y`.

Assume, for every `x : A`,

`Pr[= y | base x]
 = Pr[= y | do a ← $ᵗ A; b ← $ᵗ B; c ← $ᵗ C; lazy a b c x]`,

and, for every `x b a c`,

`Pr[= y | lazy a b c x] = Pr[= y | lazy x b c x]`.

Then

`Pr[= y | do a ← $ᵗ A; b ← $ᵗ B; c ← $ᵗ C; lazy a b c a]
 = Pr[= y | do x ← $ᵗ A; base x]`. -/
lemma probOutput_three_sample_active_param_eq
    {activeType paramType₁ paramType₂ outputType : Type 0}
    [SampleableType activeType] [SampleableType paramType₁] [SampleableType paramType₂]
    (lazy : activeType → paramType₁ → paramType₂ → activeType → ProbComp outputType)
    (base : activeType → ProbComp outputType) (y : outputType)
    (h_ih : ∀ x,
      Pr[= y | base x] = Pr[= y | do
        let active ← ($ᵗ activeType : ProbComp activeType)
        let param₁ ← ($ᵗ paramType₁ : ProbComp paramType₁)
        let param₂ ← ($ᵗ paramType₂ : ProbComp paramType₂)
        lazy active param₁ param₂ x])
    (h_indep : ∀ x param₁ active param₂,
      Pr[= y | lazy active param₁ param₂ x] =
      Pr[= y | lazy x param₁ param₂ x]) :
    Pr[= y | do
      let active ← ($ᵗ activeType : ProbComp activeType)
      let param₁ ← ($ᵗ paramType₁ : ProbComp paramType₁)
      let param₂ ← ($ᵗ paramType₂ : ProbComp paramType₂)
      lazy active param₁ param₂ active] =
    Pr[= y | do
      let x ← ($ᵗ activeType : ProbComp activeType)
      base x] := by
  have eq_ih : Pr[= y | do
        let x ← ($ᵗ activeType : ProbComp activeType)
        base x] =
      Pr[= y | do
        let x ← ($ᵗ activeType : ProbComp activeType)
        let active ← ($ᵗ activeType : ProbComp activeType)
        let param₁ ← ($ᵗ paramType₁ : ProbComp paramType₁)
        let param₂ ← ($ᵗ paramType₂ : ProbComp paramType₂)
        lazy active param₁ param₂ x] := by
    refine probOutput_bind_congr' _ y fun x => ?_
    exact h_ih x
  have eq_indep : Pr[= y | do
        let x ← ($ᵗ activeType : ProbComp activeType)
        let active ← ($ᵗ activeType : ProbComp activeType)
        let param₁ ← ($ᵗ paramType₁ : ProbComp paramType₁)
        let param₂ ← ($ᵗ paramType₂ : ProbComp paramType₂)
        lazy active param₁ param₂ x] =
      Pr[= y | do
        let x ← ($ᵗ activeType : ProbComp activeType)
        let param₁ ← ($ᵗ paramType₁ : ProbComp paramType₁)
        let param₂ ← ($ᵗ paramType₂ : ProbComp paramType₂)
        lazy x param₁ param₂ x] := by
    refine probOutput_bind_congr' _ y fun x => ?_
    refine probOutput_bind_of_const' _ fun active _ => ?_
    refine probOutput_bind_congr' _ y fun param₁ => ?_
    refine probOutput_bind_congr' _ y fun param₂ => ?_
    exact h_indep x param₁ active param₂
  have eq_swap : Pr[= y | do
        let x ← ($ᵗ activeType : ProbComp activeType)
        let param₁ ← ($ᵗ paramType₁ : ProbComp paramType₁)
        let param₂ ← ($ᵗ paramType₂ : ProbComp paramType₂)
        lazy x param₁ param₂ x] =
      Pr[= y | do
        let active ← ($ᵗ activeType : ProbComp activeType)
        let param₁ ← ($ᵗ paramType₁ : ProbComp paramType₁)
        let param₂ ← ($ᵗ paramType₂ : ProbComp paramType₂)
        lazy active param₁ param₂ active] := by
    rfl
  rw [eq_ih, eq_indep, eq_swap]

/-- Second-and-third-parameter coupling for three independent samples.

Fix
* `lazy : A → B → C → B → C → ProbComp Y`,
* `base : B → C → ProbComp Y`,
* `y : Y`.

Assume, for every `x : B` and `z : C`,

`Pr[= y | base x z]
 = Pr[= y | do first ← $ᵗ A; second ← $ᵗ B; third ← $ᵗ C;
   lazy first second third x z]`,

and, for every `x z first second third`,

`Pr[= y | lazy first second third x z]
 = Pr[= y | lazy first x third x z]`,

and, for every `x z first third`,

`Pr[= y | lazy first x third x z]
 = Pr[= y | lazy first x z x z]`.

Then

`Pr[= y | do first ← $ᵗ A; second ← $ᵗ B; third ← $ᵗ C;
   lazy first second third second third]
 = Pr[= y | do x ← $ᵗ B; z ← $ᵗ C; base x z]`. -/
lemma probOutput_three_sample_second_third_param_eq
    {firstType secondType thirdType outputType : Type 0}
    [SampleableType firstType] [SampleableType secondType] [SampleableType thirdType]
    (lazy : firstType → secondType → thirdType → secondType → thirdType →
      ProbComp outputType)
    (base : secondType → thirdType → ProbComp outputType) (y : outputType)
    (h_ih : ∀ x z,
      Pr[= y | base x z] = Pr[= y | do
        let first ← ($ᵗ firstType : ProbComp firstType)
        let second ← ($ᵗ secondType : ProbComp secondType)
        let third ← ($ᵗ thirdType : ProbComp thirdType)
        lazy first second third x z])
    (h_second_indep : ∀ x z first second third,
      Pr[= y | lazy first second third x z] = Pr[= y | lazy first x third x z])
    (h_third_indep : ∀ x z first third,
      Pr[= y | lazy first x third x z] = Pr[= y | lazy first x z x z]) :
    Pr[= y | do
      let first ← ($ᵗ firstType : ProbComp firstType)
      let second ← ($ᵗ secondType : ProbComp secondType)
      let third ← ($ᵗ thirdType : ProbComp thirdType)
      lazy first second third second third] =
    Pr[= y | do
      let x ← ($ᵗ secondType : ProbComp secondType)
      let z ← ($ᵗ thirdType : ProbComp thirdType)
      base x z] := by
  have eq_ih : Pr[= y | do
        let x ← ($ᵗ secondType : ProbComp secondType)
        let z ← ($ᵗ thirdType : ProbComp thirdType)
        base x z] =
      Pr[= y | do
        let x ← ($ᵗ secondType : ProbComp secondType)
        let z ← ($ᵗ thirdType : ProbComp thirdType)
        let first ← ($ᵗ firstType : ProbComp firstType)
        let second ← ($ᵗ secondType : ProbComp secondType)
        let third ← ($ᵗ thirdType : ProbComp thirdType)
        lazy first second third x z] := by
    refine probOutput_bind_congr' _ y fun x => ?_
    refine probOutput_bind_congr' _ y fun z => ?_
    exact h_ih x z
  have eq_second : Pr[= y | do
        let x ← ($ᵗ secondType : ProbComp secondType)
        let z ← ($ᵗ thirdType : ProbComp thirdType)
        let first ← ($ᵗ firstType : ProbComp firstType)
        let second ← ($ᵗ secondType : ProbComp secondType)
        let third ← ($ᵗ thirdType : ProbComp thirdType)
        lazy first second third x z] =
      Pr[= y | do
        let x ← ($ᵗ secondType : ProbComp secondType)
        let z ← ($ᵗ thirdType : ProbComp thirdType)
        let first ← ($ᵗ firstType : ProbComp firstType)
        let third ← ($ᵗ thirdType : ProbComp thirdType)
        lazy first x third x z] := by
    refine probOutput_bind_congr' _ y fun x => ?_
    refine probOutput_bind_congr' _ y fun z => ?_
    refine probOutput_bind_congr' _ y fun first => ?_
    refine probOutput_bind_of_const' _ fun second _ => ?_
    refine probOutput_bind_congr' _ y fun third => ?_
    exact h_second_indep x z first second third
  have eq_third : Pr[= y | do
        let x ← ($ᵗ secondType : ProbComp secondType)
        let z ← ($ᵗ thirdType : ProbComp thirdType)
        let first ← ($ᵗ firstType : ProbComp firstType)
        let third ← ($ᵗ thirdType : ProbComp thirdType)
        lazy first x third x z] =
      Pr[= y | do
        let x ← ($ᵗ secondType : ProbComp secondType)
        let z ← ($ᵗ thirdType : ProbComp thirdType)
        let first ← ($ᵗ firstType : ProbComp firstType)
        lazy first x z x z] := by
    refine probOutput_bind_congr' _ y fun x => ?_
    refine probOutput_bind_congr' _ y fun z => ?_
    refine probOutput_bind_congr' _ y fun first => ?_
    exact probOutput_bind_of_const' _ fun third _ => h_third_indep x z first third
  have eq_swap_z_first : Pr[= y | do
        let x ← ($ᵗ secondType : ProbComp secondType)
        let z ← ($ᵗ thirdType : ProbComp thirdType)
        let first ← ($ᵗ firstType : ProbComp firstType)
        lazy first x z x z] =
      Pr[= y | do
        let x ← ($ᵗ secondType : ProbComp secondType)
        let first ← ($ᵗ firstType : ProbComp firstType)
        let z ← ($ᵗ thirdType : ProbComp thirdType)
        lazy first x z x z] := by
    refine probOutput_bind_congr' _ y fun x => ?_
    exact probOutput_bind_bind_swap
      (mx := ($ᵗ thirdType : ProbComp thirdType))
      (my := ($ᵗ firstType : ProbComp firstType))
      (f := fun z first => lazy first x z x z) (z := y)
  have eq_swap_x_first : Pr[= y | do
        let x ← ($ᵗ secondType : ProbComp secondType)
        let first ← ($ᵗ firstType : ProbComp firstType)
        let z ← ($ᵗ thirdType : ProbComp thirdType)
        lazy first x z x z] =
      Pr[= y | do
        let first ← ($ᵗ firstType : ProbComp firstType)
        let second ← ($ᵗ secondType : ProbComp secondType)
        let third ← ($ᵗ thirdType : ProbComp thirdType)
        lazy first second third second third] :=
    probOutput_bind_bind_swap
      (mx := ($ᵗ secondType : ProbComp secondType))
      (my := ($ᵗ firstType : ProbComp firstType))
      (f := fun x first => do
        let z ← ($ᵗ thirdType : ProbComp thirdType)
        lazy first x z x z) (z := y)
  rw [eq_ih, eq_second, eq_third, eq_swap_z_first, eq_swap_x_first]

end ToVCVio
