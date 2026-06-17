import VCVio.EvalDist.Monad.Basic
import VCVio.EvalDist.Bool
import VCVio.OracleComp.Constructions.SampleableType

/-!
# `EvalDist` point-probability transport

Generic point-probability (`Pr[= x | _]`) facts that hold for any monad with an
evaluation distribution.

* `probOutput_eq_of_evalDist_eq` transports a point probability across an
  equality of evaluation distributions `𝒟[_]`;
* `probOutput_true_bind_add_of_pointwise` splits the `true`-output probability
  of a `bind` whose continuation splits pointwise;
* `abs_probOutput_true_not_map_gap_eq` absorbs a final Boolean negation into the
  absolute two-branch gap (for never-failing computations);
* the `evalDist_sample_bind*` and `probOutput_*sample*` lemmas collapse or couple
  one, two, or three eager `uniformSample` draws over `ProbComp`.
-/

universe u v

variable {α : Type u} {m : Type u → Type v} [Monad m]

/-- If `𝒟[mx] = 𝒟[my]` then `Pr[= x | mx] = Pr[= x | my]`: point-probability
congruence under equality of evaluation distributions. -/
lemma probOutput_eq_of_evalDist_eq [HasEvalSPMF m] {mx my : m α}
    (h : 𝒟[mx] = 𝒟[my]) (x : α) :
    Pr[= x | mx] = Pr[= x | my] := by
  simpa [probOutput] using congrFun (congrArg DFunLike.coe h) x

/-- Splitting a `bind`'s continuation pointwise splits the `true`-output
probability of the whole computation: if `Pr[= true | f z]` decomposes as
`Pr[= true | g z] + Pr[= true | h z]` for every `z`, the same decomposition
holds after binding each continuation against a shared `mx`. -/
lemma probOutput_true_bind_add_of_pointwise {β : Type} {n : Type → Type*}
    [Monad n] [HasEvalSPMF n] (mx : n β) (f g h : β → n Bool)
    (hpt : ∀ z, Pr[= true | f z] = Pr[= true | g z] + Pr[= true | h z]) :
    Pr[= true | mx >>= f] = Pr[= true | mx >>= g] + Pr[= true | mx >>= h] := by
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum, probOutput_bind_eq_tsum,
    ← ENNReal.tsum_add]
  exact tsum_congr fun z => by rw [hpt z, mul_add]

/-- A final `(! ·)` map turns `true`-output probability into `false`-output
probability, so the absolute two-branch gap is unchanged by negating both
branches. For never-failing computations this is where a `Bool`-orientation
reversal disappears. -/
lemma abs_probOutput_true_not_map_gap_eq {n : Type → Type*}
    [Monad n] [LawfulMonad n] [HasEvalPMF n] (mx my : n Bool) :
    |(Pr[= true | (! ·) <$> mx]).toReal -
      (Pr[= true | (! ·) <$> my]).toReal| =
    |(Pr[= true | mx]).toReal - (Pr[= true | my]).toReal| := by
  simp [probOutput_false_eq_sub]
  ring_nf
  rw [show -Pr[= true | my].toReal + Pr[= true | mx].toReal =
      Pr[= true | mx].toReal - Pr[= true | my].toReal by ring]
  exact abs_sub_comm (Pr[= true | my].toReal) (Pr[= true | mx].toReal)

/-- Pointwise distribution equality implies congruence under one eager uniform
sample:

`If ∀ a, 𝒟[f a] = 𝒟[g a] then
  𝒟[a ←$ α; f a] = 𝒟[a ←$ α; g a]`.

This packages the outer-sample congruence used after proving a distributional
equality for each fixed sampled value. -/
lemma evalDist_sample_bind_congr_of_forall_evalDist_eq {sampleType outputType : Type 0}
    [SampleableType sampleType] (f g : sampleType → ProbComp outputType)
    (h : ∀ a, evalDist (f a) = evalDist (g a)) :
    evalDist (do
      let a ← uniformSample sampleType
      f a) = evalDist (do
      let a ← uniformSample sampleType
      g a) := by
  apply evalDist_ext
  intro y
  refine probOutput_bind_congr' _ y fun a => ?_
  exact probOutput_eq_of_evalDist_eq (h a) y

/-- Collapse one eager uniform sample when the sampled value is pointwise unused.

`If ∀ a, f a = p then 𝒟[a ←$ α; f a] = 𝒟[p]`. -/
lemma evalDist_sample_bind_eq_of_forall_eq {sampleType outputType : Type 0}
    [SampleableType sampleType] (f : sampleType → ProbComp outputType)
    (p : ProbComp outputType) (h : ∀ a, f a = p) :
    evalDist (do
      let a ← uniformSample sampleType
      f a) = evalDist p := by
  apply evalDist_ext
  intro y
  have h_bind : (do
      let a ← uniformSample sampleType
      f a) = (do
      let _a ← uniformSample sampleType
      p) := by
    congr 1
    funext a
    exact h a
  rw [h_bind, probOutput_bind_const]
  simp

/-- Collapse two eager uniform samples when both sampled values are pointwise
unused.

`If ∀ a b, f a b = p then 𝒟[a ←$ α; b ←$ β; f a b] = 𝒟[p]`. -/
lemma evalDist_sample_bind₂_eq_of_forall_eq {sampleType₁ sampleType₂ outputType : Type 0}
    [SampleableType sampleType₁] [SampleableType sampleType₂]
    (f : sampleType₁ → sampleType₂ → ProbComp outputType) (p : ProbComp outputType)
    (h : ∀ a b, f a b = p) :
    evalDist (do
      let a ← uniformSample sampleType₁
      let b ← uniformSample sampleType₂
      f a b) = evalDist p := by
  apply evalDist_ext
  intro y
  have h_bind : (do
      let a ← uniformSample sampleType₁
      let b ← uniformSample sampleType₂
      f a b) = (do
      let _a ← uniformSample sampleType₁
      let _b ← uniformSample sampleType₂
      p) := by
    congr 1
    funext a
    congr 1
    funext b
    exact h a b
  rw [h_bind, probOutput_bind_const, probOutput_bind_const]
  simp

/-- Collapse three eager uniform samples when all sampled values are pointwise
unused.

`If ∀ a b c, f a b c = p then
  𝒟[a ←$ α; b ←$ β; c ←$ γ; f a b c] = 𝒟[p]`. -/
lemma evalDist_sample_bind₃_eq_of_forall_eq
    {sampleType₁ sampleType₂ sampleType₃ outputType : Type 0}
    [SampleableType sampleType₁] [SampleableType sampleType₂] [SampleableType sampleType₃]
    (f : sampleType₁ → sampleType₂ → sampleType₃ → ProbComp outputType)
    (p : ProbComp outputType) (h : ∀ a b c, f a b c = p) :
    evalDist (do
      let a ← uniformSample sampleType₁
      let b ← uniformSample sampleType₂
      let c ← uniformSample sampleType₃
      f a b c) = evalDist p := by
  apply evalDist_ext
  intro y
  have h_bind : (do
      let a ← uniformSample sampleType₁
      let b ← uniformSample sampleType₂
      let c ← uniformSample sampleType₃
      f a b c) = (do
      let _a ← uniformSample sampleType₁
      let _b ← uniformSample sampleType₂
      let _c ← uniformSample sampleType₃
      p) := by
    congr 1
    funext a
    congr 1
    funext b
    congr 1
    funext c
    exact h a b c
  rw [h_bind, probOutput_bind_const, probOutput_bind_const, probOutput_bind_const]
  simp

/-- Collapse one eager uniform sample at the output-probability level. -/
lemma probOutput_sample_bind_eq_of_forall_eq {sampleType outputType : Type 0}
    [SampleableType sampleType] (f : sampleType → ProbComp outputType)
    (p : ProbComp outputType) (y : outputType)
    (h : ∀ a, Pr[= y | f a] = Pr[= y | p]) :
    Pr[= y | do
      let a ← uniformSample sampleType
      f a] = Pr[= y | p] := by
  rw [probOutput_bind_of_const (uniformSample sampleType)
    (my := f) (r := Pr[= y | p]) (h := fun a _ => h a)]
  simp

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
    exact probOutput_sample_bind_eq_of_forall_eq
      (f := fun active => lazy active passive x)
      (p := lazy x passive x) y
      (fun active => h_indep x passive active)
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
    exact probOutput_sample_bind_eq_of_forall_eq
      (f := fun second => lazy first second x)
      (p := lazy first x x) y
      (fun second => h_indep x first second)
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
    exact probOutput_sample_bind_eq_of_forall_eq
      (f := fun active => do
        let param₁ ← ($ᵗ paramType₁ : ProbComp paramType₁)
        let param₂ ← ($ᵗ paramType₂ : ProbComp paramType₂)
        lazy active param₁ param₂ x)
      (p := do
        let param₁ ← ($ᵗ paramType₁ : ProbComp paramType₁)
        let param₂ ← ($ᵗ paramType₂ : ProbComp paramType₂)
        lazy x param₁ param₂ x) y
      (fun active => by
        refine probOutput_bind_congr' _ y fun param₁ => ?_
        refine probOutput_bind_congr' _ y fun param₂ => ?_
        exact h_indep x param₁ active param₂)
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
    exact probOutput_sample_bind_eq_of_forall_eq
      (f := fun second => do
        let third ← ($ᵗ thirdType : ProbComp thirdType)
        lazy first second third x z)
      (p := do
        let third ← ($ᵗ thirdType : ProbComp thirdType)
        lazy first x third x z) y
      (fun second => by
        refine probOutput_bind_congr' _ y fun third => ?_
        exact h_second_indep x z first second third)
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
    exact probOutput_sample_bind_eq_of_forall_eq
      (f := fun third => lazy first x third x z)
      (p := lazy first x z x z) y
      (fun third => h_third_indep x z first third)
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

/-- Collapse one eager uniform sample when every sampled computation has the
same evaluation distribution.

If `evalDist (f a) = evalDist p` for every sampled value `a`, then sampling
`a ← $ᵗ sampleType` and running `f a` has evaluation distribution `evalDist p`. -/
lemma evalDist_sample_bind_eq_of_forall_evalDist_eq {sampleType outputType : Type 0}
    [SampleableType sampleType] (f : sampleType → ProbComp outputType)
    (p : ProbComp outputType) (h : ∀ a, evalDist (f a) = evalDist p) :
    evalDist (do
      let a ← uniformSample sampleType
      f a) = evalDist p := by
  apply evalDist_ext
  intro y
  exact probOutput_sample_bind_eq_of_forall_eq f p y
    (fun a => probOutput_eq_of_evalDist_eq (h a) y)
