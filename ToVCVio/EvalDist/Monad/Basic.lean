/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import VCVio.EvalDist.Monad.Basic
import VCVio.EvalDist.Monad.Map
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# `EvalDist` point-probability transport

Generic point-probability (`Pr{let y ← _}[y = x]`) facts that hold for any monad with an
evaluation distribution.

* `abs_prEvent_true_not_map_gap_eq` absorbs a final Boolean negation into the
  absolute two-branch gap (for lossless computations);
* `prEvent_true_uniformBool_bind_not` relabels a uniform challenge-bit sample by negation,
  absorbing a `Bool` negation on the final comparison in the process — the "flip the challenge
  bit" step of hybrid arguments;
* `prEvent_uniformBool_branch_toReal_sub_half` writes hidden-bit guessing over a uniform bit,
  centered at `1/2`, as half the signed gap between its two branches;
* `tsum_ite_prEvent_eq_le_prEvent` and `tsum_prEvent_eq_le_one` bound sums of point masses
  in any monad;
* `tsum_prEvent_mul_le_of_forall_mem_support` bounds the expectation
  `∑' z, Pr{let x ← mx}[x = z] * F z` by any bound on `F` over the support of `mx`;
* `prEvent_bind_eq_of_forall_eq_of_support` keeps a continuation probability that is the same
  for every possible output of a lossless draw;
* the four `prEvent_*_sample_*_param_eq` lemmas couple two or three eager
  `uniformSample` draws over `ProbComp`.
-/

open scoped ENNReal

namespace ToVCVio

universe v

variable {α : Type} {m : Type → Type v} [Monad m] [LawfulMonad m]

/-- If `my x = mz` for every `x` in the support of a never-failing `mx`, then `mx >>= my`
has the distribution of `mz`. -/
lemma evalDist_bind_of_const' [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [EvalDistCompatible m]
    {β : Type u} (mx : m α) [NeverFail mx] {my : α → m β} {mz : m β}
    (h : ∀ x ∈ support mx, my x = mz) : evalDist (mx >>= my) = evalDist mz :=
  evalDist_ext fun y => probOutput_bind_of_const' mx fun x hx => by rw [h x hx]

/-- A final `(! ·)` map turns `true`-output probability into `false`-output
probability, so the absolute two-branch gap is unchanged by negating both
branches. For lossless computations this is where a `Bool`-orientation
reversal disappears. -/
lemma abs_prEvent_true_not_map_gap_eq {n : Type → Type*}
    [Monad n] [LawfulMonad n] [EvalDistSemantics n] [LawfulEvalDistSemantics n] (mx my : n Bool)
    (hmx : Pr{let _ ← mx}[True] = 1 := by simp) (hmy : Pr{let _ ← my}[True] = 1 := by simp) :
    |(Pr{let x ← (! ·) <$> mx}[x = true]).toReal -
      (Pr{let x ← (! ·) <$> my}[x = true]).toReal| =
    |(Pr{let x ← mx}[x = true]).toReal - (Pr{let x ← my}[x = true]).toReal| := by
  have hnot (mz : n Bool) (hmz : Pr{let _ ← mz}[True] = 1) :
      Pr{let x ← (! ·) <$> mz}[x = true] = 1 - Pr{let x ← mz}[x = true] := by
    rw [prEvent_map, ← hmz, ← prEvent_add_prEvent_not_eq_prEvent_true mz (· = true),
      ENNReal.add_sub_cancel_left (prEvent_ne_top _)]
    exact prEvent_congr mz _ _ fun b => by cases b <;> simp
  rw [hnot mx hmx, hnot my hmy, ENNReal.toReal_sub_of_le (prEvent_le_one _) ENNReal.one_ne_top,
    ENNReal.toReal_sub_of_le (prEvent_le_one _) ENNReal.one_ne_top, abs_sub_comm]
  congr 1
  ring

/-- Relabeling a uniform coin flip by negation, together with negating which side of the final
comparison is complemented, doesn't change the success probability:

Pr[b ← {0; 1}; b' ← f(b) | b == !b'] = Pr[b ← {0; 1}; b' ← f(!b) | b == b']

Feeding `f` the coin `b` and comparing against `!b'` is the same as feeding `f` the negated coin
`!b` and comparing directly against `b'`. This is the general fact underlying the "flip the
challenge bit" step of hybrid arguments.
-/
lemma prEvent_true_uniformBool_bind_not (f : Bool → ProbComp Bool) :
    Pr{let x ← (do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let b' ← f b
        pure (b == !b'))}[x = true] =
      Pr{let x ← (do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let b' ← f !b
        pure (b == b'))}[x = true] := by
  let g : Bool → ProbComp Bool := fun c => do
    let b' ← f c
    pure (!c == b')
  have hL : (do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let b' ← f b
        pure (b == !b')) = (do
        let b ← ($ᵗ Bool : ProbComp Bool)
        g b) := by
    congr 1; funext b; congr 1; funext b'; cases b <;> cases b' <;> rfl
  have hR : (do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let b' ← f !b
        pure (b == b')) = (do
        let b ← ($ᵗ Bool : ProbComp Bool)
        g (!b)) := by
    congr 1; funext b; congr 1; funext b'; cases b <;> cases b' <;> rfl
  rw [hL, hR, prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton,
    ProbComp.evalDist_bind_not_uniformBool]

/-- Hidden-bit guessing over a uniform bit, centered at `1/2`, is half the signed difference of
its two branches: `Pr[b ←$ {0,1}; z ← (if b then real else rand); output (b = z)] - 1/2 =
  (Pr[real = 1] - Pr[rand = 1]) / 2`. -/
lemma prEvent_uniformBool_branch_toReal_sub_half (real rand : ProbComp Bool) :
    (Pr{let x ← (do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let z ← if b then real else rand
      pure (b == z))}[x = true]).toReal - 1 / 2 =
    ((Pr{let x ← real}[x = true]).toReal - (Pr{let x ← rand}[x = true]).toReal) / 2 := by
  rw [prEvent_bind_eq_lintegral_of_discrete, MeasureTheory.lintegral_fintype, Fintype.sum_bool]
  simp only [SampleableType.evalDist_uniformSample_singleton, ite_true, Bool.false_eq_true,
    ite_false, Fintype.card_bool, bind_pure_comp, prEvent_map, Bool.true_beq, bind_pure]
  have hf : Pr{let z ← rand}[(false == z) = true] = 1 - Pr{let z ← rand}[z = true] := by
    simpa only [Bool.false_beq, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_true] using
      OracleComp.prEvent_not_eq_one_sub rand (fun z => z = true)
  have hle : Pr{let z ← rand}[z = true] ≤ 1 := prEvent_le_one _
  rw [hf, ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top]
  simp only [Nat.cast_ofNat, ENNReal.toReal_inv, ENNReal.toReal_ofNat, ENNReal.toReal_one,
    one_div]
  ring

/-- The point masses of the outputs of `mx` satisfying `p` sum to at most the probability of
`p`. -/
lemma tsum_ite_prEvent_eq_le_prEvent [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    (mx : m α) (p : α → Prop) [DecidablePred p] :
    ∑' a, (if p a then Pr{let x ← mx}[x = a] else 0) ≤ Pr{let x ← mx}[p x] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  calc ∑ a ∈ s, (if p a then Pr{let x ← mx}[x = a] else 0)
      = ∑ a ∈ s.filter p, 𝒟[mx] {a} := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun a _ => by rw [prEvent_eq_evalDist_singleton]
    _ = 𝒟[mx] (s.filter p : Set α) := MeasureTheory.sum_measure_singleton
    _ ≤ 𝒟[mx] {x | p x} := MeasureTheory.measure_mono fun a ha => (Finset.mem_filter.1 ha).2

/-- The point masses of the outputs of `mx` sum to at most `1`. -/
lemma tsum_prEvent_eq_le_one [EvalDistSemantics m] [LawfulEvalDistSemantics m] (mx : m α) :
    ∑' a, Pr{let x ← mx}[x = a] ≤ 1 := by
  simpa only [ite_true] using (tsum_ite_prEvent_eq_le_prEvent mx fun _ => True).trans
    (prEvent_le_one _)

/-- If `F z ≤ c` for every possible output `z` of `mx`, then the expectation of `F` under
`mx` is at most `c`. Missing mass only lowers the sum, so `mx` may fail. -/
lemma tsum_prEvent_mul_le_of_forall_mem_support [MonadAttach m] [WeaklyLawfulMonadAttach m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] (mx : m α) {F : α → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ z ∈ support mx, F z ≤ c) :
    ∑' z, Pr{let x ← mx}[x = z] * F z ≤ c := by
  calc ∑' z, Pr{let x ← mx}[x = z] * F z ≤ ∑' z, Pr{let x ← mx}[x = z] * c := by
        refine ENNReal.tsum_le_tsum fun z => ?_
        by_cases hz : z ∈ support mx
        · exact mul_le_mul' le_rfl (h z hz)
        · rw [prEvent_eq_zero_of_not_mem_support mx hz, zero_mul, zero_mul]
    _ = (∑' z, Pr{let x ← mx}[x = z]) * c := ENNReal.tsum_mul_right
    _ ≤ c := mul_le_of_le_one_left zero_le (tsum_prEvent_eq_le_one mx)

/-- If every possible continuation of a lossless `mx` gives the event `q` the same probability
`ε`, then so does `mx >>= f`. Upstream `prEvent_bind_eq_of_forall_eq` asks for this on every
input, including outputs `mx` never produces. -/
lemma prEvent_bind_eq_of_forall_eq_of_support [MonadAttach m] [WeaklyLawfulMonadAttach m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {β : Type} (mx : m α)
    (hmx : Pr{let _ ← mx}[True] = 1) (f : α → m β) (q : β → Prop) {ε : ℝ≥0∞}
    (h : ∀ a ∈ support mx, Pr{let y ← f a}[q y] = ε) :
    Pr{let y ← mx >>= f}[q y] = ε :=
  le_antisymm (prEvent_bind_le_of_forall_le_of_support mx f q fun a ha => (h a ha).le)
    (le_prEvent_bind_of_forall_le_of_support mx hmx f q fun a ha => (h a ha).ge)

/-- Active-parameter coupling for two independent samples.

Fix
* `lazy : A → B → A → ProbComp Y`,
* `base : A → ProbComp Y`,
* `y : Y`.

Assume, for every `x : A`,

`Pr{let z ← base x}[z = y]
 = Pr{let z ← do b ← $ᵗ B; let a ← $ᵗ A; lazy a b x}[z = y]`,

and, for every `x b a`,

`Pr{let z ← lazy a b x}[z = y] = Pr{let z ← lazy x b x}[z = y]`.

Then

`Pr{let x ← do b ← $ᵗ B; let a ← $ᵗ A; lazy a b a}[x = y]
 = Pr{let z ← do x ← $ᵗ A; base x}[z = y]`. -/
lemma prEvent_two_sample_active_param_eq
    {activeType passiveType outputType : Type 0}
    [SampleableType activeType] [SampleableType passiveType]
    (lazy : activeType → passiveType → activeType → ProbComp outputType)
    (base : activeType → ProbComp outputType) (y : outputType)
    (h_ih : ∀ x,
      Pr{let z ← base x}[z = y] = Pr{let z ← (do
        let passive ← ($ᵗ passiveType : ProbComp passiveType)
        let active ← ($ᵗ activeType : ProbComp activeType)
        lazy active passive x)}[z = y])
    (h_indep : ∀ x passive active,
      Pr{let z ← lazy active passive x}[z = y] = Pr{let z ← lazy x passive x}[z = y]) :
    Pr{let x ← (do
      let passive ← ($ᵗ passiveType : ProbComp passiveType)
      let active ← ($ᵗ activeType : ProbComp activeType)
      lazy active passive active)}[x = y] =
    Pr{let z ← (do
      let x ← ($ᵗ activeType : ProbComp activeType)
      base x)}[z = y] := by
  have eq_ih : Pr{let z ← (do
        let x ← ($ᵗ activeType : ProbComp activeType)
        base x)}[z = y] =
      Pr{let z ← (do
        let x ← ($ᵗ activeType : ProbComp activeType)
        let passive ← ($ᵗ passiveType : ProbComp passiveType)
        let active ← ($ᵗ activeType : ProbComp activeType)
        lazy active passive x)}[z = y] := by
    refine prEvent_bind_congr _ _ _ _ _ fun x => ?_
    exact h_ih x
  have eq_indep : Pr{let z ← (do
        let x ← ($ᵗ activeType : ProbComp activeType)
        let passive ← ($ᵗ passiveType : ProbComp passiveType)
        let active ← ($ᵗ activeType : ProbComp activeType)
        lazy active passive x)}[z = y] =
      Pr{let z ← (do
        let x ← ($ᵗ activeType : ProbComp activeType)
        let passive ← ($ᵗ passiveType : ProbComp passiveType)
        lazy x passive x)}[z = y] := by
    refine prEvent_bind_congr _ _ _ _ _ fun x => ?_
    refine prEvent_bind_congr _ _ _ _ _ fun passive => ?_
    exact prEvent_bind_eq_of_forall_eq _ (by simp) _ _ fun active => h_indep x passive active
  have eq_swap : Pr{let z ← (do
        let x ← ($ᵗ activeType : ProbComp activeType)
        let passive ← ($ᵗ passiveType : ProbComp passiveType)
        lazy x passive x)}[z = y] =
      Pr{let z ← (do
        let passive ← ($ᵗ passiveType : ProbComp passiveType)
        let x ← ($ᵗ activeType : ProbComp activeType)
        lazy x passive x)}[z = y] :=
    (OracleComp.EvalDistEq.bind_bind_swap
      (mx := ($ᵗ activeType : ProbComp activeType))
      (my := ($ᵗ passiveType : ProbComp passiveType))
      (f := fun x passive => lazy x passive x)).prEvent_eq (· = y)
  rw [eq_ih, eq_indep, eq_swap]

/-- Second-parameter coupling for two independent samples.

Fix
* `lazy : A → B → B → ProbComp Y`,
* `base : B → ProbComp Y`,
* `y : Y`.

Assume, for every `x : B`,

`Pr{let z ← base x}[z = y]
 = Pr{let z ← do second ← $ᵗ B; let first ← $ᵗ A; lazy first second x}[z = y]`,

and, for every `x first second`,

`Pr{let z ← lazy first second x}[z = y] = Pr{let z ← lazy first x x}[z = y]`.

Then

`Pr{let x ← do second ← $ᵗ B; let first ← $ᵗ A; lazy first second second}[x = y]
 = Pr{let z ← do x ← $ᵗ B; base x}[z = y]`. -/
lemma prEvent_two_sample_second_param_eq
    {firstType secondType outputType : Type 0}
    [SampleableType firstType] [SampleableType secondType]
    (lazy : firstType → secondType → secondType → ProbComp outputType)
    (base : secondType → ProbComp outputType) (y : outputType)
    (h_ih : ∀ x,
      Pr{let z ← base x}[z = y] = Pr{let z ← (do
        let second ← ($ᵗ secondType : ProbComp secondType)
        let first ← ($ᵗ firstType : ProbComp firstType)
        lazy first second x)}[z = y])
    (h_indep : ∀ x first second,
      Pr{let z ← lazy first second x}[z = y] = Pr{let z ← lazy first x x}[z = y]) :
    Pr{let x ← (do
      let second ← ($ᵗ secondType : ProbComp secondType)
      let first ← ($ᵗ firstType : ProbComp firstType)
      lazy first second second)}[x = y] =
    Pr{let z ← (do
      let x ← ($ᵗ secondType : ProbComp secondType)
      base x)}[z = y] := by
  have eq_ih : Pr{let z ← (do
        let x ← ($ᵗ secondType : ProbComp secondType)
        base x)}[z = y] =
      Pr{let z ← (do
        let x ← ($ᵗ secondType : ProbComp secondType)
        let second ← ($ᵗ secondType : ProbComp secondType)
        let first ← ($ᵗ firstType : ProbComp firstType)
        lazy first second x)}[z = y] := by
    refine prEvent_bind_congr _ _ _ _ _ fun x => ?_
    exact h_ih x
  have eq_indep : Pr{let z ← (do
        let x ← ($ᵗ secondType : ProbComp secondType)
        let second ← ($ᵗ secondType : ProbComp secondType)
        let first ← ($ᵗ firstType : ProbComp firstType)
        lazy first second x)}[z = y] =
      Pr{let z ← (do
        let x ← ($ᵗ secondType : ProbComp secondType)
        let first ← ($ᵗ firstType : ProbComp firstType)
        lazy first x x)}[z = y] := by
    refine prEvent_bind_congr _ _ _ _ _ fun x => ?_
    rw [(OracleComp.EvalDistEq.bind_bind_swap
      (mx := ($ᵗ secondType : ProbComp secondType))
      (my := ($ᵗ firstType : ProbComp firstType))
      (f := fun second first => lazy first second x)).prEvent_eq (· = y)]
    refine prEvent_bind_congr _ _ _ _ _ fun first => ?_
    exact prEvent_bind_eq_of_forall_eq _ (by simp) _ _ fun second => h_indep x first second
  have eq_swap : Pr{let z ← (do
        let x ← ($ᵗ secondType : ProbComp secondType)
        let first ← ($ᵗ firstType : ProbComp firstType)
        lazy first x x)}[z = y] =
      Pr{let x ← (do
        let second ← ($ᵗ secondType : ProbComp secondType)
        let first ← ($ᵗ firstType : ProbComp firstType)
        lazy first second second)}[x = y] := by
    rfl
  rw [eq_ih, eq_indep, eq_swap]

/-- Active-parameter coupling for three independent samples.

Fix
* `lazy : A → B → C → A → ProbComp Y`,
* `base : A → ProbComp Y`,
* `y : Y`.

Assume, for every `x : A`,

`Pr{let z ← base x}[z = y]
 = Pr{let z ← do a ← $ᵗ A; let b ← $ᵗ B; let c ← $ᵗ C; lazy a b c x}[z = y]`,

and, for every `x b a c`,

`Pr{let z ← lazy a b c x}[z = y] = Pr{let z ← lazy x b c x}[z = y]`.

Then

`Pr{let x ← do a ← $ᵗ A; let b ← $ᵗ B; let c ← $ᵗ C; lazy a b c a}[x = y]
 = Pr{let z ← do x ← $ᵗ A; base x}[z = y]`. -/
lemma prEvent_three_sample_active_param_eq
    {activeType paramType₁ paramType₂ outputType : Type 0}
    [SampleableType activeType] [SampleableType paramType₁] [SampleableType paramType₂]
    (lazy : activeType → paramType₁ → paramType₂ → activeType → ProbComp outputType)
    (base : activeType → ProbComp outputType) (y : outputType)
    (h_ih : ∀ x,
      Pr{let z ← base x}[z = y] = Pr{let z ← (do
        let active ← ($ᵗ activeType : ProbComp activeType)
        let param₁ ← ($ᵗ paramType₁ : ProbComp paramType₁)
        let param₂ ← ($ᵗ paramType₂ : ProbComp paramType₂)
        lazy active param₁ param₂ x)}[z = y])
    (h_indep : ∀ x param₁ active param₂,
      Pr{let z ← lazy active param₁ param₂ x}[z = y] =
      Pr{let z ← lazy x param₁ param₂ x}[z = y]) :
    Pr{let x ← (do
      let active ← ($ᵗ activeType : ProbComp activeType)
      let param₁ ← ($ᵗ paramType₁ : ProbComp paramType₁)
      let param₂ ← ($ᵗ paramType₂ : ProbComp paramType₂)
      lazy active param₁ param₂ active)}[x = y] =
    Pr{let z ← (do
      let x ← ($ᵗ activeType : ProbComp activeType)
      base x)}[z = y] := by
  have eq_ih : Pr{let z ← (do
        let x ← ($ᵗ activeType : ProbComp activeType)
        base x)}[z = y] =
      Pr{let z ← (do
        let x ← ($ᵗ activeType : ProbComp activeType)
        let active ← ($ᵗ activeType : ProbComp activeType)
        let param₁ ← ($ᵗ paramType₁ : ProbComp paramType₁)
        let param₂ ← ($ᵗ paramType₂ : ProbComp paramType₂)
        lazy active param₁ param₂ x)}[z = y] := by
    refine prEvent_bind_congr _ _ _ _ _ fun x => ?_
    exact h_ih x
  have eq_indep : Pr{let z ← (do
        let x ← ($ᵗ activeType : ProbComp activeType)
        let active ← ($ᵗ activeType : ProbComp activeType)
        let param₁ ← ($ᵗ paramType₁ : ProbComp paramType₁)
        let param₂ ← ($ᵗ paramType₂ : ProbComp paramType₂)
        lazy active param₁ param₂ x)}[z = y] =
      Pr{let z ← (do
        let x ← ($ᵗ activeType : ProbComp activeType)
        let param₁ ← ($ᵗ paramType₁ : ProbComp paramType₁)
        let param₂ ← ($ᵗ paramType₂ : ProbComp paramType₂)
        lazy x param₁ param₂ x)}[z = y] := by
    refine prEvent_bind_congr _ _ _ _ _ fun x => ?_
    refine prEvent_bind_eq_of_forall_eq _ (by simp) _ _ fun active => ?_
    refine prEvent_bind_congr _ _ _ _ _ fun param₁ => ?_
    refine prEvent_bind_congr _ _ _ _ _ fun param₂ => ?_
    exact h_indep x param₁ active param₂
  have eq_swap : Pr{let z ← (do
        let x ← ($ᵗ activeType : ProbComp activeType)
        let param₁ ← ($ᵗ paramType₁ : ProbComp paramType₁)
        let param₂ ← ($ᵗ paramType₂ : ProbComp paramType₂)
        lazy x param₁ param₂ x)}[z = y] =
      Pr{let x ← (do
        let active ← ($ᵗ activeType : ProbComp activeType)
        let param₁ ← ($ᵗ paramType₁ : ProbComp paramType₁)
        let param₂ ← ($ᵗ paramType₂ : ProbComp paramType₂)
        lazy active param₁ param₂ active)}[x = y] := by
    rfl
  rw [eq_ih, eq_indep, eq_swap]

/-- Second-and-third-parameter coupling for three independent samples.

Fix
* `lazy : A → B → C → B → C → ProbComp Y`,
* `base : B → C → ProbComp Y`,
* `y : Y`.

Assume, for every `x : B` and `z : C`,

`Pr{let w ← base x z}[w = y]
 = Pr{let w ← (do first ← $ᵗ A; second ← $ᵗ B; third ← $ᵗ C;
   lazy first second third x z)}[w = y]`,

and, for every `x z first second third`,

`Pr{let w ← lazy first second third x z}[w = y]
 = Pr{let w ← lazy first x third x z}[w = y]`,

and, for every `x z first third`,

`Pr{let w ← lazy first x third x z}[w = y]
 = Pr{let w ← lazy first x z x z}[w = y]`.

Then

`Pr{let x ← (do first ← $ᵗ A; second ← $ᵗ B; third ← $ᵗ C;
   lazy first second third second third)}[x = y]
 = Pr{let w ← do x ← $ᵗ B; let z ← $ᵗ C; base x z}[w = y]`. -/
lemma prEvent_three_sample_second_third_param_eq
    {firstType secondType thirdType outputType : Type 0}
    [SampleableType firstType] [SampleableType secondType] [SampleableType thirdType]
    (lazy : firstType → secondType → thirdType → secondType → thirdType →
      ProbComp outputType)
    (base : secondType → thirdType → ProbComp outputType) (y : outputType)
    (h_ih : ∀ x z,
      Pr{let w ← base x z}[w = y] = Pr{let w ← (do
        let first ← ($ᵗ firstType : ProbComp firstType)
        let second ← ($ᵗ secondType : ProbComp secondType)
        let third ← ($ᵗ thirdType : ProbComp thirdType)
        lazy first second third x z)}[w = y])
    (h_second_indep : ∀ x z first second third,
      Pr{let w ← lazy first second third x z}[w = y] = Pr{let w ← lazy first x third x z}[w = y])
    (h_third_indep : ∀ x z first third,
      Pr{let w ← lazy first x third x z}[w = y] = Pr{let w ← lazy first x z x z}[w = y]) :
    Pr{let x ← (do
      let first ← ($ᵗ firstType : ProbComp firstType)
      let second ← ($ᵗ secondType : ProbComp secondType)
      let third ← ($ᵗ thirdType : ProbComp thirdType)
      lazy first second third second third)}[x = y] =
    Pr{let w ← (do
      let x ← ($ᵗ secondType : ProbComp secondType)
      let z ← ($ᵗ thirdType : ProbComp thirdType)
      base x z)}[w = y] := by
  have eq_ih : Pr{let w ← (do
        let x ← ($ᵗ secondType : ProbComp secondType)
        let z ← ($ᵗ thirdType : ProbComp thirdType)
        base x z)}[w = y] =
      Pr{let w ← (do
        let x ← ($ᵗ secondType : ProbComp secondType)
        let z ← ($ᵗ thirdType : ProbComp thirdType)
        let first ← ($ᵗ firstType : ProbComp firstType)
        let second ← ($ᵗ secondType : ProbComp secondType)
        let third ← ($ᵗ thirdType : ProbComp thirdType)
        lazy first second third x z)}[w = y] := by
    refine prEvent_bind_congr _ _ _ _ _ fun x => ?_
    refine prEvent_bind_congr _ _ _ _ _ fun z => ?_
    exact h_ih x z
  have eq_second : Pr{let w ← (do
        let x ← ($ᵗ secondType : ProbComp secondType)
        let z ← ($ᵗ thirdType : ProbComp thirdType)
        let first ← ($ᵗ firstType : ProbComp firstType)
        let second ← ($ᵗ secondType : ProbComp secondType)
        let third ← ($ᵗ thirdType : ProbComp thirdType)
        lazy first second third x z)}[w = y] =
      Pr{let w ← (do
        let x ← ($ᵗ secondType : ProbComp secondType)
        let z ← ($ᵗ thirdType : ProbComp thirdType)
        let first ← ($ᵗ firstType : ProbComp firstType)
        let third ← ($ᵗ thirdType : ProbComp thirdType)
        lazy first x third x z)}[w = y] := by
    refine prEvent_bind_congr _ _ _ _ _ fun x => ?_
    refine prEvent_bind_congr _ _ _ _ _ fun z => ?_
    refine prEvent_bind_congr _ _ _ _ _ fun first => ?_
    refine prEvent_bind_eq_of_forall_eq _ (by simp) _ _ fun second => ?_
    refine prEvent_bind_congr _ _ _ _ _ fun third => ?_
    exact h_second_indep x z first second third
  have eq_third : Pr{let w ← (do
        let x ← ($ᵗ secondType : ProbComp secondType)
        let z ← ($ᵗ thirdType : ProbComp thirdType)
        let first ← ($ᵗ firstType : ProbComp firstType)
        let third ← ($ᵗ thirdType : ProbComp thirdType)
        lazy first x third x z)}[w = y] =
      Pr{let w ← (do
        let x ← ($ᵗ secondType : ProbComp secondType)
        let z ← ($ᵗ thirdType : ProbComp thirdType)
        let first ← ($ᵗ firstType : ProbComp firstType)
        lazy first x z x z)}[w = y] := by
    refine prEvent_bind_congr _ _ _ _ _ fun x => ?_
    refine prEvent_bind_congr _ _ _ _ _ fun z => ?_
    refine prEvent_bind_congr _ _ _ _ _ fun first => ?_
    exact prEvent_bind_eq_of_forall_eq _ (by simp) _ _ fun third => h_third_indep x z first third
  have eq_swap_z_first : Pr{let w ← (do
        let x ← ($ᵗ secondType : ProbComp secondType)
        let z ← ($ᵗ thirdType : ProbComp thirdType)
        let first ← ($ᵗ firstType : ProbComp firstType)
        lazy first x z x z)}[w = y] =
      Pr{let w ← (do
        let x ← ($ᵗ secondType : ProbComp secondType)
        let first ← ($ᵗ firstType : ProbComp firstType)
        let z ← ($ᵗ thirdType : ProbComp thirdType)
        lazy first x z x z)}[w = y] := by
    refine prEvent_bind_congr _ _ _ _ _ fun x => ?_
    exact (OracleComp.EvalDistEq.bind_bind_swap
      (mx := ($ᵗ thirdType : ProbComp thirdType))
      (my := ($ᵗ firstType : ProbComp firstType))
      (f := fun z first => lazy first x z x z)).prEvent_eq (· = y)
  have eq_swap_x_first : Pr{let w ← (do
        let x ← ($ᵗ secondType : ProbComp secondType)
        let first ← ($ᵗ firstType : ProbComp firstType)
        let z ← ($ᵗ thirdType : ProbComp thirdType)
        lazy first x z x z)}[w = y] =
      Pr{let x ← (do
        let first ← ($ᵗ firstType : ProbComp firstType)
        let second ← ($ᵗ secondType : ProbComp secondType)
        let third ← ($ᵗ thirdType : ProbComp thirdType)
        lazy first second third second third)}[x = y] :=
    (OracleComp.EvalDistEq.bind_bind_swap
      (mx := ($ᵗ secondType : ProbComp secondType))
      (my := ($ᵗ firstType : ProbComp firstType))
      (f := fun x first => do
        let z ← ($ᵗ thirdType : ProbComp thirdType)
        lazy first x z x z)).prEvent_eq (· = y)
  rw [eq_ih, eq_second, eq_third, eq_swap_z_first, eq_swap_x_first]

end ToVCVio
