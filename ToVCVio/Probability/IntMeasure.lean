/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.Support

/-!
# Finite integer counting measures

This file defines finite integer-valued counting measures on `ℤ` and their
basic combinators: windows, total mass, additive convolution, and the product
measure.

Mathematically, an `IntMeasure` is a finite counting measure on the discrete
space `ℤ`: if `F : ℤ →₀ ℕ`, then the measure of a subset `A` is

`μ_F(A) = ∑_{v ∈ A} F(v)`.

The value `F(v)` is the mass of the singleton `{v}`. These measures are not
probability measures in general; their total mass is usually a large natural
number, and probabilities are obtained only after normalization. The main
objects are:

* `IntMeasure`: a finite counting measure on integer outcomes;
* `MeasureWindow`: all nonzero mass lies inside a stated interval;
* `enumMeasure`: the counting measure of a value map over `range N`;
* `totalMass`: the total mass of a finite counting measure;
* multiplication on `IntMeasure`: additive convolution, the counting measure of
  an independent sum;
* `productMeasure`: the counting measure of an independent product.

These measures support exact failure-probability certificates for
lattice-based schemes, which compose per-coefficient noise measures and
evaluate their tail masses.
-/

namespace ToVCVio

/-- An integer-valued finite counting measure on `ℤ`, represented as a finitely
supported map from integer outcomes to natural-number masses. The inherited
multiplication is additive convolution: `F * G` assigns to `v` the sum of
`F a * G b` over `a + b = v`, the finite measure of a sum of independent draws.
Similarly, `F ^ n` is the finite measure of an `n`-fold independent sum. -/
abbrev IntMeasure := AddMonoidAlgebra ℕ ℤ

/-- Compatibility coercion to the coefficient Finsupp. -/
instance : Coe IntMeasure (ℤ →₀ ℕ) := ⟨AddMonoidAlgebra.coeff⟩

/-- Compatibility coercion to coefficient evaluation. -/
instance : CoeFun IntMeasure (fun _ => ℤ → ℕ) := ⟨fun F => F.coeff⟩

/-- The counting measure `F` has all its nonzero mass inside `[lo, hi]`. -/
def MeasureWindow (F : IntMeasure) (lo hi : ℤ) : Prop :=
  ∀ v : ℤ, F v ≠ 0 → lo ≤ v ∧ v ≤ hi

/-- A window may be widened. -/
theorem MeasureWindow.mono {F : IntMeasure} {lo hi lo' hi' : ℤ} (h : MeasureWindow F lo hi)
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi') : MeasureWindow F lo' hi' := fun v hv =>
  ⟨hlo.trans (h v hv).1, (h v hv).2.trans hhi⟩

/-- A windowed measure vanishes outside its window. -/
theorem MeasureWindow.apply_eq_zero {F : IntMeasure} {lo hi : ℤ} (h : MeasureWindow F lo hi)
    {v : ℤ} (hv : v < lo ∨ hi < v) : F v = 0 := by
  by_contra hne
  rcases h v hne with ⟨h1, h2⟩
  omega

/-! ## Counting measures -/

/-- The counting measure of the value map `g` over `range N`: the mass of
`v` is the number of `x < N` with `g x = v`. -/
noncomputable def enumMeasure (N : ℕ) (g : ℕ → ℤ) : IntMeasure :=
  ∑ x ∈ Finset.range N, AddMonoidAlgebra.single (g x) 1

/-- The mass of `v` under `enumMeasure N g` counts the preimages of `v`. -/
theorem enumMeasure_apply (N : ℕ) (g : ℕ → ℤ) (v : ℤ) :
    enumMeasure N g v = ((Finset.range N).filter fun x => g x = v).card := by
  rw [enumMeasure, AddMonoidAlgebra.coeff_sum, Finset.card_filter]
  refine (Finsupp.finsetSum_apply _ _ _).trans (Finset.sum_congr rfl fun x _ => ?_)
  exact Finsupp.single_apply

/-- An enumerated counting measure is windowed by pointwise bounds on the
values. -/
theorem measureWindow_enumMeasure {N : ℕ} {g : ℕ → ℤ} {lo hi : ℤ}
    (h : ∀ x < N, lo ≤ g x ∧ g x ≤ hi) : MeasureWindow (enumMeasure N g) lo hi := by
  intro v hv
  rw [enumMeasure_apply] at hv
  obtain ⟨x, hx⟩ := Finset.card_ne_zero.mp hv
  rw [Finset.mem_filter, Finset.mem_range] at hx
  exact hx.2 ▸ h x hx.1

/-! ## Total mass -/

/-- The total mass of a finite counting measure. -/
def totalMass (F : IntMeasure) : ℕ :=
  Finsupp.sum F.coeff fun _ m => m

theorem totalMass_single (v : ℤ) (m : ℕ) :
    totalMass (AddMonoidAlgebra.single v m) = m :=
  Finsupp.sum_single_index rfl

/-- Total mass, as an additive monoid homomorphism. -/
def totalMassHom : IntMeasure →+ ℕ where
  toFun := totalMass
  map_zero' := rfl
  map_add' _ _ := Finsupp.sum_add_index' (fun _ => rfl) fun _ _ _ => rfl

theorem totalMass_mul (F G : IntMeasure) :
    totalMass (F * G) = totalMass F * totalMass G := by
  rw [AddMonoidAlgebra.mul_def]
  refine (map_finsuppSum totalMassHom _ _).trans ?_
  have hinner : ∀ (a : ℤ) (m : ℕ),
      (Finsupp.sum G.coeff fun b k => totalMass (AddMonoidAlgebra.single (a + b) (m * k))) =
        m * totalMass G := by
    intro a m
    refine (Finsupp.sum_congr fun b _ => totalMass_single _ _).trans ?_
    exact (Finsupp.mul_sum _ _).symm
  calc (Finsupp.sum F.coeff fun a m =>
          totalMassHom (Finsupp.sum G.coeff fun b k => AddMonoidAlgebra.single (a + b) (m * k)))
      = Finsupp.sum F.coeff fun a m => m * totalMass G := by
        refine Finsupp.sum_congr fun a _ => ?_
        refine (map_finsuppSum totalMassHom _ _).trans ?_
        exact hinner a _
    _ = totalMass F * totalMass G := (Finsupp.sum_mul _ _).symm

theorem totalMass_one : totalMass (1 : IntMeasure) = 1 := by
  rw [AddMonoidAlgebra.one_def]
  exact totalMass_single 0 1

theorem totalMass_pow (F : IntMeasure) (n : ℕ) :
    totalMass (F ^ n) = totalMass F ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, totalMass_one]
  | succ n ih => rw [pow_succ, pow_succ, totalMass_mul, ih]

theorem totalMass_enumMeasure (N : ℕ) (g : ℕ → ℤ) : totalMass (enumMeasure N g) = N := by
  rw [enumMeasure]
  refine (map_sum totalMassHom _ _).trans ?_
  have : ∀ x ∈ Finset.range N, totalMassHom (AddMonoidAlgebra.single (g x) 1) = 1 :=
    fun x _ => totalMass_single _ _
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

/-! ## Windows of convolutions, powers, and products -/

theorem measureWindow_mul {F G : IntMeasure} {lo₁ hi₁ lo₂ hi₂ : ℤ}
    (hF : MeasureWindow F lo₁ hi₁) (hG : MeasureWindow G lo₂ hi₂) :
    MeasureWindow (F * G) (lo₁ + lo₂) (hi₁ + hi₂) := by
  intro v hv
  have hmem := AddMonoidAlgebra.support_coeff_mul_subset F G (Finsupp.mem_support_iff.mpr hv)
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hmem
  have h₁ := hF a (Finsupp.mem_support_iff.mp ha)
  have h₂ := hG b (Finsupp.mem_support_iff.mp hb)
  exact ⟨add_le_add h₁.1 h₂.1, add_le_add h₁.2 h₂.2⟩

theorem measureWindow_pow {F : IntMeasure} {lo hi : ℤ} (hF : MeasureWindow F lo hi) (n : ℕ) :
    MeasureWindow (F ^ n) (n * lo) (n * hi) := by
  induction n with
  | zero =>
    intro v hv
    rw [pow_zero, AddMonoidAlgebra.one_def] at hv
    have : v = 0 := by
      by_contra hne
      exact hv (Finsupp.single_eq_of_ne fun h => hne h)
    simp [this]
  | succ n ih =>
    have h := measureWindow_mul ih hF
    have hlo : (n : ℤ) * lo + lo = ((n + 1 : ℕ) : ℤ) * lo := by push_cast; ring
    have hhi : (n : ℤ) * hi + hi = ((n + 1 : ℕ) : ℤ) * hi := by push_cast; ring
    rw [hlo, hhi] at h
    exact fun v hv => h v (by rwa [pow_succ] at hv)

/-! ## Windowed convolution values -/

/-- The value of a convolution over a window of the left factor: with `F` inside
`[lo, lo + n - 1]`, the mass of `F * G` at `v` is the window sum of
`F (lo + i) * G (v - (lo + i))`. -/
theorem mul_apply_window {F G : IntMeasure} {lo : ℤ} {n : ℕ}
    (hF : MeasureWindow F lo (lo + n - 1)) (v : ℤ) :
  (F * G) v = ∑ i ∈ Finset.range n, F (lo + i) * G (v - (lo + i)) := by
  rw [AddMonoidAlgebra.coeff_mul]
  have hinner : ∀ (a : ℤ) (m : ℕ),
      (Finsupp.sum G.coeff fun b k => if a + b = v then m * k else 0) =
        m * G.coeff (v - a) := by
    intro a m
    have hcong : (fun (b : ℤ) (k : ℕ) => if a + b = v then m * k else 0) =
        fun b k => if b = v - a then m * k else 0 := by
      funext b k
      exact if_congr (by omega) rfl rfl
    rw [hcong, Finsupp.sum_ite_eq' G.coeff (v - a) fun _ k => m * k]
    by_cases hmem : v - a ∈ G.coeff.support
    · rw [if_pos hmem]
    · rw [if_neg hmem, Finsupp.notMem_support_iff.mp hmem, mul_zero]
  rw [Finsupp.sum_congr (g2 := fun a m => m * G.coeff (v - a))
    fun a _ => hinner a (F.coeff a)]
  rw [Finsupp.sum_of_support_subset F.coeff
    (s := (Finset.range n).image fun i : ℕ => lo + (i : ℤ))
    ?_ (fun a m => m * G.coeff (v - a)) fun i _ => zero_mul _]
  · rw [Finset.sum_image fun i _ j _ h => by omega]
  · intro a ha
    have hw := hF a (Finsupp.mem_support_iff.mp ha)
    rw [Finset.mem_image]
    exact ⟨(a - lo).toNat, Finset.mem_range.mpr (by omega), by omega⟩

/-! ## Product measures -/

/-- The product measure of two finite measures: `productMeasure F G` assigns to `v` the
sums of `F a * G b` over `a * b = v`, the finite measure of a product of
independent draws. -/
noncomputable def productMeasure (F G : IntMeasure) : IntMeasure :=
  Finsupp.sum F.coeff fun a m =>
    Finsupp.sum G.coeff fun b k => AddMonoidAlgebra.single (a * b) (m * k)

theorem totalMass_productMeasure (F G : IntMeasure) :
    totalMass (productMeasure F G) = totalMass F * totalMass G := by
  rw [productMeasure]
  refine (map_finsuppSum totalMassHom _ _).trans ?_
  calc (Finsupp.sum F.coeff fun a m =>
          totalMassHom (Finsupp.sum G.coeff fun b k => AddMonoidAlgebra.single (a * b) (m * k)))
      = Finsupp.sum F.coeff fun a m => m * totalMass G := by
        refine Finsupp.sum_congr fun a _ => ?_
        refine (map_finsuppSum totalMassHom _ _).trans ?_
        refine (Finsupp.sum_congr fun b _ => totalMass_single _ _).trans ?_
        exact (Finsupp.mul_sum _ _).symm
    _ = totalMass F * totalMass G := (Finsupp.sum_mul _ _).symm

/-- The mass of `v` under `productMeasure F G`, as a double sum over the factors. -/
theorem productMeasure_apply (F G : IntMeasure) (v : ℤ) :
    productMeasure F G v =
      Finsupp.sum F fun a m => Finsupp.sum G fun b k =>
        if a * b = v then m * k else 0 := by
  simp only [productMeasure, AddMonoidAlgebra.coeff_finsuppSum, Finsupp.sum_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

/-- Any nonzero mass of `productMeasure F G` decomposes as a product of masses. -/
theorem exists_of_productMeasure_apply_ne_zero {F G : IntMeasure} {v : ℤ}
    (hv : productMeasure F G v ≠ 0) : ∃ a b, F a ≠ 0 ∧ G b ≠ 0 ∧ a * b = v := by
  rw [productMeasure_apply, Finsupp.sum] at hv
  obtain ⟨a, ha, hane⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  rw [Finsupp.sum] at hane
  obtain ⟨b, hb, hbne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hane
  refine ⟨a, b, Finsupp.mem_support_iff.mp ha, Finsupp.mem_support_iff.mp hb, ?_⟩
  by_contra hne
  exact hbne (if_neg hne)

/-- A product of symmetrically windowed finite measures is windowed by the
product bound. -/
theorem measureWindow_productMeasure {F G : IntMeasure} {a b : ℤ}
    (hF : MeasureWindow F (-a) a) (hG : MeasureWindow G (-b) b) :
    MeasureWindow (productMeasure F G) (-(a * b)) (a * b) := by
  intro v hv
  obtain ⟨x, y, hx, hy, rfl⟩ := exists_of_productMeasure_apply_ne_zero hv
  have h₁ := hF x hx
  have h₂ := hG y hy
  have habs : |x * y| ≤ a * b := by
    rw [abs_mul]
    exact mul_le_mul (abs_le.mpr ⟨h₁.1, h₁.2⟩) (abs_le.mpr ⟨h₂.1, h₂.2⟩)
      (abs_nonneg y) ((abs_nonneg x).trans (abs_le.mpr ⟨h₁.1, h₁.2⟩))
  exact abs_le.mp habs

end ToVCVio
