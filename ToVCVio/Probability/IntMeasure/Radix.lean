/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import ToVCVio.Probability.IntMeasure
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic

/-! # Generic radix packing of finite integer counting measures -/

@[expose] public section

open ToVCVio
open scoped ENNReal BigOperators

namespace ToVCVio.Radix

/-! ## Radix packing of digit sequences -/

/-- A digit sequence bounded by the radix packs below the radix power. -/
private theorem sum_mul_pow_lt {R n : ℕ} {f : ℕ → ℕ} (h : ∀ i < n, f i < R) :
    ∑ i ∈ Finset.range n, f i * R ^ i < R ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hfn : f n < R := h n n.lt_succ_self
    have ihh := ih fun i hi => h i (hi.trans n.lt_succ_self)
    calc ∑ i ∈ Finset.range (n + 1), f i * R ^ i
        = (∑ i ∈ Finset.range n, f i * R ^ i) + f n * R ^ n := Finset.sum_range_succ _ n
      _ < R ^ n + f n * R ^ n := by omega
      _ = (1 + f n) * R ^ n := by ring
      _ ≤ R * R ^ n := Nat.mul_le_mul_right _ (by omega)
      _ = R ^ (n + 1) := by ring

/-- A digit sequence with doubled digits below the radix packs below half the
radix power, in the form needed for the strict repunit bound. -/
private theorem two_mul_sum_mul_pow_add_two_le {R : ℕ} {f : ℕ → ℕ} (n : ℕ)
    (h : ∀ i < n, 2 * f i < R) :
    2 * (∑ i ∈ Finset.range n, f i * R ^ i) + 2 ≤ R ^ n + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hfn : 2 * f n < R := h n n.lt_succ_self
    obtain ⟨r, rfl⟩ : ∃ r, R = r + 1 := ⟨R - 1, by omega⟩
    have ihh := ih fun i hi => h i (hi.trans n.lt_succ_self)
    calc 2 * (∑ i ∈ Finset.range (n + 1), f i * (r + 1) ^ i) + 2
        = (2 * (∑ i ∈ Finset.range n, f i * (r + 1) ^ i) + 2) + (2 * f n) * (r + 1) ^ n := by
          rw [Finset.sum_range_succ]; ring
      _ ≤ ((r + 1) ^ n + 1) + r * (r + 1) ^ n :=
          Nat.add_le_add ihh (Nat.mul_le_mul_right _ (by omega))
      _ = (r + 1) ^ n * (r + 1) + 1 := by ring
      _ = (r + 1) ^ (n + 1) + 1 := by rw [pow_succ]

/-- Strict form: such a sequence packs strictly below the repunit `R ^ n - 1`. -/
private theorem sum_mul_pow_lt_pred {R n : ℕ} {f : ℕ → ℕ} (hR : 2 ≤ R) (hn : 0 < n)
    (h : ∀ i < n, 2 * f i < R) :
    ∑ i ∈ Finset.range n, f i * R ^ i < R ^ n - 1 := by
  have h2 := two_mul_sum_mul_pow_add_two_le n h
  have hpow : R ≤ R ^ n := Nat.le_self_pow hn.ne' R
  omega

/-- Base-`R` digit extraction from a packed digit sequence. -/
private theorem sum_mul_pow_div_pow_mod {R n : ℕ} {f : ℕ → ℕ} (h : ∀ i < n, f i < R)
    {t : ℕ} (ht : t < n) :
    (∑ i ∈ Finset.range n, f i * R ^ i) / R ^ t % R = f t := by
  have hR : 0 < R := (Nat.zero_le _).trans_lt (h t ht)
  have hsplit := Finset.sum_range_add (fun i => f i * R ^ i) t (n - t)
  rw [show t + (n - t) = n from by omega] at hsplit
  obtain ⟨s, hs⟩ : ∃ s, n - t = s + 1 := ⟨n - t - 1, by omega⟩
  rw [hs, Finset.sum_range_succ'] at hsplit
  have htail : ∀ j : ℕ, f (t + (j + 1)) * R ^ (t + (j + 1)) =
      R ^ t * (R * (f (t + (j + 1)) * R ^ j)) := by
    intro j
    rw [pow_add, pow_succ]
    ring
  rw [Finset.sum_congr rfl fun j _ => htail j, ← Finset.mul_sum,
    show t + 0 = t from rfl] at hsplit
  have hsum_inner : ∑ i ∈ Finset.range s, R * (f (t + (i + 1)) * R ^ i) =
      R * ∑ j ∈ Finset.range s, f (t + (j + 1)) * R ^ j := (Finset.mul_sum _ _ _).symm
  rw [hsum_inner] at hsplit
  have hform : ∑ i ∈ Finset.range n, f i * R ^ i =
      (∑ i ∈ Finset.range t, f i * R ^ i) +
        R ^ t * (f t + R * ∑ j ∈ Finset.range s, f (t + (j + 1)) * R ^ j) := by
    rw [hsplit]; ring
  have hA : (∑ i ∈ Finset.range t, f i * R ^ i) < R ^ t :=
    sum_mul_pow_lt fun i hi => h i (hi.trans ht)
  rw [hform, Nat.add_mul_div_left _ _ (pow_pos hR t), Nat.div_eq_of_lt hA, zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (h t ht)]

/-- Splitting a packed sequence of `q * m` digits into `m` blocks of `q`. -/
private theorem sum_range_mul_eq_sum_sum {q m : ℕ} (g : ℕ → ℕ) :
    ∑ i ∈ Finset.range (q * m), g i =
      ∑ j ∈ Finset.range m, ∑ t ∈ Finset.range q, g (q * j + t) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- A range sum of radix terms is unchanged by padding with zero digits. -/
private theorem sum_mul_pow_pad {R q n : ℕ} (hqn : q ≤ n) (f : ℕ → ℕ) :
    ∑ t ∈ Finset.range q, f t * R ^ t =
      ∑ t ∈ Finset.range n, (if t < q then f t else 0) * R ^ t := by
  rw [show (∑ t ∈ Finset.range q, f t * R ^ t) =
      ∑ t ∈ Finset.range q, (if t < q then f t else 0) * R ^ t from
    Finset.sum_congr rfl fun t ht => by rw [ite_eq_left (Finset.mem_range.mp ht)]]
  exact Finset.sum_subset (Finset.range_subset_range.mpr hqn) fun t _ htq => by
    rw [ite_eq_right (by simpa [Finset.mem_range] using htq), zero_mul]

/-- A range sum of radix terms in blocks: `b` blocks of `a` digits, with the
block shift pulled out as a power of `R ^ a`. -/
private theorem sum_mul_pow_blocks {R : ℕ} (a b : ℕ) (f : ℕ → ℕ) :
    ∑ t ∈ Finset.range (a * b), f t * R ^ t =
      ∑ j ∈ Finset.range b,
        (∑ i ∈ Finset.range a, f (a * j + i) * R ^ i) * (R ^ a) ^ j := by
  rw [sum_range_mul_eq_sum_sum fun t => f t * R ^ t]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_add, pow_mul]
  ring

/-- Congruence of finite sums from termwise congruence. -/
private theorem sum_modEq {M : ℕ} {ι : Type*} {s : Finset ι} {f g : ι → ℕ}
    (h : ∀ i ∈ s, f i ≡ g i [MOD M]) :
    (∑ i ∈ s, f i) ≡ ∑ i ∈ s, g i [MOD M] := by
  classical
  induction s using Finset.cons_induction with
  | empty => rfl
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    exact (h a (Finset.mem_cons_self a s)).add
      (ih fun i hi => h i (Finset.mem_cons_of_mem hi))

/-- Reduction of a packed sequence modulo the repunit `R ^ q - 1` folds the
digits `q` apart onto each other. -/
private theorem sum_mul_pow_mod_repunit {R q m : ℕ} {f : ℕ → ℕ} (hR : 2 ≤ R) (hq : 0 < q)
    (hfold : ∀ t < q, 2 * (∑ j ∈ Finset.range m, f (q * j + t)) < R) :
    (∑ i ∈ Finset.range (q * m), f i * R ^ i) % (R ^ q - 1) =
      ∑ t ∈ Finset.range q, (∑ j ∈ Finset.range m, f (q * j + t)) * R ^ t := by
  have hRq : 2 ≤ R ^ q := hR.trans (Nat.le_self_pow hq.ne' R)
  have hone : R ^ q ≡ 1 [MOD R ^ q - 1] := by
    have heq : R ^ q = (R ^ q - 1) + 1 := by omega
    rw [heq]
    exact Nat.add_modEq_left
  have hterm : ∀ j t : ℕ, f (q * j + t) * R ^ (q * j + t) ≡
      f (q * j + t) * R ^ t [MOD R ^ q - 1] := by
    intro j t
    have hpow : R ^ (q * j + t) = R ^ t * (R ^ q) ^ j := by
      rw [pow_add, pow_mul]
      ring
    have hcong : (R ^ q) ^ j ≡ 1 ^ j [MOD R ^ q - 1] := hone.pow j
    rw [one_pow] at hcong
    calc f (q * j + t) * R ^ (q * j + t)
        = f (q * j + t) * R ^ t * (R ^ q) ^ j := by rw [hpow]; ring
      _ ≡ f (q * j + t) * R ^ t * 1 [MOD R ^ q - 1] := hcong.mul_left _
      _ = f (q * j + t) * R ^ t := by ring
  have hmod : (∑ i ∈ Finset.range (q * m), f i * R ^ i) ≡
      ∑ t ∈ Finset.range q, (∑ j ∈ Finset.range m, f (q * j + t)) * R ^ t
        [MOD R ^ q - 1] := by
    rw [sum_range_mul_eq_sum_sum fun i => f i * R ^ i]
    have hswap : ∑ t ∈ Finset.range q, (∑ j ∈ Finset.range m, f (q * j + t)) * R ^ t =
        ∑ j ∈ Finset.range m, ∑ t ∈ Finset.range q, f (q * j + t) * R ^ t := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun t _ => Finset.sum_mul _ _ _
    rw [hswap]
    exact sum_modEq fun j _ => sum_modEq fun t _ => hterm j t
  have hRHSlt : (∑ t ∈ Finset.range q, (∑ j ∈ Finset.range m, f (q * j + t)) * R ^ t) <
      R ^ q - 1 := sum_mul_pow_lt_pred hR hq hfold
  calc (∑ i ∈ Finset.range (q * m), f i * R ^ i) % (R ^ q - 1)
      = (∑ t ∈ Finset.range q, (∑ j ∈ Finset.range m, f (q * j + t)) * R ^ t) %
        (R ^ q - 1) := hmod
    _ = ∑ t ∈ Finset.range q, (∑ j ∈ Finset.range m, f (q * j + t)) * R ^ t :=
        Nat.mod_eq_of_lt hRHSlt

/-! ## Packing integer measures -/

/-- Evaluation at `R` of the generating polynomial for the finite measure `F`
against the base point `lo`: the mass at integer `v` contributes
`F v * R^(v - lo)`. -/
noncomputable def measurePack (R : ℕ) (lo : ℤ) (F : IntMeasure) : ℕ :=
  Finsupp.sum F fun v m => m * R ^ (v - lo).toNat

/-- Packing, as an additive monoid homomorphism. -/
private noncomputable def measurePackHom (R : ℕ) (lo : ℤ) : IntMeasure →+ ℕ where
  toFun := measurePack R lo
  map_zero' := Finsupp.sum_zero_index
  map_add' _ _ := Finsupp.sum_add_index' (fun _ => zero_mul _) fun _ _ _ => add_mul _ _ _

theorem measurePack_single (R : ℕ) (lo v : ℤ) (m : ℕ) :
    measurePack R lo (AddMonoidAlgebra.single v m) = m * R ^ (v - lo).toNat :=
  Finsupp.sum_single_index (zero_mul _)

/-- Packing turns convolution into multiplication: the packed product of two
windowed measures is the product of their packings. -/
theorem measurePack_mul {R : ℕ} {F G : IntMeasure} {lo₁ hi₁ lo₂ hi₂ : ℤ}
    (hF : MeasureWindow F lo₁ hi₁) (hG : MeasureWindow G lo₂ hi₂) :
    measurePack R (lo₁ + lo₂) (F * G) = measurePack R lo₁ F * measurePack R lo₂ G := by
  rw [AddMonoidAlgebra.mul_def]
  refine (map_finsuppSum (measurePackHom R (lo₁ + lo₂)) _ _).trans ?_
  have hRHS : measurePack R lo₁ F * measurePack R lo₂ G =
      Finsupp.sum F fun a m => Finsupp.sum G fun b k =>
        m * R ^ (a - lo₁).toNat * (k * R ^ (b - lo₂).toNat) := by
    refine (Finsupp.sum_mul _ _).trans ?_
    exact Finsupp.sum_congr fun a _ => Finsupp.mul_sum _ _
  rw [hRHS]
  refine Finsupp.sum_congr fun a ha => ?_
  refine (map_finsuppSum (measurePackHom R (lo₁ + lo₂)) _ _).trans ?_
  refine Finsupp.sum_congr fun b hb => ?_
  refine (measurePack_single _ _ _ _).trans ?_
  have h₁ := (hF a (Finsupp.mem_support_iff.mp ha)).1
  have h₂ := (hG b (Finsupp.mem_support_iff.mp hb)).1
  have hsplit : (a + b - (lo₁ + lo₂)).toNat = (a - lo₁).toNat + (b - lo₂).toNat := by omega
  rw [hsplit, pow_add]
  ring

/-- Packing turns an iterated convolution into a power. -/
theorem measurePack_pow {R : ℕ} {F : IntMeasure} {lo hi : ℤ}
    (hF : MeasureWindow F lo hi) (n : ℕ) :
    measurePack R (n * lo) (F ^ n) = measurePack R lo F ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, AddMonoidAlgebra.one_def,
      show ((0 : ℕ) : ℤ) * lo = 0 by simp, measurePack_single]
    simp
  | succ n ih =>
    have hcast : ((n + 1 : ℕ) : ℤ) * lo = (n : ℤ) * lo + lo := by push_cast; ring
    rw [pow_succ, pow_succ, hcast, measurePack_mul (measureWindow_pow hF n) hF, ih]

/-- The packing of an enumerated counting measure, as a sum over the
enumeration. -/
theorem measurePack_enumMeasure (R : ℕ) (lo : ℤ) (N : ℕ) (g : ℕ → ℤ) :
    measurePack R lo (enumMeasure N g) = ∑ x ∈ Finset.range N, R ^ (g x - lo).toNat := by
  rw [enumMeasure]
  refine (map_sum (measurePackHom R lo) _ _).trans ?_
  exact Finset.sum_congr rfl fun x _ => (measurePack_single _ _ _ _).trans (one_mul _)

private theorem productMeasure_enumMeasure_left (N : ℕ) (g : ℕ → ℤ) (G : IntMeasure) :
    productMeasure (enumMeasure N g) G =
      ∑ x ∈ Finset.range N, Finsupp.sum G fun b k =>
        AddMonoidAlgebra.single (g x * b) k := by
  rw [enumMeasure, productMeasure, AddMonoidAlgebra.coeff_sum]
  refine Eq.trans (Finsupp.sum_finsetSum_index
    (fun _ => by simp)
    fun a m₁ m₂ => ?hadd).symm ?_
  case hadd =>
    refine Eq.trans (Finsupp.sum_congr fun b k => ?_) Finsupp.sum_add
    rw [add_mul]
    exact AddMonoidAlgebra.single_add _ _ _
  refine Finset.sum_congr rfl fun x _ => ?_
  refine (Finsupp.sum_single_index (by simp)).trans ?_
  exact Finsupp.sum_congr fun b _ => by rw [one_mul]

/-- The packing of `productMeasure` with an enumerated left factor, as a window sum of
the right factor. -/
theorem measurePack_productMeasure_enumMeasure {R : ℕ} {G : IntMeasure} {lo₂ : ℤ} {n₂ : ℕ}
    (hG : MeasureWindow G lo₂ (lo₂ + n₂ - 1)) (lo : ℤ) (N : ℕ) (g : ℕ → ℤ) :
    measurePack R lo (productMeasure (enumMeasure N g) G) =
      ∑ x ∈ Finset.range N, ∑ i ∈ Finset.range n₂,
        G (lo₂ + i) * R ^ (g x * (lo₂ + i) - lo).toNat := by
  rw [productMeasure_enumMeasure_left]
  refine (map_sum (measurePackHom R lo) _ _).trans ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  refine (map_finsuppSum (measurePackHom R lo) _ _).trans ?_
  refine (Finsupp.sum_congr (g2 := fun b k => k * R ^ (g x * b - lo).toNat)
    fun b _ => measurePack_single _ _ _ _).trans ?_
  rw [Finsupp.sum_of_support_subset G
    (s := (Finset.range n₂).image fun i : ℕ => lo₂ + (i : ℤ))
    ?_ (fun b k => k * R ^ (g x * b - lo).toNat) fun i _ => zero_mul _]
  · rw [Finset.sum_image fun i _ j _ h => by omega]
  · intro b hb
    have hw := hG b (Finsupp.mem_support_iff.mp hb)
    rw [Finset.mem_image]
    exact ⟨(b - lo₂).toNat, Finset.mem_range.mpr (by omega), by omega⟩

/-- The packing of a windowed measure as a window sum of its masses. -/
theorem measurePack_eq_range_sum {R : ℕ} {F : IntMeasure} {lo : ℤ} {n : ℕ}
    (hF : MeasureWindow F lo (lo + n - 1)) :
    measurePack R lo F = ∑ i ∈ Finset.range n, F (lo + i) * R ^ i := by
  rw [measurePack]
  rw [Finsupp.sum_of_support_subset F
    (s := (Finset.range n).image fun i : ℕ => lo + (i : ℤ))
    ?_ (fun v m => m * R ^ (v - lo).toNat) fun i _ => zero_mul _]
  · rw [Finset.sum_image fun i _ j _ h => by omega]
    exact Finset.sum_congr rfl fun i _ => by rw [show (lo + (i : ℤ) - lo).toNat = i by omega]
  · intro a ha
    have hw := hF a (Finsupp.mem_support_iff.mp ha)
    rw [Finset.mem_image]
    exact ⟨(a - lo).toNat, Finset.mem_range.mpr (by omega), by omega⟩

/-- The total mass of a windowed measure as a window sum of its masses. -/
theorem totalMass_eq_range_sum {F : IntMeasure} {lo : ℤ} {n : ℕ}
    (hF : MeasureWindow F lo (lo + n - 1)) :
    totalMass F = ∑ i ∈ Finset.range n, F (lo + i) := by
  have h := measurePack_eq_range_sum (R := 1) hF
  rw [measurePack] at h
  simp only [one_pow, mul_one] at h
  rw [totalMass]
  exact h

/-- Every mass of a convolution with a pointwise-bounded measure is at most the
total mass of the other factor times the bound. -/
theorem mul_apply_le {F G : IntMeasure} {lo : ℤ} {n : ℕ} {B : ℕ}
    (hF : MeasureWindow F lo (lo + n - 1)) (hB : ∀ b, G b ≤ B) (v : ℤ) :
    (F * G) v ≤ totalMass F * B := by
  rw [mul_apply_window hF v, totalMass_eq_range_sum hF, Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (hB _)

/-- A mass of a windowed measure is a base-`R` digit of its packing. -/
theorem measurePack_digit {R : ℕ} {F : IntMeasure} {lo : ℤ} {n : ℕ}
    (hF : MeasureWindow F lo (lo + n - 1)) (hd : ∀ v, F v < R) {t : ℕ} (ht : t < n) :
    measurePack R lo F / R ^ t % R = F (lo + t) := by
  rw [measurePack_eq_range_sum hF]
  exact sum_mul_pow_div_pow_mod (fun i _ => hd _) ht

/-! ## Sequence measures -/

/-- The finite measure placing mass `f t` at each `t < q`. -/
noncomputable def seqMeasure (q : ℕ) (f : ℕ → ℕ) : IntMeasure :=
  ∑ t ∈ Finset.range q, AddMonoidAlgebra.single ((t : ℕ) : ℤ) (f t)

theorem seqMeasure_apply {q t : ℕ} (f : ℕ → ℕ) (ht : t < q) :
    seqMeasure q f ((t : ℕ) : ℤ) = f t := by
  rw [seqMeasure, AddMonoidAlgebra.coeff_sum]
  refine (Finsupp.finsetSum_apply _ _ _).trans ?_
  have hcong : ∀ x ∈ Finset.range q,
      AddMonoidAlgebra.single ((x : ℕ) : ℤ) (f x) ((t : ℕ) : ℤ) =
        if x = t then f x else 0 := by
    intro x _
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    exact if_congr Int.natCast_inj rfl rfl
  rw [Finset.sum_congr rfl hcong, Finset.sum_ite_eq' (Finset.range q) t fun x => f x,
    ite_eq_left (Finset.mem_range.mpr ht)]

theorem measureWindow_seqMeasure (q : ℕ) (f : ℕ → ℕ) :
    MeasureWindow (seqMeasure q f) 0 ((q : ℤ) - 1) := by
  intro v hv
  rw [seqMeasure, AddMonoidAlgebra.coeff_sum] at hv
  have hex : ∃ t ∈ Finset.range q, AddMonoidAlgebra.single ((t : ℕ) : ℤ) (f t) v ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hv ((Finsupp.finsetSum_apply _ _ _).trans (Finset.sum_eq_zero hall))
  obtain ⟨t, htq, hne⟩ := hex
  have hvt : v = (t : ℤ) := by
    by_contra hne'
    exact hne (Finsupp.single_eq_of_ne fun h => hne' h)
  have htlt := Finset.mem_range.mp htq
  subst hvt
  omega

theorem totalMass_seqMeasure (q : ℕ) (f : ℕ → ℕ) :
    totalMass (seqMeasure q f) = ∑ t ∈ Finset.range q, f t := by
  rw [seqMeasure]
  refine (map_sum totalMassHom _ _).trans ?_
  exact Finset.sum_congr rfl fun t _ => totalMass_single _ _

theorem measurePack_seqMeasure (R q : ℕ) (f : ℕ → ℕ) :
    measurePack R 0 (seqMeasure q f) = ∑ t ∈ Finset.range q, f t * R ^ t := by
  rw [seqMeasure]
  refine (map_sum (measurePackHom R 0) _ _).trans ?_
  refine Finset.sum_congr rfl fun t _ => ?_
  refine (measurePack_single _ _ _ _).trans ?_
  rw [show ((t : ℤ) - 0).toNat = t by omega]

/-- Every mass of a sequence measure is bounded by any pointwise bound on the
sequence. -/
theorem seqMeasure_apply_le {q B : ℕ} {f : ℕ → ℕ} (hf : ∀ t < q, f t ≤ B) (v : ℤ) :
    seqMeasure q f v ≤ B := by
  by_cases hv : seqMeasure q f v = 0
  · rw [hv]
    exact Nat.zero_le B
  · have hw := measureWindow_seqMeasure q f v hv
    have hvt : v = ((v.toNat : ℕ) : ℤ) := by omega
    rw [hvt, seqMeasure_apply f (by omega)]
    exact hf _ (by omega)

end ToVCVio.Radix
