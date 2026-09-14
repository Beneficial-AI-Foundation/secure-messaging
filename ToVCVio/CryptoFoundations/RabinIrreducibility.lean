/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Algebra.Ring.GeomSum

/-!
# Rabin's irreducibility test over a finite field

Rabin's test recognises irreducibility of a monic polynomial `f` of positive degree `n` over a
finite field `K` with `q = Fintype.card K` elements from two conditions:

1. `f ∣ X ^ (q ^ n) - X`, and
2. `IsCoprime f (X ^ (q ^ (n / p)) - X)` for every prime `p ∣ n`.

Mathlib supplies the hard half of the first condition, the forward implication
`Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X`. Missing is its converse,
`dvd_X_pow_card_pow_natDegree_sub_X` below, which follows from `FiniteField.pow_card` in the
finite field `AdjoinRoot g` together with the power basis of that extension. Everything else in
this file is bookkeeping around those two facts.

## Main Results

- `dvd_X_pow_card_pow_natDegree_sub_X`: an irreducible `g` divides `X ^ (q ^ g.natDegree) - X`,
  the converse Mathlib lacks.
- `dvd_X_pow_card_pow_sub_X_of_natDegree_dvd`: the same divisibility at any multiple of
  `g.natDegree`.
- `exists_prime_dvd_and_dvd_div`: a proper divisor `d` of `n` divides `n / p` for some prime
  `p ∣ n`.
- `isCoprime_of_isUnit_mk`: a unit in `AdjoinRoot f` read off as a Bézout certificate for
  coprimality.
- `irreducible_of_rabin`: Rabin's test in its classical divisibility/coprimality form.
- `irreducible_of_rabin_root`: Rabin's test with both conditions phrased inside `AdjoinRoot f`,
  the interface downstream callers consume.

## Upstream candidates

`dvd_X_pow_card_pow_natDegree_sub_X` and `dvd_X_pow_card_pow_sub_X_of_natDegree_dvd` are Mathlib
upstream candidates: they belong beside the forward direction in
`Mathlib/FieldTheory/Finite/Extension.lean`. They live here only until that upstreaming happens.

This module is cryptography-free: nothing here knows about any concrete polynomial, block cipher,
hash or bit-vector representation, and the whole import list is the two Mathlib modules above.
The intended application is certifying a fixed modulus (e.g. of degree `128` over `GF(2)`) where
both Rabin conditions are checked by kernel computation in `AdjoinRoot f`.
-/

open Polynomial

namespace ToVCVio

section Rabin
variable {K : Type*} [Field K] [Fintype K]

/-- The converse of `Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X`: an irreducible
polynomial `g` over a finite field `K` divides `X ^ (Fintype.card K) ^ g.natDegree - X`.

The content is `FiniteField.pow_card` applied to the image of `X` in the finite field
`AdjoinRoot g`, whose cardinality is `Fintype.card K ^ g.natDegree` by the power basis of the
extension. Together with the forward direction already in Mathlib this makes the first of
Rabin's two conditions an exact characterisation. -/
theorem dvd_X_pow_card_pow_natDegree_sub_X {g : K[X]} (hg : Irreducible g) :
    g ∣ X ^ (Fintype.card K) ^ g.natDegree - X := by
  haveI : Fact (Irreducible g) := ⟨hg⟩
  haveI : Module.Finite K (AdjoinRoot g) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hg.ne_zero).basis
  haveI : Fintype (AdjoinRoot g) := Module.fintypeOfFintype (AdjoinRoot.powerBasis hg.ne_zero).basis
  have hcard : Fintype.card (AdjoinRoot g) = Fintype.card K ^ g.natDegree := by
    rw [Module.card_eq_pow_finrank (K := K) (V := AdjoinRoot g),
      (AdjoinRoot.powerBasis hg.ne_zero).finrank]
    rfl
  rw [← AdjoinRoot.mk_eq_zero]
  have h := FiniteField.pow_card (AdjoinRoot.root g)
  rw [hcard] at h
  simp [AdjoinRoot.mk_X, h]

/-- Degree-divisibility upgrade of `dvd_X_pow_card_pow_natDegree_sub_X`: an irreducible `g`
divides `X ^ (Fintype.card K) ^ n - X` for every multiple `n` of `g.natDegree`.

The upgrade is one application of `dvd_pow_pow_sub_self_of_dvd`, so no geometric-sum argument
has to be repeated here. -/
theorem dvd_X_pow_card_pow_sub_X_of_natDegree_dvd {n : ℕ} {g : K[X]}
    (hg : Irreducible g) (h : g.natDegree ∣ n) :
    g ∣ X ^ (Fintype.card K) ^ n - X :=
  (dvd_X_pow_card_pow_natDegree_sub_X hg).trans (dvd_pow_pow_sub_self_of_dvd h)

/-- A proper divisor `d` of `n` divides `n / p` for some prime `p ∣ n`. (`hn` is unused by the
proof and kept for the interface.) -/
theorem exists_prime_dvd_and_dvd_div {d n : ℕ} (hn : 0 < n) (hdvd : d ∣ n) (hne : d ≠ n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ d ∣ n / p := by
  obtain ⟨c, rfl⟩ := hdvd
  have hc1 : c ≠ 1 := by rintro rfl; simp at hne
  obtain ⟨p, hp, hpc⟩ := Nat.exists_prime_and_dvd hc1
  refine ⟨p, hp, hpc.mul_left d, ?_⟩
  obtain ⟨e, rfl⟩ := hpc
  exact ⟨e, by rw [← mul_assoc, mul_comm d p, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]⟩

/-- A unit modulo `f` is coprime to `f`: an inverse `b` of `a` in `AdjoinRoot f` is a Bézout
certificate `a * b - 1 = f * c`. This lets coprimality be certified by one multiplication against
a precomputed inverse. -/
theorem isCoprime_of_isUnit_mk {R : Type*} [CommRing R] {f a : R[X]}
    (h : IsUnit (AdjoinRoot.mk f a)) : IsCoprime f a := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨b, hb⟩ := AdjoinRoot.mk_surjective (g := f) (↑u⁻¹ : AdjoinRoot f)
  have hz : AdjoinRoot.mk f (a * b - 1) = 0 := by
    rw [map_sub, map_mul, hb, map_one, ← hu]; simp
  obtain ⟨c, hc⟩ := AdjoinRoot.mk_eq_zero.1 hz
  exact ⟨-c, b, by linear_combination hc⟩

/-- Rabin's irreducibility test in its classical divisibility/coprimality form: a monic `f` of
positive degree `n` over a finite field `K` with `q` elements is irreducible as soon as
`f ∣ X ^ (q ^ n) - X` and `f` is coprime to `X ^ (q ^ (n / p)) - X` for every prime `p ∣ n`.

The proof takes an irreducible factor `g` of `f`. Mathlib's forward direction bounds its degree
to a divisor of `n`; the coprimality conditions rule out every proper divisor, so `g` has degree
`n` and the cofactor is a unit. -/
theorem irreducible_of_rabin {f : K[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (h1 : f ∣ X ^ (Fintype.card K) ^ f.natDegree - X)
    (h2 : ∀ p : ℕ, p.Prime → p ∣ f.natDegree →
      IsCoprime f (X ^ (Fintype.card K) ^ (f.natDegree / p) - X)) :
    Irreducible f := by
  have hf0 : f ≠ 0 := hf.ne_zero
  have hfu : ¬ IsUnit f := fun h => by
    simp [Polynomial.natDegree_eq_zero_of_isUnit h] at hdeg
  obtain ⟨g, hg, hgf⟩ := WfDvdMonoid.exists_irreducible_factor hfu hf0
  have hgn : g.natDegree ∣ f.natDegree := by
    refine _root_.Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hg ?_
    rw [Nat.card_eq_fintype_card]
    exact hgf.trans h1
  have hgeq : g.natDegree = f.natDegree := by
    by_contra hne
    obtain ⟨p, hp, hpn, hdiv⟩ := exists_prime_dvd_and_dvd_div hdeg hgn hne
    exact hg.not_isUnit ((h2 p hp hpn).isUnit_of_dvd' hgf
      (dvd_X_pow_card_pow_sub_X_of_natDegree_dvd hg hdiv))
  obtain ⟨c, rfl⟩ := hgf
  have hc0 : c ≠ 0 := fun h => by simp [h] at hf0
  have hcdeg : c.natDegree = 0 := by
    have := Polynomial.natDegree_mul hg.ne_zero hc0
    omega
  refine (associated_mul_unit_right g c
    (Polynomial.isUnit_iff.2 ⟨c.coeff 0, ?_, ?_⟩)).irreducible hg
  · rw [Polynomial.eq_C_of_natDegree_eq_zero hcdeg] at hc0
    exact isUnit_iff_ne_zero.2 (by simpa using hc0)
  · exact (Polynomial.eq_C_of_natDegree_eq_zero hcdeg).symm

/-- Rabin's irreducibility test, quotient-ring interface: the form callers consume. Both
conditions are stated about the image of `X` inside `AdjoinRoot f`, namely the Frobenius
fixed-point equation at exponent `Fintype.card K ^ f.natDegree` and, for every prime
`p ∣ f.natDegree`, the unit condition at exponent `Fintype.card K ^ (f.natDegree / p)`.

Phrasing both hypotheses in `AdjoinRoot f` is mandatory, not stylistic. At a concrete base field
such as `ZMod 2` an equivalent statement written with polynomial subtraction elaborates with its
`Semiring` instance coming through `ZMod.commRing` while its `Sub` comes through the
`ZMod.instField` path; closing such a goal by `exact` then diverges, first hitting the recursion
limit and eventually overflowing the stack after several seconds and gigabytes of memory. Raising
the recursion limit makes the behaviour worse, so no downstream statement should be restated in
the polynomial-subtraction shape.

The two exponents differ by design: the first is `Fintype.card K ^ f.natDegree`, the second
`Fintype.card K ^ (f.natDegree / p)`. Callers apply this positionally, so the binders are a
fixed interface. -/
theorem irreducible_of_rabin_root {f : K[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (h1 : (AdjoinRoot.root f) ^ (Fintype.card K ^ f.natDegree) = AdjoinRoot.root f)
    (h2 : ∀ p : ℕ, p.Prime → p ∣ f.natDegree →
      IsUnit ((AdjoinRoot.root f) ^ (Fintype.card K ^ (f.natDegree / p)) - AdjoinRoot.root f)) :
    Irreducible f := by
  refine irreducible_of_rabin hf hdeg ?_ (fun p hp hpn => ?_)
  · rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X, h1, sub_self]
  · refine isCoprime_of_isUnit_mk ?_
    rw [map_sub, map_pow, AdjoinRoot.mk_X]
    exact h2 p hp hpn

end Rabin

end ToVCVio
