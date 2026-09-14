/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Algebra.Ring.GeomSum

/-!
# Rabin's irreducibility test over a finite field

Rabin's test characterises irreducibility of a polynomial `f` of positive degree `n` over a
finite field `K` with `q = Nat.card K` elements by two conditions:

1. `f ∣ X ^ (q ^ n) - X`, and
2. `IsCoprime f (X ^ (q ^ (n / p)) - X)` for every prime `p ∣ n`.

The degree-theoretic input is `natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X`: an irreducible `g`
divides `X ^ (q ^ m) - X` exactly when `g.natDegree ∣ m`. Everything else in this file is
bookkeeping around that fact.

## Main Results

- `natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X`: the degree/divisibility characterisation for an
  irreducible `g`. Mathlib at this toolchain (v4.32.0) has only the forward direction,
  `Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X`; the converse is proved here.
- `exists_prime_dvd_and_dvd_div`: a proper divisor `d` of `n` divides `n / p` for some prime
  `p ∣ n`.
- `isCoprime_of_isUnit_mk`: a unit in `AdjoinRoot f` read off as a Bézout certificate for
  coprimality.
- `irreducible_of_rabin`: Rabin's test in its classical divisibility/coprimality form.
- `irreducible_iff_rabin`: the same, as a characterisation.
- `irreducible_of_rabin_root`: Rabin's test with both conditions phrased inside `AdjoinRoot f`,
  the interface downstream callers consume.

## Upstream status

`natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X` is already in Mathlib master as
`Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X` (Mathlib PR #39239, 2026-07-28, first
released in v4.33.0), with the same statement. Delete the local copy at the next toolchain bump
and replace `natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X hg` by
`hg.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X`.

Mathlib has no Rabin test. `irreducible_iff_rabin` and its supporting lemmas are stated with
`Nat.card` and `Finite`, matching `Mathlib/FieldTheory/Finite/Extension.lean`, so that they can
move there as they stand.

This module is cryptography-free: nothing here knows about any concrete polynomial, block cipher,
hash or bit-vector representation, and the whole import list is the two Mathlib modules above.
The intended application is certifying a fixed modulus (e.g. of degree `128` over `GF(2)`) where
both Rabin conditions are checked by kernel computation in `AdjoinRoot f`.
-/

open Polynomial

namespace ToVCVio

section Rabin
variable {K : Type*} [Field K] [Finite K]

/-- An irreducible `g` over a finite field `K` divides `X ^ (Nat.card K) ^ n - X` exactly when
`g.natDegree ∣ n`.

The forward direction is Mathlib's `Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X`. The
converse is `FiniteField.pow_card` applied to the image of `X` in the finite field `AdjoinRoot g`,
whose cardinality is `Nat.card K ^ g.natDegree` by the power basis of the extension, followed by
`dvd_pow_pow_sub_self_of_dvd` to pass from `g.natDegree` to any multiple of it.

Superseded by `Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X` (Mathlib PR #39239) from
Mathlib v4.33.0 on; see the module docstring. -/
theorem natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X {g : K[X]} (hg : Irreducible g) {n : ℕ} :
    g.natDegree ∣ n ↔ g ∣ X ^ (Nat.card K) ^ n - X := by
  refine ⟨fun hdvd => dvd_trans ?_ (dvd_pow_pow_sub_self_of_dvd hdvd),
    hg.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X⟩
  have := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
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

/-- Rabin's irreducibility test in its classical divisibility/coprimality form: `f` of positive
degree `n` over a finite field `K` with `q` elements is irreducible as soon as
`f ∣ X ^ (q ^ n) - X` and `f` is coprime to `X ^ (q ^ (n / p)) - X` for every prime `p ∣ n`.

The proof takes an irreducible factor `g` of `f`. `natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X`
bounds its degree to a divisor of `n`; the coprimality conditions rule out every proper divisor,
so `g` has degree `n` and the cofactor is a unit. -/
theorem irreducible_of_rabin {f : K[X]} (hdeg : 0 < f.natDegree)
    (h1 : f ∣ X ^ (Nat.card K) ^ f.natDegree - X)
    (h2 : ∀ p : ℕ, p.Prime → p ∣ f.natDegree →
      IsCoprime f (X ^ (Nat.card K) ^ (f.natDegree / p) - X)) :
    Irreducible f := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hdeg
  have hfu : ¬ IsUnit f := fun h => by
    simp [Polynomial.natDegree_eq_zero_of_isUnit h] at hdeg
  obtain ⟨g, hg, hgf⟩ := WfDvdMonoid.exists_irreducible_factor hfu hf0
  have hgn : g.natDegree ∣ f.natDegree :=
    (natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X hg).2 (hgf.trans h1)
  have hgeq : g.natDegree = f.natDegree := by
    by_contra hne
    obtain ⟨p, hp, hpn, hdiv⟩ := exists_prime_dvd_and_dvd_div hdeg hgn hne
    exact hg.not_isUnit ((h2 p hp hpn).isUnit_of_dvd' hgf
      ((natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X hg).1 hdiv))
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

/-- Rabin's criterion: a polynomial of positive degree `n` over a finite field with `q` elements
is irreducible if and only if it divides `X ^ (q ^ n) - X` and is coprime to
`X ^ (q ^ (n / p)) - X` for every prime `p ∣ n`.

The forward direction is `natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X` twice: `f` divides
`X ^ (q ^ n) - X` because `n ∣ n`, and does not divide `X ^ (q ^ (n / p)) - X` because
`n ∤ n / p` for `0 < n / p < n`, which for an irreducible `f` is coprimality
(`Irreducible.coprime_iff_not_dvd`). The reverse direction is `irreducible_of_rabin`. -/
theorem irreducible_iff_rabin {f : K[X]} (hdeg : 0 < f.natDegree) :
    Irreducible f ↔
      f ∣ X ^ (Nat.card K) ^ f.natDegree - X ∧
      ∀ p : ℕ, p.Prime → p ∣ f.natDegree →
        IsCoprime f (X ^ (Nat.card K) ^ (f.natDegree / p) - X) := by
  refine ⟨fun hi => ⟨(natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X hi).1 dvd_rfl,
    fun p hp hpn => hi.coprime_iff_not_dvd.2 fun h => ?_⟩,
    fun h => irreducible_of_rabin hdeg h.1 h.2⟩
  have hle := Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd hdeg hpn) hp.pos)
    ((natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X hi).2 h)
  have hlt := Nat.div_lt_self hdeg hp.one_lt
  omega

/-- Rabin's test with both conditions stated about `root f` in `AdjoinRoot f`: the root is fixed
by the `n`-fold Frobenius, and `root ^ (q ^ (n / p)) - root` is a unit for every prime `p ∣ n`.
Keep this shape: at `ZMod 2` the polynomial-subtraction form of the same hypotheses makes
elaboration diverge through mismatched `Semiring`/`Sub` instance paths. -/
theorem irreducible_of_rabin_root {f : K[X]} (hdeg : 0 < f.natDegree)
    (h1 : (AdjoinRoot.root f) ^ (Nat.card K ^ f.natDegree) = AdjoinRoot.root f)
    (h2 : ∀ p : ℕ, p.Prime → p ∣ f.natDegree →
      IsUnit ((AdjoinRoot.root f) ^ (Nat.card K ^ (f.natDegree / p)) - AdjoinRoot.root f)) :
    Irreducible f := by
  refine irreducible_of_rabin hdeg ?_ (fun p hp hpn => ?_)
  · rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X, h1, sub_self]
  · refine isCoprime_of_isUnit_mk ?_
    rw [map_sub, map_pow, AdjoinRoot.mk_X]
    exact h2 p hp hpn

end Rabin

end ToVCVio
