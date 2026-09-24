/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import Mathlib.FieldTheory.Finite.Extension

/-!
# Rabin's irreducibility test over a finite field

A polynomial `f` of positive degree `n` over a finite field with `q` elements is irreducible iff

1. `f ∣ X^(qⁿ) − X`, and
2. `f` is coprime to `X^(q^(n/p)) − X` for every prime `p ∣ n`.

This is Rabin's test (M. O. Rabin, *Probabilistic algorithms in finite fields*, SIAM J. Comput.
9(2), 1980). The only finite-field input is Mathlib's
`Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X`. `irreducible_of_rabin_root` restates
both conditions inside `AdjoinRoot f`, where they can be checked by kernel computation for a
concrete `f`.
-/

open Polynomial

namespace ToVCVio

section Rabin
variable {K : Type*} [Field K] [Finite K]

/-- A proper divisor `d` of `n` divides `n / p` for some prime `p ∣ n`. -/
theorem exists_prime_dvd_and_dvd_div {d n : ℕ} (hdvd : d ∣ n) (hne : d ≠ n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ d ∣ n / p := by
  obtain ⟨c, rfl⟩ := hdvd
  have hc1 : c ≠ 1 := by rintro rfl; simp at hne
  obtain ⟨p, hp, hpc⟩ := Nat.exists_prime_and_dvd hc1
  refine ⟨p, hp, hpc.mul_left d, ?_⟩
  obtain ⟨e, rfl⟩ := hpc
  exact ⟨e, by rw [← mul_assoc, mul_comm d p, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]⟩

/-- If `a` is a unit modulo `f`, then `f` and `a` are coprime. -/
theorem isCoprime_of_isUnit_mk {R : Type*} [CommRing R] {f a : R[X]}
    (h : IsUnit (AdjoinRoot.mk f a)) : IsCoprime f a := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨b, hb⟩ := AdjoinRoot.mk_surjective (g := f) (↑u⁻¹ : AdjoinRoot f)
  have hz : AdjoinRoot.mk f (a * b - 1) = 0 := by
    rw [map_sub, map_mul, hb, map_one, ← hu]; simp
  obtain ⟨c, hc⟩ := AdjoinRoot.mk_eq_zero.1 hz
  exact ⟨-c, b, by linear_combination hc⟩

/-- Rabin's test, sufficiency. Let `f` have degree `n > 0` over a finite field with `q`
elements. If `f ∣ X^(qⁿ) − X` and `f` is coprime to `X^(q^(n/p)) − X` for every prime
`p ∣ n`, then `f` is irreducible. -/
theorem irreducible_of_rabin {f : K[X]} (hdeg : 0 < f.natDegree)
    (h1 : f ∣ X ^ (Nat.card K) ^ f.natDegree - X)
    (h2 : ∀ p : ℕ, p.Prime → p ∣ f.natDegree →
      IsCoprime f (X ^ (Nat.card K) ^ (f.natDegree / p) - X)) :
    Irreducible f := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hdeg
  obtain ⟨g, hg, hgf⟩ := Polynomial.exists_irreducible_of_natDegree_pos hdeg
  have hgn : g.natDegree ∣ f.natDegree :=
    hg.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.2 (hgf.trans h1)
  have hgeq : g.natDegree = f.natDegree := by
    by_contra hne
    obtain ⟨p, hp, hpn, hdiv⟩ := exists_prime_dvd_and_dvd_div hgn hne
    exact hg.not_isUnit ((h2 p hp hpn).isUnit_of_dvd' hgf
      (hg.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.1 hdiv))
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

/-- Rabin's test. A polynomial `f` of degree `n > 0` over a finite field with `q` elements is
irreducible iff `f ∣ X^(qⁿ) − X` and `f` is coprime to `X^(q^(n/p)) − X` for every prime
`p ∣ n`. -/
theorem irreducible_iff_rabin {f : K[X]} (hdeg : 0 < f.natDegree) :
    Irreducible f ↔
      f ∣ X ^ (Nat.card K) ^ f.natDegree - X ∧
      ∀ p : ℕ, p.Prime → p ∣ f.natDegree →
        IsCoprime f (X ^ (Nat.card K) ^ (f.natDegree / p) - X) := by
  refine ⟨fun hi => ⟨hi.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.1 dvd_rfl,
    fun p hp hpn => hi.coprime_iff_not_dvd.2 fun h => ?_⟩,
    fun h => irreducible_of_rabin hdeg h.1 h.2⟩
  have hle := Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd hdeg hpn) hp.pos)
    (hi.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.2 h)
  have hlt := Nat.div_lt_self hdeg hp.one_lt
  omega

/-- Rabin's test in `AdjoinRoot f`, sufficiency. Let `f` have degree `n > 0` over a finite field
with `q` elements, and let `α = root f`. If `α^(qⁿ) = α` and `α^(q^(n/p)) − α` is a unit for
every prime `p ∣ n`, then `f` is irreducible.

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
