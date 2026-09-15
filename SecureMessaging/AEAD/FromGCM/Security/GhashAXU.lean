/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromGCM.Security.Axu
import SecureMessaging.AEAD.FromGCM.Security.Polynomial
import ToVCVio.CryptoFoundations.UniversalHash
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.List.GetD

/-!
# GHASH is almost-XOR-universal

`ghash_isAXU`: for two distinct inputs and any target `Δ`, a uniformly random GHASH key `H` makes
the two hashes XOR to `Δ` with probability at most `maxBlocks L / 2¹²⁸`. This is the
almost-XOR-universality (AXU) property the authenticity hop of the GCM proof consumes.

The argument: by `Polynomial.lean` the event says `H` is a root of the nonzero polynomial
`ghashPoly bp - ghashPoly bq - C Δ` of degree at most `maxBlocks L`, which has at most that
many roots in a field. Irreducibility of `nistPoly` makes the quotient a field and is used only
in `card_filter_le`; it is an explicit hypothesis here and is discharged in
`NistIrreducible.lean`.
-/

open OracleComp OracleSpec ENNReal ToVCVio Polynomial

namespace GCM

/-! ## Characteristic 2 in the quotient -/

theorem adjoinRoot_two_eq_zero : (2 : AdjoinRoot nistPoly) = 0 := by
  rw [← map_ofNat (AdjoinRoot.of nistPoly) 2, show (2 : ZMod 2) = 0 from rfl, map_zero]

theorem adjoinRoot_neg_eq_self (a : AdjoinRoot nistPoly) : -a = a := by
  linear_combination (-a) * adjoinRoot_two_eq_zero

/-! ## The coefficients of `ghashPoly` -/

/-- Holds for every `i`: out of range both sides are `0`. -/
theorem ghashPoly_coeff_succ (blocks : List (BitVec 128)) (i : ℕ) :
    (ghashPoly blocks).coeff (i + 1) = reflectN (blocks.reverse.getD i 0) := by
  rw [ghashPoly, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases hi : i < blocks.length
  · rw [Finset.sum_eq_single i]
    · rw [if_pos rfl]
    · intro j _ hj; exact if_neg (by omega)
    · intro h; exact absurd (Finset.mem_range.2 hi) h
  · have hz : blocks.reverse.getD i 0 = 0 :=
      List.getD_eq_default _ _ (by simpa using hi)
    rw [hz, reflectN_zero]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_range] at hj
    exact if_neg (by omega)

/-! ## The difference polynomial -/

/-- The polynomial whose roots are the keys `H` with `ghash H bp ^^^ ghash H bq = Δ`
(`eval_ghashDiffPoly`). The offset `Δ` is a constant term, so it adds no degree. -/
noncomputable def ghashDiffPoly (bp bq : List (BitVec 128)) (Δ : BitVec 128) :
    (AdjoinRoot nistPoly)[X] :=
  ghashPoly bp - ghashPoly bq - Polynomial.C (reflectN Δ)

theorem ghashDiffPoly_natDegree_le (bp bq : List (BitVec 128)) (Δ : BitVec 128) {n : ℕ}
    (hp : bp.length ≤ n) (hq : bq.length ≤ n) :
    (ghashDiffPoly bp bq Δ).natDegree ≤ n := by
  refine (Polynomial.natDegree_sub_le _ _).trans ?_
  simp only [Polynomial.natDegree_C, max_le_iff]
  refine ⟨(Polynomial.natDegree_sub_le _ _).trans ?_, Nat.zero_le _⟩
  exact max_le ((ghashPoly_natDegree_le bp).trans hp) ((ghashPoly_natDegree_le bq).trans hq)

/-- A differing block makes the difference polynomial nonzero: the coefficient of `X^(i+1)`
differs, and the constant offset cannot cancel a positive-degree coefficient. -/
theorem ghashDiffPoly_ne_zero (bp bq : List (BitVec 128)) (Δ : BitVec 128) {i : ℕ}
    (hne : bp.reverse.getD i 0 ≠ bq.reverse.getD i 0) :
    ghashDiffPoly bp bq Δ ≠ 0 := by
  intro h0
  have hc : (ghashDiffPoly bp bq Δ).coeff (i + 1) = 0 := by rw [h0]; simp
  rw [ghashDiffPoly] at hc
  simp only [Polynomial.coeff_sub, ghashPoly_coeff_succ, Polynomial.coeff_C,
    Nat.succ_ne_zero, if_false, sub_zero] at hc
  exact hne (reflectN.injective (sub_eq_zero.1 hc))

/-- `H` is a root of `ghashDiffPoly bp bq Δ` iff `ghash H bp ^^^ ghash H bq = Δ`. -/
theorem eval_ghashDiffPoly (H : BitVec 128) (bp bq : List (BitVec 128)) (Δ : BitVec 128) :
    (ghashDiffPoly bp bq Δ).eval (reflectN H)
      = reflectN (ghash H bp ^^^ ghash H bq) - reflectN Δ := by
  rw [ghashDiffPoly]
  simp only [Polynomial.eval_sub, Polynomial.eval_C, ← reflect_ghash_eval, reflectN_xor]
  rw [sub_eq_add_neg (reflectN (ghash H bp)), adjoinRoot_neg_eq_self]

/-- The exponent is written `(128 : ℕ)` so the statement matches the bound in `Security.lean`. -/
theorem card_bitVec128_enn : (Fintype.card (BitVec 128) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (128 : ℕ) := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]
  push_cast
  norm_num

/-! ### The root bound -/

-- Pins the import `Mathlib.Algebra.Field.ZMod`: without `Field (ZMod 2)`, the `Fact` below does
-- not yield `IsDomain (AdjoinRoot nistPoly)`.
example : Field (ZMod 2) := inferInstance

/-- At most `n` keys send two block lists of length `≤ n`, differing at some position, to a fixed
XOR offset. This is the only place irreducibility is used: it makes `AdjoinRoot nistPoly` a
field, so a nonzero polynomial has at most `natDegree` roots (false over a ring with zero
divisors). It is taken as an explicit argument rather than a `Fact` instance so it stays visible
in the signature. -/
theorem card_filter_le (hirr : Irreducible nistPoly) (bp bq : List (BitVec 128))
    (Δ : BitVec 128) {n : ℕ} (hp : bp.length ≤ n) (hq : bq.length ≤ n)
    {i : ℕ} (hne : bp.reverse.getD i 0 ≠ bq.reverse.getD i 0) :
    (Finset.univ.filter
      (fun H : BitVec 128 => ghash H bp ^^^ ghash H bq = Δ)).card ≤ n := by
  have : Fact (Irreducible nistPoly) := ⟨hirr⟩
  set P := ghashDiffPoly bp bq Δ with hP
  have hPne : P ≠ 0 := ghashDiffPoly_ne_zero bp bq Δ hne
  set S := Finset.univ.filter
    (fun H : BitVec 128 => ghash H bp ^^^ ghash H bq = Δ) with hS
  have hsub : (S.image reflectN).val ⊆ P.roots := by
    intro y hy
    simp only [Finset.mem_val, Finset.mem_image, hS, Finset.mem_filter,
      Finset.mem_univ, true_and] at hy
    obtain ⟨H, hH, rfl⟩ := hy
    rw [Polynomial.mem_roots hPne]
    -- `Polynomial.IsRoot` unfolds to the evaluation equation; `change` rather than `show`,
    -- which `linter.style.show` rejects when the goal is being rewritten.
    change P.eval (reflectN H) = 0
    rw [hP, eval_ghashDiffPoly, hH, sub_self]
  calc S.card = (S.image reflectN).card :=
        (Finset.card_image_of_injective _ reflectN.injective).symm
    _ ≤ P.natDegree := Polynomial.card_le_degree_of_subset_roots hsub
    _ ≤ n := ghashDiffPoly_natDegree_le bp bq Δ hp hq

/-! ### GHASH is almost-XOR-universal -/

/-- GHASH composed with GCM's input encoding is AXU at `ε = maxBlocks L / 2¹²⁸`. The encoding
matters: on raw block lists the property fails (`ghash h [0, X] = ghash h [X]`), and it is the
trailing length block of `gcmEncode` that separates distinct inputs. -/
theorem ghash_isAXU (L : ℕ) (hirr : Irreducible nistPoly) :
    GhashIsAXU L ((maxBlocks L : ℝ≥0∞) / 2 ^ (128 : ℕ)) := by
  have hb : GhashIsAXU L ((maxBlocks L : ℝ≥0∞) / Fintype.card (BitVec 128)) := by
    refine ToVCVio.isAlmostXorUniversal_of_card_le (d := maxBlocks L) ?_
    intro p q hpq Δ
    obtain ⟨i, hi⟩ := gcmEncode_tail_distinct hpq
    exact card_filter_le hirr _ _ Δ (gcmEncode_length_le p.1 p.2)
      (gcmEncode_length_le q.1 q.2) hi
  rwa [card_bitVec128_enn] at hb

end GCM
