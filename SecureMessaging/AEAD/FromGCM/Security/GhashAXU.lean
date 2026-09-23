/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromGCM.Security.Axu
import SecureMessaging.AEAD.FromGCM.Security.GhashPolynomial
import ToVCVio.CryptoFoundations.UniversalHash
import ToVCVio.OracleComp.Constructions.BitVec
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.List.GetD

/-!
# GHASH is almost-XOR-universal

`ghash_isAXU`: for two distinct inputs and any target `Δ`, a uniformly random GHASH key `H`
makes the two hashes XOR to `Δ` with probability at most `maxBlocks L / 2¹²⁸`. This is the
almost-XOR-universality (AXU) property the authenticity hop of the GCM proof consumes.

The argument: `Polynomial.lean` turns `ghash H` into evaluation of `ghashPoly` at `H`, so the
event says `H` is a root of `ghashDiffPoly bp bq Δ = ghashPoly bp - ghashPoly bq - C Δ`, a
nonzero polynomial of degree at most `maxBlocks L`, which has at most that many roots in a
field. Irreducibility of `nistPoly` makes the quotient a field and is used only in
`card_filter_le`; it is an explicit hypothesis here and is discharged in `NistIrreducible.lean`.
-/

open OracleComp OracleSpec ENNReal ToVCVio Polynomial

namespace GCM

/-! ## The coefficients of `ghashPoly` -/

/-- Coefficient `i + 1` of `ghashPoly` is reversed block `i`, with no range hypothesis on `i`:
past the block count both sides are `0`. -/
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

/-! ### The root bound -/

-- Pins the import `Mathlib.Algebra.Field.ZMod`: without `Field (ZMod 2)`, the `Fact` below does
-- not yield `IsDomain (AdjoinRoot nistPoly)`.
example : Field (ZMod 2) := inferInstance

/-- At most `n` keys send two block lists of length `≤ n`, differing at some reversed position,
to a fixed XOR offset. This is the only place irreducibility is used: it makes
`AdjoinRoot nistPoly` a field, where a nonzero polynomial has at most `natDegree` roots; over a
ring with zero divisors that bound fails. `hirr` is an explicit argument rather than a `Fact`
instance so that it stays visible in the signature. -/
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

/-- GHASH composed with GCM's input encoding is AXU at `ε = maxBlocks L / 2¹²⁸`. The encoding is
essential: `Axu.lean` shows AXU fails on raw block lists. `gcmEncode_tail_distinct` supplies the
differing reversed position `card_filter_le` needs: two distinct inputs differ either in AAD
length, which the trailing length block records, or in some content block at the same block
count. -/
theorem ghash_isAXU (L : ℕ) (hirr : Irreducible nistPoly) :
    GhashIsAXU L ((maxBlocks L : ℝ≥0∞) / 2 ^ (128 : ℕ)) := by
  have hb : GhashIsAXU L ((maxBlocks L : ℝ≥0∞) / Fintype.card (BitVec 128)) := by
    refine ToVCVio.isAlmostXorUniversal_of_card_le (d := maxBlocks L) ?_
    intro p q hpq Δ
    obtain ⟨i, hi⟩ := gcmEncode_tail_distinct hpq
    exact card_filter_le hirr _ _ Δ (gcmEncode_length_le p.1 p.2)
      (gcmEncode_length_le q.1 q.2) hi
  rwa [ToVCVio.natCast_card_bitVec] at hb

/-! ### The constant is nontrivial -/

theorem one_le_maxBlocks (L : ℕ) : 1 ≤ maxBlocks L := by
  unfold maxBlocks; omega

theorem maxBlocks_lt_two_pow (L : ℕ) (hL : ValidMsgLength L) : maxBlocks L < 2 ^ 128 := by
  have h := hL.1
  unfold maxBlocks
  rw [lenAMax_blocks]
  have : (L + 127) / 128 ≤ (2 ^ 39 - 256 + 127) / 128 := Nat.div_le_div_right (by omega)
  norm_num at this ⊢
  omega

/-- The concrete AXU constant sits between the blind-guess floor and `1`. The upper half needs
`ValidMsgLength L`, since `maxBlocks L` grows with `L`. A sanity check that the bound is not
vacuous; the main theorem does not use it. -/
theorem maxBlocks_div_nontrivial (L : ℕ) (hL : ValidMsgLength L) :
    ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹ ≤ (maxBlocks L : ℝ≥0∞) / 2 ^ (128 : ℕ) ∧
      (maxBlocks L : ℝ≥0∞) / 2 ^ (128 : ℕ) < 1 := by
  refine ⟨?_, ?_⟩
  · rw [← one_div]
    exact ENNReal.div_le_div_right (by exact_mod_cast one_le_maxBlocks L) _
  · rw [ENNReal.div_lt_iff (Or.inl (by positivity)) (Or.inl (by simp)), one_mul]
    exact_mod_cast maxBlocks_lt_two_pow L hL

end GCM
