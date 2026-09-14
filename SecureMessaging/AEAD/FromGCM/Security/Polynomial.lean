/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.ZMod.Basic
import SecureMessaging.AEAD.GCM
import ToVCVio.CryptoFoundations.AdjoinRootReflect

/-!
# GHASH as polynomial evaluation

GCM's bit-level block multiplication `gfmul` (NIST SP 800-38D §6.3) is multiplication in the
quotient ring `𝔽₂[x] / (x¹²⁸ + x⁷ + x² + x + 1)`, and GHASH, GCM's hash of a block list, is a
Horner evaluation in that ring. This file fixes the modulus `nistPoly`, transports bit vectors
into `AdjoinRoot nistPoly` via `reflectN`, and proves:

- `reflect_gfmul`: `gfmul` is ring multiplication;
- `reflect_ghash_eval`: `ghash h blocks` is the polynomial `ghashPoly blocks` evaluated at `h`.

Nothing here needs `nistPoly` to be irreducible; `AdjoinRoot`'s `CommRing` structure suffices.

## References

- [NIST_GCM] Dworkin. *NIST SP 800-38D*, 2007. https://csrc.nist.gov/pubs/sp/800/38/d/final
-/

namespace GCM

open Polynomial

/-- GCM's field polynomial `x¹²⁸ + x⁷ + x² + x + 1` over `𝔽₂` (NIST SP 800-38D §6.3). -/
noncomputable def nistPoly : (ZMod 2)[X] := X ^ 128 + (X ^ 7 + X ^ 2 + X + 1)

theorem nistPoly_monic : nistPoly.Monic := by
  unfold nistPoly
  apply monic_X_pow_add
  compute_degree!

theorem nistPoly_natDegree : nistPoly.natDegree = 128 := by
  unfold nistPoly
  compute_degree!

/-- `x¹²⁸ = x⁷ + x² + x + 1` in the quotient (characteristic 2 absorbs the sign). This is what the
`⊕ gcmReductionConst` step of `gfmul` implements. -/
theorem nistPoly_root_pow :
    (AdjoinRoot.root nistPoly) ^ 128
      = (AdjoinRoot.root nistPoly) ^ 7 + (AdjoinRoot.root nistPoly) ^ 2
        + (AdjoinRoot.root nistPoly) + 1 := by
  -- `root` annihilates `nistPoly`. Keep the modulus written as `nistPoly` (only the reduced
  -- element is spelled out) so `mk_X` yields `root nistPoly`.
  have h : (AdjoinRoot.mk nistPoly) (X ^ 128 + (X ^ 7 + X ^ 2 + X + 1)) = 0 :=
    AdjoinRoot.mk_self
  simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X] at h
  -- char 2: `(2 : AdjoinRoot nistPoly) = 0` via `of (2 : ZMod 2) = of 0`.
  have h2 : (2 : AdjoinRoot nistPoly) = 0 := by
    rw [← map_ofNat (AdjoinRoot.of nistPoly) 2, show (2 : ZMod 2) = 0 from rfl, map_zero]
  linear_combination h
    - (AdjoinRoot.root nistPoly ^ 7 + AdjoinRoot.root nistPoly ^ 2
        + AdjoinRoot.root nistPoly + 1) * h2

/-! ## The reflected equivalence at `nistPoly` -/

open ToVCVio.AdjoinRootReflect

/-- `ToVCVio.AdjoinRootReflect.reflect` at `nistPoly`, with the domain stated as the concrete
`BitVec 128`: bit `i` (most-significant first) is the coefficient of `root nistPoly ^ i`. -/
noncomputable def reflectN : BitVec 128 ≃ AdjoinRoot nistPoly where
  toFun x := reflect nistPoly_monic (x.cast nistPoly_natDegree.symm)
  invFun y := ((reflect nistPoly_monic).symm y).cast nistPoly_natDegree
  left_inv x := by simp only [Equiv.symm_apply_apply, BitVec.cast_cast, BitVec.cast_eq]
  right_inv y := by simp only [BitVec.cast_cast, BitVec.cast_eq, Equiv.apply_symm_apply]

theorem reflectN_apply (x : BitVec 128) :
    reflectN x
      = ∑ i : Fin 128, boolToZMod2 (x.getMsbD (i : ℕ)) • AdjoinRoot.root nistPoly ^ (i : ℕ) := by
  change reflect nistPoly_monic (x.cast nistPoly_natDegree.symm) = _
  rw [reflect_apply]
  refine Fintype.sum_equiv (finCongr nistPoly_natDegree) _ _ (fun i => ?_)
  simp [BitVec.getMsbD_cast]

theorem reflectN_xor (x y : BitVec 128) :
    reflectN (x ^^^ y) = reflectN x + reflectN y := by
  change reflect nistPoly_monic ((x ^^^ y).cast nistPoly_natDegree.symm)
     = reflect nistPoly_monic (x.cast nistPoly_natDegree.symm)
     + reflect nistPoly_monic (y.cast nistPoly_natDegree.symm)
  rw [← BitVec.xor_cast, reflect_xor]

/-- The reduction constant `R = 0xE1 <<< 120` has bits `0, 1, 2, 7` set, so it reads as
`x⁷ + x² + x + 1`, i.e. `x¹²⁸` in the quotient. -/
theorem reflect_gcmReductionConst :
    reflectN gcmReductionConst
      = AdjoinRoot.root nistPoly ^ 7 + AdjoinRoot.root nistPoly ^ 2
        + AdjoinRoot.root nistPoly + 1 := by
  have hsub : Finset.range 8 ⊆ Finset.range 128 := by
    intro x hx; rw [Finset.mem_range] at hx ⊢; omega
  have hvanish : ∀ x ∈ Finset.range 128, x ∉ Finset.range 8 →
      boolToZMod2 (gcmReductionConst.getMsbD x) • AdjoinRoot.root nistPoly ^ x = 0 := by
    intro x hx hx8
    rw [Finset.mem_range] at hx hx8
    have hb : gcmReductionConst.getMsbD x = false := by
      unfold gcmReductionConst
      rw [BitVec.getMsbD_shiftLeft, BitVec.getMsbD_eq_getLsbD]
      have : ¬ (x + 120 < 128) := by omega
      simp [this]
    rw [hb]
    simp [boolToZMod2]
  rw [reflectN_apply,
      Fin.sum_univ_eq_sum_range
        (fun j => boolToZMod2 (gcmReductionConst.getMsbD j) • AdjoinRoot.root nistPoly ^ j) 128,
      ← Finset.sum_subset hsub hvanish]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, gcmReductionConst,
    BitVec.getMsbD_shiftLeft]
  rw [show (0xE1 : BitVec 128).getMsbD 120 = true from by decide,
      show (0xE1 : BitVec 128).getMsbD 121 = true from by decide,
      show (0xE1 : BitVec 128).getMsbD 122 = true from by decide,
      show (0xE1 : BitVec 128).getMsbD 123 = false from by decide,
      show (0xE1 : BitVec 128).getMsbD 124 = false from by decide,
      show (0xE1 : BitVec 128).getMsbD 125 = false from by decide,
      show (0xE1 : BitVec 128).getMsbD 126 = false from by decide,
      show (0xE1 : BitVec 128).getMsbD 127 = true from by decide]
  have bt : boolToZMod2 true = (1 : ZMod 2) := by decide
  have bf : boolToZMod2 false = (0 : ZMod 2) := by decide
  simp only [bt, bf, one_smul, zero_smul, add_zero, zero_add, pow_zero, pow_one]
  ring

/-! ## One `gfmul` step multiplies by `root`

The `v`-update of `gfmul` right-shifts (coefficient `xʲ ↦ xʲ⁺¹`, dropping `x¹²⁷`) and, when the
dropped bit was set, XORs in `R`, which by `reflect_gcmReductionConst` and `nistPoly_root_pow`
restores exactly the lost `x¹²⁸` term. -/

theorem getLsbD0_eq_getMsbD127 (v : BitVec 128) : v.getLsbD 0 = v.getMsbD 127 := by
  rw [BitVec.getLsbD_eq_getMsbD]; simp

private theorem reflectN_mul_root_left (v : BitVec 128) :
    reflectN v * AdjoinRoot.root nistPoly
      = (∑ i : Fin 127, boolToZMod2 (v.getMsbD (i : ℕ)) • AdjoinRoot.root nistPoly ^ ((i : ℕ) + 1))
        + boolToZMod2 (v.getMsbD 127) • AdjoinRoot.root nistPoly ^ 128 := by
  rw [reflectN_apply, Finset.sum_mul]
  simp only [smul_mul_assoc, ← pow_succ]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]

private theorem reflectN_ushiftRight_eq (v : BitVec 128) :
    reflectN (v >>> 1)
      = ∑ i : Fin 127,
          boolToZMod2 (v.getMsbD (i : ℕ)) • AdjoinRoot.root nistPoly ^ ((i : ℕ) + 1) := by
  rw [reflectN_apply, Fin.sum_univ_succ]
  have hz : boolToZMod2 ((v >>> 1).getMsbD 0) • AdjoinRoot.root nistPoly ^ (0 : ℕ) = 0 := by
    simp [BitVec.getMsbD_ushiftRight, boolToZMod2]
  rw [Fin.val_zero, hz, zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := i.isLt
  rw [Fin.val_succ, BitVec.getMsbD_ushiftRight]
  have ha : (i : ℕ) + 1 < 128 := by omega
  have hb : ¬ ((i : ℕ) + 1 < 1) := by omega
  simp [ha, hb]

/-- Right shift is multiplication by `root`, up to the `x¹²⁸` term of the dropped top bit. -/
theorem reflectN_mul_root (v : BitVec 128) :
    reflectN v * AdjoinRoot.root nistPoly
      = reflectN (v >>> 1)
        + boolToZMod2 (v.getMsbD 127) • AdjoinRoot.root nistPoly ^ 128 := by
  rw [reflectN_mul_root_left, reflectN_ushiftRight_eq]

/-- The `v`-update of one `gfmul` iteration: the second component of the `foldl` body of
`GCM.gfmul`. -/
def vStep (v : BitVec 128) : BitVec 128 :=
  if v.getLsbD 0 then (v >>> 1) ^^^ gcmReductionConst else v >>> 1

theorem reflect_gfmulStep (v : BitVec 128) :
    reflectN (vStep v) = reflectN v * AdjoinRoot.root nistPoly := by
  have bt : boolToZMod2 true = (1 : ZMod 2) := by decide
  have bf : boolToZMod2 false = (0 : ZMod 2) := by decide
  have hcond : v.getLsbD 0 = v.getMsbD 127 := getLsbD0_eq_getMsbD127 v
  have key := reflectN_mul_root v
  unfold vStep
  by_cases h : v.getMsbD 127 = true
  · have hif : v.getLsbD 0 = true := by rw [hcond]; exact h
    rw [if_pos hif, reflectN_xor, key, reflect_gcmReductionConst, ← nistPoly_root_pow, h, bt,
      one_smul]
  · have hif : ¬ (v.getLsbD 0 = true) := by rw [hcond]; exact h
    have h127 : v.getMsbD 127 = false := by simpa using h
    rw [if_neg hif, key, h127, bf, zero_smul, add_zero]

/-! ## The `gfmul` fold invariant -/

/-- The `foldl` body of `GCM.gfmul`, named so the loop invariant can peel one iteration. -/
def gfmulStep (x : BitVec 128) (p : BitVec 128 × BitVec 128) (i : ℕ) :
    BitVec 128 × BitVec 128 :=
  (if x.getMsbD i then p.1 ^^^ p.2 else p.1, vStep p.2)

theorem reflectN_zero : reflectN (0 : BitVec 128) = 0 := by
  rw [reflectN_apply]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have hb : (0 : BitVec 128).getMsbD (i : ℕ) = false := by simp
  rw [hb, boolToZMod2]
  simp

theorem gfmul_eq_foldl (x y : BitVec 128) :
    gfmul x y = ((List.range 128).foldl (gfmulStep x) (0, y)).1 := rfl

/-- Loop invariant after `k` steps of `gfmul x y`: `v = y · rootᵏ` and
`z = (∑_{i<k} xᵢ · rootⁱ) · y`, in `AdjoinRoot nistPoly`. -/
theorem reflect_gfmul_aux (x y : BitVec 128) (k : ℕ) :
    reflectN ((List.range k).foldl (gfmulStep x) (0, y)).2
        = reflectN y * AdjoinRoot.root nistPoly ^ k ∧
    reflectN ((List.range k).foldl (gfmulStep x) (0, y)).1
        = (∑ i ∈ Finset.range k,
            boolToZMod2 (x.getMsbD i) • AdjoinRoot.root nistPoly ^ i) * reflectN y := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [List.range_zero, List.foldl_nil]
      change reflectN y = reflectN y * AdjoinRoot.root nistPoly ^ 0
      rw [pow_zero, mul_one]
    · rw [List.range_zero, List.foldl_nil]
      change reflectN (0 : BitVec 128)
          = (∑ i ∈ Finset.range 0, boolToZMod2 (x.getMsbD i) • AdjoinRoot.root nistPoly ^ i)
            * reflectN y
      rw [reflectN_zero, Finset.sum_range_zero, zero_mul]
  | succ k ih =>
    obtain ⟨ihv, ihz⟩ := ih
    have bt : boolToZMod2 true = (1 : ZMod 2) := by decide
    have bf : boolToZMod2 false = (0 : ZMod 2) := by decide
    rw [List.range_succ, List.foldl_append]
    set p := (List.range k).foldl (gfmulStep x) (0, y) with hp
    simp only [List.foldl_cons, List.foldl_nil]
    refine ⟨?_, ?_⟩
    · change reflectN (vStep p.2) = reflectN y * AdjoinRoot.root nistPoly ^ (k + 1)
      rw [reflect_gfmulStep, ihv, pow_succ]
      ring
    · change reflectN (if x.getMsbD k then p.1 ^^^ p.2 else p.1)
          = (∑ i ∈ Finset.range (k + 1),
              boolToZMod2 (x.getMsbD i) • AdjoinRoot.root nistPoly ^ i) * reflectN y
      rw [Finset.sum_range_succ, add_mul]
      by_cases h : x.getMsbD k = true
      · rw [if_pos h, reflectN_xor, ihz, ihv, h, bt, one_smul]
        ring
      · rw [if_neg h]
        rw [Bool.not_eq_true] at h
        rw [ihz, h, bf, zero_smul, zero_mul, add_zero]

/-- `gfmul` is multiplication in `AdjoinRoot nistPoly`. -/
theorem reflect_gfmul (x y : BitVec 128) :
    reflectN (gfmul x y) = reflectN x * reflectN y := by
  have hx : (∑ i ∈ Finset.range 128,
      boolToZMod2 (x.getMsbD i) • AdjoinRoot.root nistPoly ^ i) = reflectN x := by
    rw [reflectN_apply]
    exact (Fin.sum_univ_eq_sum_range
      (fun i => boolToZMod2 (x.getMsbD i) • AdjoinRoot.root nistPoly ^ i) 128).symm
  rw [gfmul_eq_foldl, (reflect_gfmul_aux x y 128).2, hx]

/-! ## `ghash` as polynomial evaluation

`ghash h blocks = blocks.foldl (fun y x => gfmul (y ⊕ x) h) 0` (NIST SP 800-38D §6.4) is a
Horner evaluation in `AdjoinRoot nistPoly`: `ghash h [X₁, …, Xₘ] = X₁·hᵐ + ⋯ + Xₘ·h`. -/

theorem reflect_ghash_foldl_gen (h : BitVec 128) (blocks : List (BitVec 128)) (y : BitVec 128) :
    reflectN (blocks.foldl (fun y x => gfmul (y ^^^ x) h) y)
      = blocks.foldl (fun (acc : AdjoinRoot nistPoly) (x : BitVec 128) =>
          (acc + reflectN x) * reflectN h) (reflectN y) := by
  induction blocks generalizing y with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons]
    rw [ih (gfmul (y ^^^ b) h), reflect_gfmul, reflectN_xor]

theorem reflect_ghash_foldl (h : BitVec 128) (blocks : List (BitVec 128)) :
    reflectN (blocks.foldl (fun y x => gfmul (y ^^^ x) h) 0)
      = blocks.foldl (fun (acc : AdjoinRoot nistPoly) (x : BitVec 128) =>
          (acc + reflectN x) * reflectN h) 0 := by
  have := reflect_ghash_foldl_gen h blocks 0
  rwa [reflectN_zero] at this

/-- The Horner fold unrolled: the last block pairs with `H¹`, the first with `Hᵐ`. -/
theorem horner_foldl_eq_sum (H : AdjoinRoot nistPoly) (blocks : List (BitVec 128)) :
    blocks.foldl (fun (acc : AdjoinRoot nistPoly) (x : BitVec 128) => (acc + reflectN x) * H) 0
      = ∑ i ∈ Finset.range blocks.length,
          reflectN (blocks.reverse.getD i 0) * H ^ (i + 1) := by
  induction blocks using List.reverseRecOn with
  | nil => simp
  | append_singleton l b ih =>
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, ih, List.length_append, List.length_cons,
      List.length_nil, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append]
    rw [Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, zero_add, pow_one]
    rw [add_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, ← pow_succ]

/-- `ghash h [X₁, …, Xₘ] = X₁·hᵐ + ⋯ + Xₘ·h` in `AdjoinRoot nistPoly`, indexed by the reversed
block list so that `blocks.reverse[i]` carries `h^(i+1)`. -/
theorem reflect_ghash (h : BitVec 128) (blocks : List (BitVec 128)) :
    reflectN (ghash h blocks)
      = ∑ i ∈ Finset.range blocks.length,
          reflectN (blocks.reverse.getD i 0) * (reflectN h) ^ (i + 1) := by
  unfold ghash
  rw [reflect_ghash_foldl, horner_foldl_eq_sum]

/-! ## Polynomial packaging -/

/-- The polynomial `X₁·Xᵐ + ⋯ + Xₘ·X` whose value at `h` is `ghash h [X₁, …, Xₘ]`. Its constant
term is zero and its degree is at most the block count. -/
noncomputable def ghashPoly (blocks : List (BitVec 128)) : (AdjoinRoot nistPoly)[X] :=
  ∑ i ∈ Finset.range blocks.length,
    Polynomial.C (reflectN (blocks.reverse.getD i 0)) * Polynomial.X ^ (i + 1)

/-- GHASH is evaluation of `ghashPoly` at the key. -/
theorem reflect_ghash_eval (h : BitVec 128) (blocks : List (BitVec 128)) :
    reflectN (ghash h blocks) = (ghashPoly blocks).eval (reflectN h) := by
  rw [reflect_ghash, ghashPoly, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]

theorem ghashPoly_coeff_zero (blocks : List (BitVec 128)) :
    (ghashPoly blocks).coeff 0 = 0 := by
  rw [ghashPoly, Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  simp

theorem ghashPoly_natDegree_le (blocks : List (BitVec 128)) :
    (ghashPoly blocks).natDegree ≤ blocks.length := by
  rw [ghashPoly]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  rw [Finset.mem_range] at hi
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_X_pow_le _).trans ?_
  omega

end GCM
