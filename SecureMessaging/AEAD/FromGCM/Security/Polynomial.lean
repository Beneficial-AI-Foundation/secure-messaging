/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import SecureMessaging.AEAD.GCM
import ToVCVio.CryptoFoundations.AdjoinRootReflect

/-!
# The NIST GHASH polynomial and its ring-level facts

GCM's field multiplication `gfmul` (NIST SP 800-38D §6.3) is multiplication in the
quotient ring `𝔽₂[x] / (x¹²⁸ + x⁷ + x² + x + 1)`. This file fixes that polynomial —
`nistPoly : (ZMod 2)[X]` — and records the three purely algebraic facts the rest of
Phase 7a builds on:

- `nistPoly_monic` : `nistPoly` is monic;
- `nistPoly_natDegree` : `nistPoly.natDegree = 128`, so `BitVec 128` matches the rank of
  `AdjoinRoot nistPoly` as a free `ZMod 2`-module;
- `nistPoly_root_pow` : in `AdjoinRoot nistPoly`, `root¹²⁸ = root⁷ + root² + root + 1`.

Everything here comes from `AdjoinRoot`'s **unconditional** `CommRing` instance and the
`Monic` fact — *no irreducibility* (`Fact (Irreducible _)`, `Field`, `IsDomain`,
`GaloisField`) is used or needed. That is exactly Phase 7a criterion 1's "ring structure
suffices": the reduction identity `nistPoly_root_pow` is the algebraic content of the
`⊕ gcmReductionConst` step in `gfmul` (`R = 0xE1 <<< 120` reads as `x¹²⁸ mod nistPoly`),
consumed by plan 07a-03's `reflect_gfmulStep`.

## References

- [NIST_GCM] Dworkin. *NIST SP 800-38D*, 2007. https://csrc.nist.gov/pubs/sp/800/38/d/final
-/

namespace GCM

open Polynomial

/-- The NIST GHASH reduction polynomial `x¹²⁸ + x⁷ + x² + x + 1` over `𝔽₂ = ZMod 2`
(NIST SP 800-38D §6.3). The low-degree tail `x⁷ + x² + x + 1` is grouped explicitly so
`Polynomial.monic_X_pow_add` applies with that tail as its `p`.

`AdjoinRoot nistPoly` is the ring in which `gfmul` multiplies; it is a `CommRing`
unconditionally (no irreducibility), and monic here suffices for its power basis. -/
noncomputable def nistPoly : (ZMod 2)[X] := X ^ 128 + (X ^ 7 + X ^ 2 + X + 1)

/-- `nistPoly` is monic: its leading term is `x¹²⁸` because the tail
`x⁷ + x² + x + 1` has degree `7 < 128`. Proven via `monic_X_pow_add`; no irreducibility. -/
theorem nistPoly_monic : nistPoly.Monic := by
  unfold nistPoly
  apply monic_X_pow_add
  compute_degree!

/-- `nistPoly.natDegree = 128`. Stated as an equality (not a `≤` bound): the reflected
`BitVec 128 ≃ AdjoinRoot nistPoly` equivalence's dimension depends on it. -/
theorem nistPoly_natDegree : nistPoly.natDegree = 128 := by
  unfold nistPoly
  compute_degree!

set_option maxRecDepth 4000 in
/-- The reduction identity: in `AdjoinRoot nistPoly` the adjoined root satisfies
`root¹²⁸ = root⁷ + root² + root + 1`.

This is the algebraic content of the `⊕ gcmReductionConst` step in `gfmul`: the constant
`R = 0xE1 <<< 120` reads (MSB = coefficient of `x⁰`) as `x⁷ + x² + x + 1 = x¹²⁸ mod nistPoly`,
so shifting a `x¹²⁷` coefficient up to `x¹²⁸` and XORing `R` is exactly this substitution.
Plan 07a-03's `reflect_gfmulStep` rewrites with this lemma at the reduction bit.

Proof is `CommRing`-only: `AdjoinRoot.mk_self` gives `root¹²⁸ + (root⁷+root²+root+1) = 0`,
and `(2 : AdjoinRoot nistPoly) = 0` (from the `ZMod 2` base, `AdjoinRoot.of`) turns the sign
flip into the stated equality. No irreducibility / `Field` / `IsDomain`. -/
theorem nistPoly_root_pow :
    (AdjoinRoot.root nistPoly) ^ 128
      = (AdjoinRoot.root nistPoly) ^ 7 + (AdjoinRoot.root nistPoly) ^ 2
        + (AdjoinRoot.root nistPoly) + 1 := by
  -- `root` annihilates `nistPoly`: `mk nistPoly nistPoly = 0`. Keep the modulus written as
  -- `nistPoly` (only the reduced element is spelled out) so `mk_X` yields `root nistPoly`.
  have h : (AdjoinRoot.mk nistPoly) (X ^ 128 + (X ^ 7 + X ^ 2 + X + 1)) = 0 :=
    AdjoinRoot.mk_self
  simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X] at h
  -- char 2: `(2 : AdjoinRoot nistPoly) = 0` via `of (2 : ZMod 2) = of 0`.
  have h2 : (2 : AdjoinRoot nistPoly) = 0 := by
    rw [← map_ofNat (AdjoinRoot.of nistPoly) 2, show (2 : ZMod 2) = 0 from rfl, map_zero]
  linear_combination h
    - (AdjoinRoot.root nistPoly ^ 7 + AdjoinRoot.root nistPoly ^ 2
        + AdjoinRoot.root nistPoly + 1) * h2

/-! ## The reflected equivalence at `nistPoly`

`AdjoinRootReflect.reflect` is the general reflected bijection
`BitVec p.natDegree ≃ AdjoinRoot p` for a monic `p`. Here we instantiate it at `nistPoly`,
rewriting the domain `BitVec nistPoly.natDegree` to the concrete `BitVec 128` (via
`nistPoly_natDegree`) so `gfmul`/`gcmReductionConst` — all `BitVec 128` — feed in directly.
The characterization lemma `reflectN_apply` expresses `reflectN` as the coordinate sum over
`Fin 128`, so every downstream proof reads bits off `getMsbD` and never fights the transport. -/

open AdjoinRootReflect

set_option maxRecDepth 4000

/-- The GCM instantiation of the general reflected equivalence: `BitVec 128 ≃ AdjoinRoot nistPoly`.
The `BitVec.cast` on both sides bridges the `nistPoly.natDegree = 128` gap, keeping the exposed
type the concrete `BitVec 128`. NIST bit index `i` (`getMsbD i`) maps to the coefficient of
`root nistPoly ^ i`. Monic-only (via `nistPoly_monic`); no irreducibility. -/
noncomputable def reflectN : BitVec 128 ≃ AdjoinRoot nistPoly where
  toFun x := reflect nistPoly_monic (x.cast nistPoly_natDegree.symm)
  invFun y := ((reflect nistPoly_monic).symm y).cast nistPoly_natDegree
  left_inv x := by simp only [Equiv.symm_apply_apply, BitVec.cast_cast, BitVec.cast_eq]
  right_inv y := by simp only [BitVec.cast_cast, BitVec.cast_eq, Equiv.apply_symm_apply]

/-- Coordinate = coefficient for `reflectN`, phrased over `Fin 128` with `getMsbD` on the concrete
`BitVec 128` (the general `reflect_apply` is over `Fin nistPoly.natDegree`; here the transport is
discharged once and for all). This is the primitive every downstream lemma reads bits off of. -/
theorem reflectN_apply (x : BitVec 128) :
    reflectN x
      = ∑ i : Fin 128, boolToZMod2 (x.getMsbD (i : ℕ)) • AdjoinRoot.root nistPoly ^ (i : ℕ) := by
  change reflect nistPoly_monic (x.cast nistPoly_natDegree.symm) = _
  rw [reflect_apply]
  refine Fintype.sum_equiv (finCongr nistPoly_natDegree) _ _ (fun i => ?_)
  simp [BitVec.getMsbD_cast]

/-- XOR additivity of `reflectN` (the `BitVec 128` specialization of `reflect_xor`), obtained by
distributing `BitVec.cast` over `^^^`. -/
theorem reflectN_xor (x y : BitVec 128) :
    reflectN (x ^^^ y) = reflectN x + reflectN y := by
  change reflect nistPoly_monic ((x ^^^ y).cast nistPoly_natDegree.symm)
     = reflect nistPoly_monic (x.cast nistPoly_natDegree.symm)
     + reflect nistPoly_monic (y.cast nistPoly_natDegree.symm)
  rw [← BitVec.xor_cast, reflect_xor]

/-- The reflected reading of the GCM reduction constant `R = 0xE1 <<< 120`. Its set MSB bits are
`getMsbD 0, 1, 2, 7` (the top byte `0b1110_0001`), so reflected (MSB ↔ `x⁰`) it is
`root⁷ + root² + root + 1` — i.e. exactly `root¹²⁸` in the quotient (`nistPoly_root_pow`). This is
the value the `⊕ R` branch of `gfmul` contributes when the reduction bit fires. -/
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

/-! ## The single-step multiplicativity crux

One iteration of `gfmul`'s `v`-update multiplies `reflectN` by `root`. The `v`-update
`vStep` right-shifts (moving coefficient `xʲ ↦ xʲ⁺¹`, dropping the old `x¹²⁷`) and, when the
reduction bit `getLsbD 0 = getMsbD 127` fires, XORs in `R`. Reflected, the right shift is
`· root` minus the escaped `x¹²⁷` coefficient's `root¹²⁸` term; the `⊕ R` restores exactly that
`root¹²⁸` (via `reflect_gcmReductionConst` + `nistPoly_root_pow`), and in char 2 the two copies
cancel — so both branches equal `reflectN v * root`. -/

/-- The reduction bit: the arithmetic LSB is the coefficient of `x¹²⁷` in reflected coordinates. -/
theorem getLsbD0_eq_getMsbD127 (v : BitVec 128) : v.getLsbD 0 = v.getMsbD 127 := by
  rw [BitVec.getLsbD_eq_getMsbD]; simp

/-- `reflectN v * root` in coordinate form: reindex `xⁱ ↦ xⁱ⁺¹` and peel the `i = 127` top term
into `root¹²⁸`. Kept a top-level lemma (not an inline `have`) so it elaborates within its own
heartbeat budget — the repo convention for these coordinate manipulations. -/
private theorem reflectN_mul_root_left (v : BitVec 128) :
    reflectN v * AdjoinRoot.root nistPoly
      = (∑ i : Fin 127, boolToZMod2 (v.getMsbD (i : ℕ)) • AdjoinRoot.root nistPoly ^ ((i : ℕ) + 1))
        + boolToZMod2 (v.getMsbD 127) • AdjoinRoot.root nistPoly ^ 128 := by
  rw [reflectN_apply, Finset.sum_mul]
  simp only [smul_mul_assoc, ← pow_succ]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]

/-- `reflectN (v ≫ 1)` in coordinate form: the same reindex as `· root`, but the old `x¹²⁷`
coefficient shifts off the top (index `0` produces nothing), so only `∑_{i<127} vᵢ • root^(i+1)`
survives. Top-level for the heartbeat budget. -/
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

/-- The right-shift `v ≫ 1` reflects to `reflectN v * root` up to the escaped top coefficient's
`root¹²⁸` term. Both sides collapse to `∑_{i<127} vᵢ • root^(i+1)` plus `v₁₂₇ • root¹²⁸`:
multiplying by `root` reindexes `xⁱ ↦ xⁱ⁺¹` and peels the `i = 127` top term (which becomes
`root¹²⁸`); the shift does the same reindex but drops that top coefficient (it shifts off the
end). -/
theorem reflectN_mul_root (v : BitVec 128) :
    reflectN v * AdjoinRoot.root nistPoly
      = reflectN (v >>> 1)
        + boolToZMod2 (v.getMsbD 127) • AdjoinRoot.root nistPoly ^ 128 := by
  rw [reflectN_mul_root_left, reflectN_ushiftRight_eq]

/-- The `v`-update performed by one iteration of `gfmul`'s 128-step fold (NIST SP 800-38D §6.3):
right-shift and conditionally reduce by `R = gcmReductionConst`. This is exactly the second
component of the `foldl` body in `GCM.gfmul`. -/
def vStep (v : BitVec 128) : BitVec 128 :=
  if v.getLsbD 0 then (v >>> 1) ^^^ gcmReductionConst else v >>> 1

/-- **The phase's crux single-step lemma.** One `vStep` corresponds to multiplication by `root`
in `AdjoinRoot nistPoly`: `reflectN (vStep v) = reflectN v * root`. Proven from `reflectN_mul_root`
(the shift is `· root` up to the escaped `root¹²⁸` term), `reflect_gcmReductionConst`, and
`nistPoly_root_pow` — `CommRing`-only, no irreducibility. Plan 07a-04's fold invariant lifts this
across `gfmul`'s `List.range 128` fold to close full multiplicativity. -/
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

/-! ## The `gfmul` fold invariant (criterion 1)

`gfmul x y` runs a 128-step `List.range 128 |>.foldl` accumulating a pair `(z, v)`. Lifting the
single-step lemma `reflect_gfmulStep` across the whole fold shows `gfmul` is multiplication in
`AdjoinRoot nistPoly` transported through `reflectN` — the identity
`reflectN (gfmul x y) = reflectN x * reflectN y`. The proof is a loop invariant peeled with
`List.range_succ` + `List.foldl_append`, using ring structure only (no irreducibility). -/

/-- One iteration of `gfmul`'s 128-step fold body (NIST SP 800-38D §6.3, Algorithm 1), named so the
invariant can peel it: `z ↦ z ⊕ v` when the multiplier bit `xᵢ` is set, and `v ↦ vStep v`. This is
definitionally the `foldl` body of `GCM.gfmul` (its second component is exactly `vStep p.2`). -/
def gfmulStep (x : BitVec 128) (p : BitVec 128 × BitVec 128) (i : ℕ) :
    BitVec 128 × BitVec 128 :=
  (if x.getMsbD i then p.1 ^^^ p.2 else p.1, vStep p.2)

/-- `reflectN` sends the XOR-identity `0` to the ring `0` (the additive identity is preserved). Used
for the fold invariant's base case. Proven from `reflectN_xor` and self-cancellation, so it needs no
`getMsbD`-of-zero fact. -/
theorem reflectN_zero : reflectN (0 : BitVec 128) = 0 := by
  rw [reflectN_apply]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have hb : (0 : BitVec 128).getMsbD (i : ℕ) = false := by simp
  rw [hb, boolToZMod2]
  simp

/-- `gfmul` written as the `gfmulStep` fold — definitional, since `gfmulStep x` is the exact body of
`gfmul`'s `List.range 128 |>.foldl` (`vStep` unfolds to the literal `v`-update). Lets the
invariant at `k = 128` specialize directly onto `gfmul`. -/
theorem gfmul_eq_foldl (x y : BitVec 128) :
    gfmul x y = ((List.range 128).foldl (gfmulStep x) (0, y)).1 := rfl

/-- **The fold invariant.** After the first `k` steps of `gfmul x y`, the `v`-accumulator is
`reflectN y * root^k` and the `z`-accumulator is `(∑_{i<k} xᵢ • root^i) * reflectN y`. Both
halves are proven simultaneously by peeling the last step with `List.range_succ` /
`List.foldl_append`: the
`v`-half advances by one `reflect_gfmulStep` (`· root`); the `z`-half either extends the coefficient
sum by the `i = k` term (bit set, via `reflectN_xor` and `Finset.sum_range_succ`) or leaves it
unchanged (bit clear, the new coefficient being `0`). Holds unconditionally — no `k ≤ 128` bound is
needed, since the single-step lemma is bit-index agnostic. -/
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

end GCM
