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

end GCM
