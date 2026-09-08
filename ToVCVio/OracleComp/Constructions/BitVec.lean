/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.Constructions.SampleableType
import VCVio.EvalDist.BitVec
import VCVio.EvalDist.Prod

/-!
# Uniform `BitVec` block concatenation

Uniformity of truncated concatenation of uniform blocks — staging for upstream
VCVio (mirrors `VCVio/OracleComp/Constructions/BitVec.lean`, whose lemmas are
top-level): if each 128-bit block is uniform and independent, then the first `p`
bits of their concatenation are uniform on `BitVec p`.

The map `blocksToBitVec` reads bit `j` of the big-endian concatenation
`blocks[0] ‖ blocks[1] ‖ …` as bit `j % 128` of block `j / 128`, truncating to the
first `p` bits. The main results `evalDist_blocksToBitVec_uniform` and
`probOutput_blocksToBitVec_uniform` show that applying it to a uniform
`Vector (BitVec 128) n` yields the uniform distribution on `BitVec L` for any
`L ≤ 128 * n` (including the degenerate `L = 0`).
-/

open OracleSpec OracleComp ENNReal

/-- The cardinality of `Vector α n` over a `Fintype`, via the equivalence with
`Fin n → α`. Counterpart of Mathlib's `card_vector` for `List.Vector`. -/
lemma Fintype.card_vector (α : Type) [Fintype α] (n : ℕ) :
    Fintype.card (Vector α n) = Fintype.card α ^ n := by
  rw [Fintype.card_congr
    { toFun := fun (v : Vector α n) (i : Fin n) => v.get i
      invFun := Vector.ofFn
      left_inv := fun v => Vector.ext fun i hi => by simp [Vector.ofFn, Vector.get]
      right_inv := fun f => funext fun i => by simp [Vector.get, Vector.ofFn] }]
  simp

/-- The first `p` bits (big-endian) of the concatenation `blocks[0] ‖ blocks[1] ‖ …`
of 128-bit blocks: bit `j` of the result is bit `j % 128` of block `j / 128`.
Out-of-range reads return `false` (`List.getD` default block, `getMsbD` padding),
so `p` may exceed `128 * blocks.length`, in which case the result is zero-padded. -/
def blocksToBitVec (blocks : List (BitVec 128)) (p : ℕ) : BitVec p :=
  (BitVec.ofBoolListBE ((List.range p).map fun j =>
    (blocks.getD (j / 128) 0).getMsbD (j % 128))).cast (by simp)

/-- Bit-level characterization of `blocksToBitVec`: bit `j` (big-endian) of the
truncated concatenation is bit `j % 128` of block `j / 128`, for `j < p`. -/
lemma getMsbD_blocksToBitVec (blocks : List (BitVec 128)) {p j : ℕ} (hj : j < p) :
    (blocksToBitVec blocks p).getMsbD j = (blocks.getD (j / 128) 0).getMsbD (j % 128) := by
  simp [blocksToBitVec, List.getD_eq_getElem?_getD, hj]

/-- The window of `p` bits starting at position `s` (big-endian) of the concatenation
`blocks[0] ‖ blocks[1] ‖ …` of 128-bit blocks. `blocksToBitVec` is the `s = 0` window;
this generalization provides the complementary bits needed to see the pair
`(first L bits, remaining bits)` as a bijective image of the blocks. -/
def blocksToBitVecFrom (blocks : List (BitVec 128)) (s p : ℕ) : BitVec p :=
  (BitVec.ofBoolListBE ((List.range p).map fun j =>
    (blocks.getD ((s + j) / 128) 0).getMsbD ((s + j) % 128))).cast (by simp)

/-- Bit-level characterization of `blocksToBitVecFrom`: bit `j` (big-endian) of the
window starting at `s` is bit `(s + j) % 128` of block `(s + j) / 128`, for `j < p`. -/
lemma getMsbD_blocksToBitVecFrom (blocks : List (BitVec 128)) {s p j : ℕ} (hj : j < p) :
    (blocksToBitVecFrom blocks s p).getMsbD j =
      (blocks.getD ((s + j) / 128) 0).getMsbD ((s + j) % 128) := by
  simp [blocksToBitVecFrom, List.getD_eq_getElem?_getD, hj]
