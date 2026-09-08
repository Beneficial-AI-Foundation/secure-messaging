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

/-- Split the concatenation of `n` 128-bit blocks at position `L`: the pair of the
first `L` bits and the remaining `128 * n - L` bits. Bijective when `L ≤ 128 * n`
(`blocksSplit_bijective`), which makes `blocksToBitVec · L` the first coordinate of
a bijective image of the blocks — the key to `probOutput_blocksToBitVec_uniform`. -/
def blocksSplit (n L : ℕ) (v : Vector (BitVec 128) n) :
    BitVec L × BitVec (128 * n - L) :=
  (blocksToBitVec v.toList L, blocksToBitVecFrom v.toList L (128 * n - L))

lemma blocksSplit_injective (n L : ℕ) (hL : L ≤ 128 * n) :
    Function.Injective (blocksSplit n L) := by
  intro v w h
  rw [blocksSplit, blocksSplit, Prod.ext_iff] at h
  obtain ⟨h1, h2⟩ := h
  -- The two components together determine every bit of the concatenation.
  have hbit : ∀ j, j < 128 * n →
      (v.toList.getD (j / 128) 0).getMsbD (j % 128) =
        (w.toList.getD (j / 128) 0).getMsbD (j % 128) := by
    intro j hj
    rcases lt_or_ge j L with hjL | hjL
    · simpa [getMsbD_blocksToBitVec _ hjL] using congrArg (·.getMsbD j) h1
    · have hj' : j - L < 128 * n - L := by omega
      have hbit' := congrArg (·.getMsbD (j - L)) h2
      simp only [getMsbD_blocksToBitVecFrom _ hj'] at hbit'
      rwa [Nat.add_sub_cancel' hjL] at hbit'
  -- Hence the blocks agree bit by bit.
  refine Vector.ext fun i hi => ?_
  refine BitVec.eq_of_getMsbD_eq fun b hb => ?_
  have hj := hbit (128 * i + b) (by omega)
  have hdiv : (128 * i + b) / 128 = i := by omega
  have hmod : (128 * i + b) % 128 = b := by omega
  rw [hdiv, hmod] at hj
  simpa [List.getD_eq_getElem?_getD, hi] using hj

lemma blocksSplit_bijective (n L : ℕ) (hL : L ≤ 128 * n) :
    Function.Bijective (blocksSplit n L) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨blocksSplit_injective n L hL, ?_⟩
  rw [Fintype.card_vector, card_bitVec, ← pow_mul, Fintype.card_prod,
    card_bitVec, card_bitVec, ← pow_add]
  exact congrArg (2 ^ ·) (by omega)

/-- **Truncated concatenation of uniform blocks is uniform** (distribution form):
mapping a uniform `Vector (BitVec 128) n` through `blocksToBitVec · L` yields the
uniform distribution on `BitVec L`, for any `L ≤ 128 * n`. -/
theorem evalDist_blocksToBitVec_uniform (n L : ℕ) (hL : L ≤ 128 * n) :
    𝒟[(fun v : Vector (BitVec 128) n => blocksToBitVec v.toList L) <$>
        ($ᵗ Vector (BitVec 128) n)] = 𝒟[$ᵗ BitVec L] :=
  calc 𝒟[(fun v : Vector (BitVec 128) n => blocksToBitVec v.toList L) <$>
        ($ᵗ Vector (BitVec 128) n)]
      = 𝒟[Prod.fst <$> (blocksSplit n L <$> ($ᵗ Vector (BitVec 128) n))] := by
        rw [Functor.map_map]; rfl
    _ = 𝒟[Prod.fst <$> ($ᵗ (BitVec L × BitVec (128 * n - L)))] :=
        evalDist_map_eq_of_evalDist_eq
          (evalDist_map_bijective_uniform_cross (α := Vector (BitVec 128) n)
            (blocksSplit n L) (blocksSplit_bijective n L hL)) Prod.fst
    _ = 𝒟[$ᵗ BitVec L] := evalDist_map_fst_uniformSample_prod

/-- **Truncated concatenation of uniform blocks is uniform**: every `y : BitVec L`
is hit with probability `(Fintype.card (BitVec L))⁻¹` when `n` independent uniform
128-bit blocks are concatenated and truncated to `L ≤ 128 * n` bits. -/
theorem probOutput_blocksToBitVec_uniform (n L : ℕ) (hL : L ≤ 128 * n) (y : BitVec L) :
    Pr[= y | (fun v : Vector (BitVec 128) n => blocksToBitVec v.toList L) <$>
        ($ᵗ Vector (BitVec 128) n)] = (Fintype.card (BitVec L) : ℝ≥0∞)⁻¹ := by
  rw [evalDist_ext_iff.mp (evalDist_blocksToBitVec_uniform n L hL) y,
    probOutput_uniformSample]

/-- The degenerate case `L = 0`: `BitVec 0` is a singleton, so the truncated
concatenation hits its unique value with probability `1`. The main theorem covers
this case rather than excluding it. -/
example (n : ℕ) (y : BitVec 0) :
    Pr[= y | (fun v : Vector (BitVec 128) n => blocksToBitVec v.toList 0) <$>
        ($ᵗ Vector (BitVec 128) n)] = 1 := by
  simpa using probOutput_blocksToBitVec_uniform n 0 (Nat.zero_le _) y
