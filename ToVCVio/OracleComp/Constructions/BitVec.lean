/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.Constructions.SampleableType
import VCVio.EvalDist.BitVec
import VCVio.EvalDist.Prod
import VCVio.EvalDist.List
import ToVCVio.OracleComp.Constructions.SampleableType
import Mathlib.Data.LawfulXor.Equiv

/-!
# Uniform `BitVec` block concatenation

Uniformity facts about bit vectors built from uniform draws, candidates for
`VCVio/OracleComp/Constructions/BitVec.lean` upstream.

* `natCast_card_bitVec`: `|BitVec w| = 2 ^ w` in any semiring, for whichever `Fintype` instance
  the goal carries.
* `evalDist_blocksToBitVec_uniform`: the first `L ≤ w * n` bits of `n` independent uniform
  `w`-bit blocks are uniform on `BitVec L`.
* `evalDist_pair_xor_uniform`: a value masked by a uniform `BitVec n`, paired with any
  function of it masked by an independent uniform `BitVec m`, is uniform on the product.
* `evalDist_mapM_const_uniform`: a list of independent uniform draws is one uniform vector.
-/

open OracleSpec OracleComp ENNReal

/-- Mathlib's `card_vector` for `Vector` rather than `List.Vector`. -/
lemma Fintype.card_vector (α : Type) [Fintype α] (n : ℕ) :
    Fintype.card (Vector α n) = Fintype.card α ^ n := by
  rw [Fintype.card_congr (arrayVectorEquivFin α n)]; simp

namespace ToVCVio

/-- `|BitVec w| = 2 ^ w`, cast into any semiring. The `Fintype` instance is left to unification
so the lemma applies whatever instance a generic sampling lemma leaves behind. -/
lemma natCast_card_bitVec {R : Type*} [Semiring R] (w : ℕ) [Fintype (BitVec w)] :
    (Fintype.card (BitVec w) : R) = 2 ^ w := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]
  push_cast
  rfl

variable {w : ℕ}

/-- The first `p` bits, most significant first, of the concatenation `blocks[0] ‖ blocks[1] ‖ …`,
zero-padded if `p` exceeds `w * blocks.length`. -/
def blocksToBitVec (blocks : List (BitVec w)) (p : ℕ) : BitVec p :=
  (BitVec.ofBoolListBE ((List.range p).map fun j =>
    (blocks.getD (j / w) 0).getMsbD (j % w))).cast (by simp)

lemma getMsbD_blocksToBitVec (blocks : List (BitVec w)) {p j : ℕ} (hj : j < p) :
    (blocksToBitVec blocks p).getMsbD j = (blocks.getD (j / w) 0).getMsbD (j % w) := by
  simp [blocksToBitVec, List.getD_eq_getElem?_getD, hj]

/-- The `p` bits starting at bit `s`, most significant first, of the concatenation
`blocks[0] ‖ blocks[1] ‖ …`; `blocksToBitVec` is the case `s = 0`. -/
def blocksToBitVecFrom (blocks : List (BitVec w)) (s p : ℕ) : BitVec p :=
  (BitVec.ofBoolListBE ((List.range p).map fun j =>
    (blocks.getD ((s + j) / w) 0).getMsbD ((s + j) % w))).cast (by simp)

lemma getMsbD_blocksToBitVecFrom (blocks : List (BitVec w)) {s p j : ℕ} (hj : j < p) :
    (blocksToBitVecFrom blocks s p).getMsbD j =
      (blocks.getD ((s + j) / w) 0).getMsbD ((s + j) % w) := by
  simp [blocksToBitVecFrom, List.getD_eq_getElem?_getD, hj]

/-- `blocksSplit n L v` cuts the concatenation of the `n` `w`-bit blocks of `v` at bit `L`,
returning the first `L` bits and the remaining `w * n - L`. It is a bijection when `L ≤ w * n`
(`blocksSplit_bijective`). -/
def blocksSplit (n L : ℕ) (v : Vector (BitVec w) n) :
    BitVec L × BitVec (w * n - L) :=
  (blocksToBitVec v.toList L, blocksToBitVecFrom v.toList L (w * n - L))

lemma blocksSplit_injective (n L : ℕ) (hL : L ≤ w * n) :
    Function.Injective (blocksSplit (w := w) n L) := by
  intro v v' h
  rw [blocksSplit, blocksSplit, Prod.ext_iff] at h
  obtain ⟨h1, h2⟩ := h
  -- The two components together determine every bit of the concatenation.
  have hbit : ∀ j, j < w * n →
      (v.toList.getD (j / w) 0).getMsbD (j % w) =
        (v'.toList.getD (j / w) 0).getMsbD (j % w) := by
    intro j hj
    rcases lt_or_ge j L with hjL | hjL
    · simpa [getMsbD_blocksToBitVec _ hjL] using congrArg (·.getMsbD j) h1
    · have hj' : j - L < w * n - L := by omega
      have hbit' := congrArg (·.getMsbD (j - L)) h2
      simp only [getMsbD_blocksToBitVecFrom _ hj'] at hbit'
      rwa [Nat.add_sub_cancel' hjL] at hbit'
  -- Hence the blocks agree bit by bit.
  refine Vector.ext fun i hi => ?_
  refine BitVec.eq_of_getMsbD_eq fun b hb => ?_
  have hlt : w * i + b < w * n := by
    have h1 := Nat.mul_le_mul_left w hi
    rw [Nat.mul_succ] at h1
    exact lt_of_lt_of_le (Nat.add_lt_add_left hb _) h1
  have hj := hbit (w * i + b) hlt
  have hdiv : (w * i + b) / w = i := by
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hb, Nat.add_zero]
  have hmod : (w * i + b) % w = b := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  rw [hdiv, hmod] at hj
  simpa [List.getD_eq_getElem?_getD, hi] using hj

lemma blocksSplit_bijective (n L : ℕ) (hL : L ≤ w * n) :
    Function.Bijective (blocksSplit (w := w) n L) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨blocksSplit_injective n L hL, ?_⟩
  rw [Fintype.card_vector, card_bitVec, ← pow_mul, Fintype.card_prod,
    card_bitVec, card_bitVec, ← pow_add]
  exact congrArg (2 ^ ·) (Nat.add_sub_cancel' hL).symm

/-- The first `L ≤ w * n` bits of `n` independent uniform `w`-bit blocks are uniform. -/
theorem evalDist_blocksToBitVec_uniform (n L : ℕ) (hL : L ≤ w * n) :
    𝒟[(fun v : Vector (BitVec w) n => blocksToBitVec v.toList L) <$>
        ($ᵗ Vector (BitVec w) n)] = 𝒟[$ᵗ BitVec L] :=
  calc 𝒟[(fun v : Vector (BitVec w) n => blocksToBitVec v.toList L) <$>
        ($ᵗ Vector (BitVec w) n)]
      = 𝒟[Prod.fst <$> (blocksSplit n L <$> ($ᵗ Vector (BitVec w) n))] := by
        rw [Functor.map_map]; rfl
    _ = 𝒟[Prod.fst <$> ($ᵗ (BitVec L × BitVec (w * n - L)))] :=
        evalDist_map_eq_of_evalDist_eq
          (evalDist_map_bijective_uniform_cross (α := Vector (BitVec w) n)
            (blocksSplit n L) (blocksSplit_bijective n L hL)) Prod.fst
    _ = 𝒟[$ᵗ BitVec L] := evalDist_map_fst_uniformSample_prod

/-- Pointwise form of `evalDist_blocksToBitVec_uniform`. -/
theorem probOutput_blocksToBitVec_uniform (n L : ℕ) (hL : L ≤ w * n) (y : BitVec L) :
    Pr[= y | (fun v : Vector (BitVec w) n => blocksToBitVec v.toList L) <$>
        ($ᵗ Vector (BitVec w) n)] = (Fintype.card (BitVec L) : ℝ≥0∞)⁻¹ := by
  rw [evalDist_ext_iff.mp (evalDist_blocksToBitVec_uniform n L hL) y,
    probOutput_uniformSample]

/-- Sanity check at `L = 0`: `BitVec 0` is a singleton, hit with probability `1`. -/
example (n : ℕ) (y : BitVec 0) :
    Pr[= y | (fun v : Vector (BitVec w) n => blocksToBitVec v.toList 0) <$>
        ($ᵗ Vector (BitVec w) n)] = 1 := by
  simpa using probOutput_blocksToBitVec_uniform n 0 (Nat.zero_le _) y

/-! ## A masked value and a masked function of it are jointly uniform -/

/-- One-time pad: for fixed `x` and uniform `y`, `x ⊕ y` is uniform, also when passed to an
arbitrary continuation. -/
private lemma evalDist_bind_xor_left_uniform {k : ℕ} {γ : Type} (x : BitVec k)
    (cont : BitVec k → ProbComp γ) :
    𝒟[($ᵗ BitVec k : ProbComp (BitVec k)) >>= fun y => cont (x ^^^ y)] =
      𝒟[($ᵗ BitVec k : ProbComp (BitVec k)) >>= cont] :=
  evalDist_ext fun z =>
    probOutput_bind_bijective_uniform_cross (BitVec k) (x ^^^ ·)
      (Equiv.xor x).bijective cont z

/-- Let `msg : BitVec n` and `g : BitVec n → BitVec m` be fixed, and let `ks` and `mask` be
independent uniform samples from `BitVec n` and `BitVec m`. Then the pair
`(msg ⊕ ks, g(msg ⊕ ks) ⊕ mask)` is uniform on `BitVec n × BitVec m`. -/
theorem evalDist_pair_xor_uniform {n m : ℕ} (msg : BitVec n) (g : BitVec n → BitVec m) :
    evalDist (do
      let mask ← ($ᵗ BitVec m : ProbComp (BitVec m))
      let ks ← ($ᵗ BitVec n : ProbComp (BitVec n))
      return (msg ^^^ ks, g (msg ^^^ ks) ^^^ mask))
      = evalDist ($ᵗ (BitVec n × BitVec m) : ProbComp (BitVec n × BitVec m)) := by
  rw [evalDist_bind_bind_swap,
    ToVCVio.uniformSample_prod_eq_bind (BitVec n) (BitVec m)]
  refine (evalDist_bind_xor_left_uniform msg (fun c => ($ᵗ BitVec m : ProbComp (BitVec m)) >>=
    fun mask => (pure (c, g c ^^^ mask) : ProbComp (BitVec n × BitVec m)))).trans ?_
  refine evalDist_bind_congr' _ fun c => ?_
  exact evalDist_bind_xor_left_uniform (g c) fun t => (pure (c, t) : ProbComp _)

/-- Sanity check at width `n = 0`. -/
example {m : ℕ} (msg : BitVec 0) (g : BitVec 0 → BitVec m) :
    evalDist (do
      let mask ← ($ᵗ BitVec m : ProbComp (BitVec m))
      let ks ← ($ᵗ BitVec 0 : ProbComp (BitVec 0))
      return (msg ^^^ ks, g (msg ^^^ ks) ^^^ mask))
      = evalDist ($ᵗ (BitVec 0 × BitVec m) : ProbComp (BitVec 0 × BitVec m)) :=
  evalDist_pair_xor_uniform msg g

/-- Sanity check at width `m = 0`. -/
example {n : ℕ} (msg : BitVec n) (g : BitVec n → BitVec 0) :
    evalDist (do
      let mask ← ($ᵗ BitVec 0 : ProbComp (BitVec 0))
      let ks ← ($ᵗ BitVec n : ProbComp (BitVec n))
      return (msg ^^^ ks, g (msg ^^^ ks) ^^^ mask))
      = evalDist ($ᵗ (BitVec n × BitVec 0) : ProbComp (BitVec n × BitVec 0)) :=
  evalDist_pair_xor_uniform msg g

/-! ## From a list of independent draws to one uniform vector -/

/-- Let `q = pts.length`. A list of `q` independent uniform samples from `R` equals `xs` with
probability `|R|⁻¹ ^ q` if `xs` has length `q`, and `0` otherwise. -/
lemma probOutput_mapM_const_uniform {D R : Type} [SampleableType R] [Fintype R]
    (pts : List D) (xs : List R) :
    Pr[= xs | pts.mapM (fun _ => ($ᵗ R : ProbComp R))] =
      if xs.length = pts.length then ((Fintype.card R : ℝ≥0∞)⁻¹) ^ pts.length else 0 := by
  rw [probOutput_list_mapM]
  by_cases h : xs.length = pts.length
  · rw [if_pos h, if_pos h, List.prod_eq_pow_card _ ((Fintype.card R : ℝ≥0∞)⁻¹),
      List.length_zipWith, h, Nat.min_self]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    simp [probOutput_uniformSample]
  · rw [if_neg h, if_neg h]

/-- A uniform `v : Vector R n` has `v.toList = xs` with probability `|R|⁻¹ ^ n` if `xs` has
length `n`, and `0` otherwise. -/
private lemma probOutput_toList_uniformSample_vector {R : Type} [SampleableType R] [Fintype R]
    (n : ℕ) (xs : List R) :
    Pr[= xs | (Vector.toList <$> ($ᵗ Vector R n : ProbComp (Vector R n)))] =
      if xs.length = n then ((Fintype.card R : ℝ≥0∞)⁻¹) ^ n else 0 := by
  by_cases hlen : xs.length = n
  · rw [if_pos hlen]
    have hv : (⟨xs.toArray, by simpa using hlen⟩ : Vector R n).toList = xs := by
      simp [Vector.toList]
    rw [← hv, probOutput_map_injective _ (fun a b hab => Vector.toList_inj.mp hab),
      probOutput_uniformSample, Fintype.card_vector, Nat.cast_pow, ENNReal.inv_pow]
  · rw [if_neg hlen, probOutput_map]
    refine probEvent_eq_zero fun v _ hv => hlen ?_
    rw [← hv]
    simp [Vector.toList]

/-- One independent uniform draw per element of `pts` is distributed as one uniform
`Vector R pts.length`, read as a list. -/
theorem evalDist_mapM_const_uniform {D R : Type} [SampleableType R]
    (pts : List D) :
    evalDist (pts.mapM (fun _ => ($ᵗ R : ProbComp R))) =
      evalDist (Vector.toList <$> ($ᵗ Vector R pts.length : ProbComp _)) := by
  let : Fintype R := Fintype.ofFinite R
  refine evalDist_ext fun xs => ?_
  rw [probOutput_mapM_const_uniform, probOutput_toList_uniformSample_vector]

end ToVCVio
