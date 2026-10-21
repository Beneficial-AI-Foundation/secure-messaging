/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.EvalDist.Monad.Map
public import VCVio.EvalDist.Prod
public import VCVio.EvalDist.List
public import VCVio.OracleComp.Constructions.Replicate
public import ToVCVio.OracleComp.Constructions.SampleableType
public import Mathlib.Data.LawfulXor.Equiv

/-!
# Uniform `BitVec` block concatenation

Uniformity facts about bit vectors built from uniform draws, candidates for
`VCVio/OracleComp/Constructions/BitVec.lean` upstream.

* `natCast_card_bitVec`: `|BitVec w| = 2 ^ w` in any semiring, for whichever `Fintype` instance
  the goal carries.
* `evalDistEq_blocksToBitVec_uniform`: the first `L ≤ w * n` bits of `n` independent uniform
  `w`-bit blocks are uniform on `BitVec L`.
* `evalDistEq_pair_xor_uniform`: a value masked by a uniform `BitVec n`, paired with any
  function of it masked by an independent uniform `BitVec m`, is uniform on the product.
* `evalDistEq_mapM_const_uniform`: a list of independent uniform draws is one uniform vector.
-/

@[expose] public section

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
  rw [Fintype.card_vector, Fintype.card_bitVec, ← pow_mul, Fintype.card_prod,
    Fintype.card_bitVec, Fintype.card_bitVec, ← pow_add]
  exact congrArg (2 ^ ·) (Nat.add_sub_cancel' hL).symm

/-- The first `L ≤ w * n` bits of `n` independent uniform `w`-bit blocks are uniform. -/
theorem evalDistEq_blocksToBitVec_uniform (n L : ℕ) (hL : L ≤ w * n) :
    (fun v : Vector (BitVec w) n => blocksToBitVec v.toList L) <$>
        ($ᵗ Vector (BitVec w) n) =ᵈ ($ᵗ BitVec L : ProbComp (BitVec L)) := by
  have hsplit : (fun v : Vector (BitVec w) n => blocksToBitVec v.toList L) <$>
      ($ᵗ Vector (BitVec w) n : ProbComp _) =
        Prod.fst <$> (blocksSplit n L <$> ($ᵗ Vector (BitVec w) n)) := by
    rw [Functor.map_map]; rfl
  rw [hsplit]
  refine ((SampleableType.map_uniformSample_evalDistEq_of_bijective
    (blocksSplit_bijective n L hL)).map Prod.fst).trans ?_
  exact OracleComp.evalDistEq_of_forall_prEvent_eq_output fun y => by
    rw [prEvent_map]
    exact SampleableType.prEvent_uniformSample_fst (fun x => x = y)

/-- Pointwise form of `evalDistEq_blocksToBitVec_uniform`. -/
theorem prEvent_blocksToBitVec_uniform (n L : ℕ) (hL : L ≤ w * n) (y : BitVec L) :
    Pr{let x ← ((fun v : Vector (BitVec w) n => blocksToBitVec v.toList L) <$>
        ($ᵗ Vector (BitVec w) n))}[x = y] = (Fintype.card (BitVec L) : ℝ≥0∞)⁻¹ :=
  ((evalDistEq_blocksToBitVec_uniform n L hL).prEvent_eq _).trans
    (SampleableType.prEvent_uniformSample_eq_singleton y)

/-- Sanity check at `L = 0`: `BitVec 0` is a singleton, hit with probability `1`. -/
example (n : ℕ) (y : BitVec 0) :
    Pr{let x ← ((fun v : Vector (BitVec w) n => blocksToBitVec v.toList 0) <$>
        ($ᵗ Vector (BitVec w) n))}[x = y] = 1 := by
  simpa using prEvent_blocksToBitVec_uniform n 0 (Nat.zero_le _) y

/-! ## A masked value and a masked function of it are jointly uniform -/

/-- One-time pad: for fixed `x` and uniform `y`, `x ⊕ y` is uniform, also when passed to an
arbitrary continuation. -/
private lemma evalDistEq_bind_xor_left_uniform {k : ℕ} {γ : Type} (x : BitVec k)
    (cont : BitVec k → ProbComp γ) :
    (($ᵗ BitVec k : ProbComp (BitVec k)) >>= fun y => cont (x ^^^ y)) =ᵈ
      (($ᵗ BitVec k : ProbComp (BitVec k)) >>= cont) := by
  have h := (SampleableType.map_uniformSample_evalDistEq_of_bijective (α := BitVec k)
    (f := (x ^^^ ·)) (Equiv.xor x).bijective).bind_left cont
  simpa only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply] using h

/-- Let `msg : BitVec n` and `g : BitVec n → BitVec m` be fixed, and let `ks` and `mask` be
independent uniform samples from `BitVec n` and `BitVec m`. Then the pair
`(msg ⊕ ks, g(msg ⊕ ks) ⊕ mask)` is uniform on `BitVec n × BitVec m`. -/
theorem evalDistEq_pair_xor_uniform {n m : ℕ} (msg : BitVec n) (g : BitVec n → BitVec m) :
    (do
      let mask ← ($ᵗ BitVec m : ProbComp (BitVec m))
      let ks ← ($ᵗ BitVec n : ProbComp (BitVec n))
      return (msg ^^^ ks, g (msg ^^^ ks) ^^^ mask))
      =ᵈ ($ᵗ (BitVec n × BitVec m) : ProbComp (BitVec n × BitVec m)) := by
  rw [SampleableType.uniformSample_prod_eq_bind (BitVec n) (BitVec m)]
  refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine (evalDistEq_bind_xor_left_uniform msg (fun c => ($ᵗ BitVec m : ProbComp (BitVec m)) >>=
    fun mask => (pure (c, g c ^^^ mask) : ProbComp (BitVec n × BitVec m)))).trans ?_
  exact EvalDistEq.bind_right _ fun c =>
    evalDistEq_bind_xor_left_uniform (g c) fun t => (pure (c, t) : ProbComp _)

/-- Sanity check at width `n = 0`. -/
example {m : ℕ} (msg : BitVec 0) (g : BitVec 0 → BitVec m) :
    (do
      let mask ← ($ᵗ BitVec m : ProbComp (BitVec m))
      let ks ← ($ᵗ BitVec 0 : ProbComp (BitVec 0))
      return (msg ^^^ ks, g (msg ^^^ ks) ^^^ mask))
      =ᵈ ($ᵗ (BitVec 0 × BitVec m) : ProbComp (BitVec 0 × BitVec m)) :=
  evalDistEq_pair_xor_uniform msg g

/-- Sanity check at width `m = 0`. -/
example {n : ℕ} (msg : BitVec n) (g : BitVec n → BitVec 0) :
    (do
      let mask ← ($ᵗ BitVec 0 : ProbComp (BitVec 0))
      let ks ← ($ᵗ BitVec n : ProbComp (BitVec n))
      return (msg ^^^ ks, g (msg ^^^ ks) ^^^ mask))
      =ᵈ ($ᵗ (BitVec n × BitVec 0) : ProbComp (BitVec n × BitVec 0)) :=
  evalDistEq_pair_xor_uniform msg g

/-! ## From a list of independent draws to one uniform vector -/

/-- A uniform `v : Vector R n` has `v.toList = xs` with probability `(|R| ^ n)⁻¹` if `xs` has
length `n`, and `0` otherwise. -/
private lemma prEvent_toList_uniformSample_vector {R : Type} [SampleableType R] [Fintype R]
    (n : ℕ) (xs : List R) :
    Pr{let x ← (Vector.toList <$> ($ᵗ Vector R n : ProbComp (Vector R n)))}[x = xs] =
      if xs.length = n then ((Fintype.card R ^ n : ℕ) : ℝ≥0∞)⁻¹ else 0 := by
  by_cases hlen : xs.length = n
  · simp only [hlen, ↓reduceIte]
    have hv : (⟨xs.toArray, by simpa using hlen⟩ : Vector R n).toList = xs := by
      simp [Vector.toList]
    rw [← hv, prEvent_map_injective _ (fun a b hab => Vector.toList_inj.mp hab),
      SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_vector]
  · simp only [hlen, ↓reduceIte]
    rw [prEvent_map]
    refine prEvent_eq_zero_of_forall_mem_support _ _ fun v _ hv => hlen ?_
    rw [← hv]
    simp [Vector.toList]

/-- Mapping a constant computation over a list is `replicate` of its length. -/
private lemma mapM_const_eq_replicate {D R : Type} (c : ProbComp R) (pts : List D) :
    pts.mapM (fun _ => c) = OracleComp.replicate pts.length c := by
  induction pts with
  | nil => rfl
  | cons _ ps ih => rw [List.mapM_cons, ih, List.length_cons, OracleComp.replicate_succ_bind]

/-- One independent uniform draw per element of `pts` is distributed as one uniform
`Vector R pts.length`, read as a list. -/
theorem evalDistEq_mapM_const_uniform {D R : Type} [SampleableType R]
    (pts : List D) :
    pts.mapM (fun _ => ($ᵗ R : ProbComp R)) =ᵈ
      (Vector.toList <$> ($ᵗ Vector R pts.length : ProbComp _)) := by
  let : Fintype R := Fintype.ofFinite R
  refine OracleComp.evalDistEq_of_forall_prEvent_eq_output fun xs => ?_
  rw [mapM_const_eq_replicate, prEvent_toList_uniformSample_vector]
  by_cases h : xs.length = pts.length
  · simp only [h, ↓reduceIte]
    exact SampleableType.prEvent_replicate_uniformSample h
  · simp only [h, ↓reduceIte]
    refine prEvent_eq_zero_of_forall_mem_support _ _ fun v hv hvx => h ?_
    rw [OracleComp.support_replicate] at hv
    exact hvx ▸ hv.1

end ToVCVio
