/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.Constructions.SampleableType
import VCVio.EvalDist.BitVec
import VCVio.EvalDist.Prod
import ToVCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-!
# Uniform `BitVec` block concatenation

Uniformity facts about bit vectors built from uniform draws. Candidate for upstream VCVio
(mirrors `VCVio/OracleComp/Constructions/BitVec.lean`; the namespace is only to satisfy
`lake lint` here).

* `evalDist_blocksToBitVec_uniform`: the first `L ≤ 128 * n` bits of `n` independent uniform
  128-bit blocks are uniform on `BitVec L`.
* `evalDist_pair_xor_uniform`: a value masked by a uniform `BitVec n`, paired with any
  function of it masked by an independent uniform `BitVec m`, is uniform on the product.
* `evalDist_mapM_const_uniform`: a list of independent uniform draws is one uniform vector.
-/

open OracleSpec OracleComp ENNReal

/-- Mathlib's `card_vector` for `Vector` rather than `List.Vector`. -/
lemma Fintype.card_vector (α : Type) [Fintype α] (n : ℕ) :
    Fintype.card (Vector α n) = Fintype.card α ^ n := by
  rw [Fintype.card_congr
    { toFun := fun (v : Vector α n) (i : Fin n) => v.get i
      invFun := Vector.ofFn
      left_inv := fun v => Vector.ext fun i hi => by simp [Vector.ofFn, Vector.get]
      right_inv := fun f => funext fun i => Vector.getElem_ofFn .. }]
  simp

namespace ToVCVio

/-- The first `p` bits (big-endian) of the concatenation `blocks[0] ‖ blocks[1] ‖ …`,
zero-padded if `p` exceeds `128 * blocks.length`. -/
def blocksToBitVec (blocks : List (BitVec 128)) (p : ℕ) : BitVec p :=
  (BitVec.ofBoolListBE ((List.range p).map fun j =>
    (blocks.getD (j / 128) 0).getMsbD (j % 128))).cast (by simp)

lemma getMsbD_blocksToBitVec (blocks : List (BitVec 128)) {p j : ℕ} (hj : j < p) :
    (blocksToBitVec blocks p).getMsbD j = (blocks.getD (j / 128) 0).getMsbD (j % 128) := by
  simp [blocksToBitVec, List.getD_eq_getElem?_getD, hj]

/-- The `p` bits starting at bit `s` (big-endian) of the concatenation
`blocks[0] ‖ blocks[1] ‖ …`; `blocksToBitVec` is the case `s = 0`. -/
def blocksToBitVecFrom (blocks : List (BitVec 128)) (s p : ℕ) : BitVec p :=
  (BitVec.ofBoolListBE ((List.range p).map fun j =>
    (blocks.getD ((s + j) / 128) 0).getMsbD ((s + j) % 128))).cast (by simp)

lemma getMsbD_blocksToBitVecFrom (blocks : List (BitVec 128)) {s p j : ℕ} (hj : j < p) :
    (blocksToBitVecFrom blocks s p).getMsbD j =
      (blocks.getD ((s + j) / 128) 0).getMsbD ((s + j) % 128) := by
  simp [blocksToBitVecFrom, List.getD_eq_getElem?_getD, hj]

/-- The concatenation of `n` 128-bit blocks cut at bit `L`: the first `L` bits and the rest.
A bijection when `L ≤ 128 * n` (`blocksSplit_bijective`). -/
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

/-- Injective between types of the same cardinality `2 ^ (128 * n)`, hence bijective. -/
lemma blocksSplit_bijective (n L : ℕ) (hL : L ≤ 128 * n) :
    Function.Bijective (blocksSplit n L) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨blocksSplit_injective n L hL, ?_⟩
  rw [Fintype.card_vector, card_bitVec, ← pow_mul, Fintype.card_prod,
    card_bitVec, card_bitVec, ← pow_add]
  exact congrArg (2 ^ ·) (by omega)

/-- The first `L ≤ 128 * n` bits of `n` independent uniform blocks are uniform. -/
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

/-- Pointwise form of `evalDist_blocksToBitVec_uniform`. -/
theorem probOutput_blocksToBitVec_uniform (n L : ℕ) (hL : L ≤ 128 * n) (y : BitVec L) :
    Pr[= y | (fun v : Vector (BitVec 128) n => blocksToBitVec v.toList L) <$>
        ($ᵗ Vector (BitVec 128) n)] = (Fintype.card (BitVec L) : ℝ≥0∞)⁻¹ := by
  rw [evalDist_ext_iff.mp (evalDist_blocksToBitVec_uniform n L hL) y,
    probOutput_uniformSample]

/-- Sanity check at `L = 0`: `BitVec 0` is a singleton, hit with probability `1`. -/
example (n : ℕ) (y : BitVec 0) :
    Pr[= y | (fun v : Vector (BitVec 128) n => blocksToBitVec v.toList 0) <$>
        ($ᵗ Vector (BitVec 128) n)] = 1 := by
  simpa using probOutput_blocksToBitVec_uniform n 0 (Nat.zero_le _) y


/-- Xor with a fixed `BitVec` is a bijection (it is its own inverse). -/
lemma bitVec_xor_left_bijective {k : ℕ} (x : BitVec k) : Function.Bijective (x ^^^ ·) :=
  ⟨fun a b h => by simpa using congrArg (x ^^^ ·) h, fun y => ⟨x ^^^ y, by simp⟩⟩

/-- One-time pad: a uniform draw xored with a fixed value is still uniform, under any
continuation. -/
private lemma evalDist_bind_xor_left_uniform {k : ℕ} {γ : Type} (x : BitVec k)
    (cont : BitVec k → ProbComp γ) :
    𝒟[($ᵗ BitVec k : ProbComp (BitVec k)) >>= fun y => cont (x ^^^ y)] =
      𝒟[($ᵗ BitVec k : ProbComp (BitVec k)) >>= cont] :=
  evalDist_ext fun z =>
    probOutput_bind_bijective_uniform_cross (BitVec k) (x ^^^ ·)
      (bitVec_xor_left_bijective x) cont z

/-- A value masked by a uniform `ks`, paired with an arbitrary function `g` of it masked by an
independent uniform `mask`, is *jointly* uniform on `BitVec n × BitVec m` (not merely uniform
in each component): given the first component, `mask` still re-randomizes the second. -/
theorem evalDist_pair_xor_uniform {n m : ℕ} (msg : BitVec n) (g : BitVec n → BitVec m) :
    evalDist (do
      let mask ← ($ᵗ BitVec m : ProbComp (BitVec m))
      let ks ← ($ᵗ BitVec n : ProbComp (BitVec n))
      return (msg ^^^ ks, g (msg ^^^ ks) ^^^ mask))
      = evalDist ($ᵗ (BitVec n × BitVec m) : ProbComp (BitVec n × BitVec m)) := by
  rw [OracleComp.DeferredSampling.evalDist_bind_comm,
    ToVCVio.uniformSample_prod_eq_bind (BitVec n) (BitVec m)]
  refine (evalDist_bind_xor_left_uniform msg (fun c => ($ᵗ BitVec m : ProbComp (BitVec m)) >>=
    fun mask => (pure (c, g c ^^^ mask) : ProbComp (BitVec n × BitVec m)))).trans ?_
  refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun c => ?_
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


/-- One independent uniform draw per element of `pts` puts mass `(card R)⁻¹ ^ pts.length` on
each list of length `pts.length` and `0` elsewhere. -/
lemma probOutput_mapM_const_uniform {D R : Type} [SampleableType R] [Fintype R]
    (pts : List D) (xs : List R) :
    Pr[= xs | pts.mapM (fun _ => ($ᵗ R : ProbComp R))] =
      if xs.length = pts.length then ((Fintype.card R : ℝ≥0∞)⁻¹) ^ pts.length else 0 := by
  letI : DecidableEq R := Classical.decEq R
  induction pts generalizing xs with
  | nil =>
      rw [List.mapM_nil]
      cases xs with
      | nil => simp
      | cons y ys => simp
  | cons t ts ih =>
      rw [List.mapM_cons, probOutput_bind_eq_sum_fintype]
      simp only [bind_pure_comp, probOutput_uniformSample]
      cases xs with
      | nil =>
          -- Every output of the loop is a cons, so the empty list is never produced.
          have hin : ∀ r : R,
              Pr[= ([] : List R) | ((r :: ·) <$> List.mapM (fun _ => ($ᵗ R : ProbComp R)) ts)]
                = 0 := by
            intro r
            rw [probOutput_map]
            simp
          simp [hin]
      | cons y ys =>
          -- Only the draw `r = y` can produce the head of `y :: ys`, and `(y :: ·)` is
          -- injective, so the tail probability is the one supplied by the induction.
          have hin : ∀ r : R,
              Pr[= y :: ys | ((r :: ·) <$> List.mapM (fun _ => ($ᵗ R : ProbComp R)) ts)]
                = if r = y then Pr[= ys | List.mapM (fun _ => ($ᵗ R : ProbComp R)) ts]
                  else 0 := by
            intro r
            by_cases hr : r = y
            · subst hr
              rw [if_pos rfl]
              exact probOutput_map_injective _ (fun a b hab => by simpa using hab) ys
            · rw [if_neg hr, probOutput_map]
              simp [hr]
          simp only [hin, mul_ite, mul_zero, Finset.sum_ite_eq' Finset.univ y,
            Finset.mem_univ, if_true, ih ys, List.length_cons]
          by_cases hlen : ys.length = ts.length
          · simp [hlen, pow_succ, mul_comm]
          · simp [hlen]

/-- A uniform `Vector R n`, read as a list, puts mass `(card R)⁻¹ ^ n` on each list of length
`n` and `0` elsewhere. -/
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
  letI : Fintype R := Fintype.ofFinite R
  refine evalDist_ext fun xs => ?_
  rw [probOutput_mapM_const_uniform, probOutput_toList_uniformSample_vector]

end ToVCVio
