/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import LatticeCrypto.Ring.Transform

/-!
# Finite-vector and transpose identities for transform rings

Let `R` be a commutative ring represented by coefficient vectors whose
multiplication is polynomial multiplication modulo `X^n+1`.  Equivalently,
`X^n=-1`, so a term whose degree passes `n-1` re-enters at the corresponding
lower degree with a minus sign; this multiplication is conventionally called
*negacyclic*.  Let `ops : TransformOps R R̂` be a transform interface from `R`
to an additive transform domain `R̂`.  For vectors `u,v ∈ R̂^k`, its dot
product is

`dot(u,v) = ∑_{i=0}^{k-1} mulHat(u_i,v_i)`.

For a matrix `A ∈ R̂^{r×c}`, the definitions of matrix-vector multiplication
give

```
(A v)_i   = dot(A_i,v),
(Aᵀ u)_j  = dot((A_{ij})_i,u).
```

If `ops` satisfies `TransformOps.Laws`, transform multiplication is the
transport of a commutative ring multiplication.  It is therefore bilinear and
commutative, and finite rearrangement yields the transpose-exchange identity

`dot(s,Aᵀy) = dot(As,y)`.                                (1)

This file proves these identities for every transform satisfying
`TransformOps.Laws`.
-/

universe u v

namespace LatticeCrypto.TransformOps

variable {Coeff : Type u} [CommRing Coeff] {ring : NegacyclicRing Coeff} {Hat : Type v}
  [AddCommGroup Hat] (ops : TransformOps ring Hat)

/-- Folding addition over a vector equals the finite sum of its entries. -/
private theorem foldl_add_eq_sum {k : Nat} (w : PolyVec Hat k) :
    w.foldl (· + ·) (0 : Hat) = ∑ i : Fin k, w.get i := by
  induction k with
  | zero =>
    have hw : w = #v[] := Vector.eq_empty
    subst hw
    simp
  | succ n ih =>
    haveI : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
    obtain ⟨w', x, rfl⟩ : ∃ (w' : Vector Hat n) (x : Hat), w = w'.push x :=
      ⟨w.pop, w.back, (Vector.push_pop_back w).symm⟩
    rw [Vector.foldl_push, ih w', Fin.sum_univ_castSucc]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      change w'[i.val] = (w'.push x)[i.val]
      exact (Vector.getElem_push_lt i.isLt).symm
    · change x = (w'.push x)[n]
      exact Vector.getElem_push_eq.symm

/-- The transform-domain dot product as a finite sum of pointwise products. -/
theorem dot_eq_sum {k : Nat} (u v : PolyVec Hat k) :
    ops.dot u v = ∑ i : Fin k, ops.mulHat (u.get i) (v.get i) := by
  change (Vector.zipWith ops.mulHat u v).foldl (· + ·) (0 : Hat) = _
  rw [foldl_add_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change (Vector.zipWith ops.mulHat u v)[i.val] = ops.mulHat u[i.val] v[i.val]
  exact Vector.getElem_zipWith i.isLt

/-- Entry `i` of a matrix-vector product is the dot product of row `i` with the
vector. -/
theorem matVecMul_get {rows cols : Nat} (A : PolyMatrix Hat rows cols)
    (v : PolyVec Hat cols) (i : Fin rows) :
    (ops.matVecMul A v).get i = ops.dot (A.get i) v :=
  Vector.get_map A _ i

/-- Entry `j` of a transposed matrix-vector product is the dot product of column
`j` with the vector. -/
theorem matTransposeVecMul_get {rows cols : Nat} (A : PolyMatrix Hat rows cols)
    (v : PolyVec Hat rows) (j : Fin cols) :
    (ops.matTransposeVecMul A v).get j =
      ops.dot (Vector.ofFn fun i => (A.get i).get j) v := by
  change ((transpose A).map fun row => ops.dot row v).get j = _
  rw [Vector.get_map]
  change ops.dot ((Vector.ofFn fun j => Vector.ofFn fun i => (A.get i).get j).get j) v = _
  rw [Vector.get_ofFn]

variable [laws : Laws ops]

/-- Transform-domain multiplication distributes over a finite sum on the right. -/
theorem mulHat_sum {ι : Type*} (a : Hat) (t : Finset ι) (f : ι → Hat) :
    ops.mulHat a (∑ i ∈ t, f i) = ∑ i ∈ t, ops.mulHat a (f i) :=
  map_sum (AddMonoidHom.mk' (ops.mulHat a) (laws.mul_add a)) f t

/-- Transform-domain multiplication distributes over a finite sum on the left. -/
theorem sum_mulHat {ι : Type*} (t : Finset ι) (f : ι → Hat) (b : Hat) :
    ops.mulHat (∑ i ∈ t, f i) b = ∑ i ∈ t, ops.mulHat (f i) b := by
  rw [mulHat_comm ops, mulHat_sum ops]
  exact Finset.sum_congr rfl fun i _ => mulHat_comm ops b (f i)

/-- The transform-domain dot product is commutative. -/
theorem dot_comm {k : Nat} (u v : PolyVec Hat k) : ops.dot u v = ops.dot v u := by
  rw [dot_eq_sum ops, dot_eq_sum ops]
  exact Finset.sum_congr rfl fun i _ => mulHat_comm ops _ _

/-- The transform-domain dot product is additive in its first argument. -/
theorem dot_add_left {k : Nat} (u v w : PolyVec Hat k) :
    ops.dot (u + v) w = ops.dot u w + ops.dot v w := by
  rw [dot_comm ops (u + v) w, dot_add_right ops w u v, dot_comm ops w u, dot_comm ops w v]

/-- Applying the transform coordinate-wise after the inverse transform is the
identity on transform-domain vectors. -/
theorem hatVec_unhatVec {k : Nat} (vHat : PolyVec Hat k) :
    ops.hatVec (ops.unhatVec vHat) = vHat := by
  refine Vector.ext fun i hi => ?_
  simp only [hatVec, unhatVec, Vector.getElem_map]
  exact laws.toHat_fromHat vHat[i]

/-- Transpose exchange:
`dot(s, Aᵀy) = dot(As, y)` in the transform domain. -/
theorem dot_matTransposeVecMul {rows cols : Nat} (A : PolyMatrix Hat rows cols)
    (s : PolyVec Hat cols) (y : PolyVec Hat rows) :
    ops.dot s (ops.matTransposeVecMul A y) = ops.dot (ops.matVecMul A s) y := by
  rw [dot_eq_sum ops, dot_eq_sum ops]
  simp only [matTransposeVecMul_get, matVecMul_get, dot_eq_sum, Vector.get_ofFn,
    mulHat_sum, sum_mulHat]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← mulHat_assoc ops, mulHat_comm ops (s.get j) ((A.get i).get j)]

end LatticeCrypto.TransformOps
