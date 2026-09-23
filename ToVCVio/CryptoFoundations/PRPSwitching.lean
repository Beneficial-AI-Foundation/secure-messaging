/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.Constructions.SampleableType
import ToVCVio.OracleComp.Constructions.SampleableType
import ToVCVio.EvalDist.UniformInjection
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Fixed-list PRP/PRF switching

Let `X` be a finite nonempty set of size `N = Fintype.card X`, and let `x₁, …, x_q` be a fixed
list `pts` of pairwise-distinct points of `X`, so `q = pts.length`. Consider two distributions on
lists of outputs:

* `P`, the law of `π(x₁), …, π(x_q)` for a uniformly random permutation `π` of `X`;
* `F`, the law of `q` independent uniform elements of `X`. For distinct points this is also the
  law of `f(x₁), …, f(x_q)` for a uniformly random function `f : X → X`.

We prove that `P` is uniform over lists of `q` distinct elements of `X`, that is, `P` samples `q`
elements without replacement. We then prove that the total-variation distance between `P` and
`F` is at most `q(q - 1)/(2N)`, so any test of the output list accepts with probabilities that
differ by at most this bound.

The proof shows by symmetry that all lists of distinct outputs are equally likely under `P`,
without counting permutations, then compares sampling without replacement to independent
sampling. The bound is the birthday bound: `q(q - 1)/2` pairs of positions, each equal under `F`
with probability `1/N`. At `N = 2ⁿ` it is `q(q - 1)/2ⁿ⁺¹`, Lemma 1 of the reference below.

The points must be fixed in advance: choosing later points from earlier outputs is not covered,
since the reductions that use this file query the permutation on a fixed list. `q` counts every
point at which the permutation is evaluated, which for a mode of operation may exceed its
message-block count.

## Main results

* `evalDist_map_uniformPerm_eq_uniformDistinct`: `P` is sampling without replacement.
* `tvDist_map_uniformPerm_mapM_const_uniform_le`: the bound on the distance between `P` and `F`.

## Reference

Bellare and Rogaway, *The Security of Triple Encryption and a Framework for Code-Based
Game-Playing Proofs*, EUROCRYPT 2006, <https://eprint.iacr.org/2004/331.pdf>.
-/

open ENNReal OracleComp

namespace OracleComp

/-- The embedding `Fin pts.length ↪ X`, `i ↦ pts[i]`, given by a duplicate-free list. -/
def nodupEmbedding {X : Type} (pts : List X) (hpts : pts.Nodup) : Fin pts.length ↪ X :=
  ⟨fun i => pts[i], fun i j hij => Fin.ext (hpts.getElem_inj_iff.mp hij)⟩

/-- Drawing `q` points of `X` without replacement: a uniform injective `q`-tuple, as a list.

`hq` is explicit because callers hold it as a term, `⟨nodupEmbedding pts hpts⟩`, and it
appears in the statement of `evalDist_map_uniformPerm_eq_uniformDistinct`. There is no
instance to find anyway: `Nonempty (Fin q ↪ X)` needs `q ≤ Fintype.card X`. -/
def sampleDistinctFrom (X : Type) [FinEnum X] (q : ℕ)
    (hq : Nonempty (Fin q ↪ X)) : ProbComp (List X) :=
  letI := hq
  (fun e : Fin q ↪ X => List.ofFn e) <$> ($ᵗ (Fin q ↪ X) : ProbComp (Fin q ↪ X))

/-- Let `e₀ : Fin q ↪ X` be a fixed injective function and let `π` be a uniformly random
permutation of `X`. Then `π ∘ e₀` is uniformly distributed over all injective functions
`Fin q ↪ X`. -/
theorem evalDist_map_trans_uniformPerm {X : Type} [FinEnum X] {q : ℕ}
    [Nonempty (Fin q ↪ X)] (e₀ : Fin q ↪ X) :
    evalDist ((fun π : Equiv.Perm X => e₀.trans π.toEmbedding) <$>
        ($ᵗ (Equiv.Perm X) : ProbComp (Equiv.Perm X)))
      = evalDist ($ᵗ (Fin q ↪ X) : ProbComp (Fin q ↪ X)) := by
  set Φ : Equiv.Perm X → (Fin q ↪ X) := fun π => e₀.trans π.toEmbedding
  -- Invariance of `Φ <$> $ᵗ (Equiv.Perm X)` under post-composition by any fixed `σ`.
  have hinv : ∀ σ : Equiv.Perm X,
      evalDist ((fun f : Fin q ↪ X => f.trans σ.toEmbedding) <$>
          (Φ <$> ($ᵗ (Equiv.Perm X) : ProbComp (Equiv.Perm X))))
        = evalDist (Φ <$> ($ᵗ (Equiv.Perm X) : ProbComp (Equiv.Perm X))) := by
    intro σ
    have hcomp : ((fun f : Fin q ↪ X => f.trans σ.toEmbedding) <$>
          (Φ <$> ($ᵗ (Equiv.Perm X) : ProbComp (Equiv.Perm X))))
        = Φ <$> ((fun π : Equiv.Perm X => σ * π) <$>
          ($ᵗ (Equiv.Perm X) : ProbComp (Equiv.Perm X))) := by
      rw [Functor.map_map, Functor.map_map]
      exact congrArg (· <$> ($ᵗ (Equiv.Perm X) : ProbComp (Equiv.Perm X)))
        (funext fun π => Function.Embedding.ext fun i => rfl)
    rw [hcomp]
    exact evalDist_map_eq_of_evalDist_eq
      (evalDist_ext (probOutput_map_bijective_uniformSample (Equiv.Perm X)
        (Group.mulLeft_bijective σ))) Φ
  refine ToVCVio.evalDist_eq_uniformSample_of_uniform _ ?_ ?_
  · -- Full support: transitivity of the action hits every embedding.
    intro e'
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair e₀ e' e₀.injective e'.injective
    rw [support_map, support_uniformSample]
    exact ⟨σ, Set.mem_univ σ, Function.Embedding.ext fun i => hσ i⟩
  · -- Pointwise uniformity: transport the mass along the transitive action.
    intro e e'
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair e e' e.injective e'.injective
    have he' : e' = e.trans σ.toEmbedding := Function.Embedding.ext fun i => (hσ i).symm
    have hTinj : Function.Injective (fun f : Fin q ↪ X => f.trans σ.toEmbedding) := by
      intro f g hfg
      refine Function.Embedding.ext fun i => σ.injective ?_
      exact congrFun (congrArg (fun h : Fin q ↪ X => (h : Fin q → X)) hfg) i
    calc Pr[= e | Φ <$> ($ᵗ (Equiv.Perm X) : ProbComp (Equiv.Perm X))]
        = Pr[= e.trans σ.toEmbedding | (fun f : Fin q ↪ X => f.trans σ.toEmbedding) <$>
            (Φ <$> ($ᵗ (Equiv.Perm X) : ProbComp (Equiv.Perm X)))] :=
          (probOutput_map_injective _ hTinj e).symm
      _ = Pr[= e.trans σ.toEmbedding | Φ <$> ($ᵗ (Equiv.Perm X) : ProbComp (Equiv.Perm X))] :=
          evalDist_ext_iff.mp (hinv σ) _
      _ = Pr[= e' | Φ <$> ($ᵗ (Equiv.Perm X) : ProbComp (Equiv.Perm X))] := by rw [he']

/-- Let `pts = x₁, …, x_q` be fixed, pairwise-distinct elements of a finite set `X`. If `π` is a
uniformly random permutation of `X`, then `(π(x₁), …, π(x_q))` is uniformly distributed over all
ordered `q`-tuples of distinct elements of `X`. -/
theorem evalDist_map_uniformPerm_eq_uniformDistinct {X : Type} [FinEnum X]
    (pts : List X) (hpts : pts.Nodup) :
    evalDist ((fun π : Equiv.Perm X => pts.map π) <$>
        ($ᵗ (Equiv.Perm X) : ProbComp (Equiv.Perm X)))
      = evalDist (sampleDistinctFrom X pts.length ⟨nodupEmbedding pts hpts⟩) := by
  have hq : Nonempty (Fin pts.length ↪ X) := ⟨nodupEmbedding pts hpts⟩
  have hfun : ∀ π : Equiv.Perm X,
      pts.map π = List.ofFn ((nodupEmbedding pts hpts).trans π.toEmbedding) := by
    intro π
    rw [← List.ofFn_getElem_eq_map pts (π : X → X)]
    rfl
  have hRHS : sampleDistinctFrom X pts.length ⟨nodupEmbedding pts hpts⟩
      = (fun e : Fin pts.length ↪ X => List.ofFn e) <$>
        ($ᵗ (Fin pts.length ↪ X) : ProbComp (Fin pts.length ↪ X)) := rfl
  have hmapeq : ((fun π : Equiv.Perm X => pts.map π) <$>
        ($ᵗ (Equiv.Perm X) : ProbComp (Equiv.Perm X)))
      = (fun e : Fin pts.length ↪ X => List.ofFn e) <$>
        ((fun π : Equiv.Perm X => (nodupEmbedding pts hpts).trans π.toEmbedding) <$>
          ($ᵗ (Equiv.Perm X) : ProbComp (Equiv.Perm X))) := by
    rw [Functor.map_map]
    exact congrArg (· <$> ($ᵗ (Equiv.Perm X) : ProbComp (Equiv.Perm X))) (funext hfun)
  rw [hmapeq, hRHS]
  exact evalDist_map_eq_of_evalDist_eq
    (evalDist_map_trans_uniformPerm (nodupEmbedding pts hpts)) _

/-! ## The assembled fixed-list switching bound -/

/-- Replacing each of two probabilistic computations by one with the same output distribution
leaves their total-variation distance unchanged. -/
private theorem tvDist_congr {α : Type} {m₁ m₂ m₃ m₄ : ProbComp α}
    (h₁ : evalDist m₁ = evalDist m₂) (h₂ : evalDist m₃ = evalDist m₄) :
    tvDist m₁ m₃ = tvDist m₂ m₄ := by
  rw [tvDist, tvDist, h₁, h₂]

/-- The fixed-list PRP/PRF switching bound: for a duplicate-free list `pts` of `q` points,
applying a uniform permutation of `X` to `pts` and drawing `q` independent uniform elements of
`X` are within total-variation distance `q (q - 1) / (2 * card X)`.

The bound is read in `ℝ`: `pts.length - 1` is a real subtraction, and `q (q - 1)` is `0` at
`q = 0` and nonnegative otherwise. `[Nonempty X]` is what makes `X` sampleable; `[FinEnum X]`
alone does not. -/
theorem tvDist_map_uniformPerm_mapM_const_uniform_le {X : Type} [FinEnum X] [Nonempty X]
    (pts : List X) (hpts : pts.Nodup) :
    tvDist ((fun π : Equiv.Perm X => pts.map π) <$>
        ($ᵗ (Equiv.Perm X) : ProbComp (Equiv.Perm X)))
        (pts.mapM (fun _ => ($ᵗ X : ProbComp X)))
      ≤ (pts.length * (pts.length - 1) : ℝ) / (2 * Fintype.card X) := by
  let : DecidableEq X := Classical.decEq X
  have hq : Nonempty (Fin pts.length ↪ X) := ⟨nodupEmbedding pts hpts⟩
  have hNpos : 0 < Fintype.card X := Fintype.card_pos
  have hN0 : (Fintype.card X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hNpos.ne'
  -- (a) The permutation side, as a without-replacement draw. `sampleDistinctFrom`'s body is
  -- `rfl`-equal to the explicit map, the `Nonempty` witness being a `Prop`.
  have hRHSperm : sampleDistinctFrom X pts.length ⟨nodupEmbedding pts hpts⟩
      = (fun e : Fin pts.length ↪ X => List.ofFn (e : Fin pts.length → X)) <$>
        ($ᵗ (Fin pts.length ↪ X) : ProbComp (Fin pts.length ↪ X)) := rfl
  have hperm : evalDist ((fun π : Equiv.Perm X => pts.map π) <$>
      ($ᵗ (Equiv.Perm X) : ProbComp (Equiv.Perm X)))
      = evalDist ((fun e : Fin pts.length ↪ X => List.ofFn (e : Fin pts.length → X)) <$>
          ($ᵗ (Fin pts.length ↪ X) : ProbComp (Fin pts.length ↪ X))) := by
    rw [evalDist_map_uniformPerm_eq_uniformDistinct pts hpts, hRHSperm]
  -- (b) The i.i.d. side, as a single uniform function draw.
  rw [tvDist_congr hperm (evalDist_listMapM_uniform_eq_map_ofFn pts)]
  -- (c) Strip the common `List.ofFn`, leaving the embedding coercion against the full function
  -- space. `rw [Functor.map_map]` is used forwards and beta-reduces, so the coercion side is
  -- stated in its already-beta-reduced shape.
  have hmap : ((fun e : Fin pts.length ↪ X => List.ofFn (e : Fin pts.length → X)) <$>
        ($ᵗ (Fin pts.length ↪ X) : ProbComp (Fin pts.length ↪ X)))
      = (List.ofFn : (Fin pts.length → X) → List X) <$>
        ((fun e : Fin pts.length ↪ X => (e : Fin pts.length → X)) <$>
          ($ᵗ (Fin pts.length ↪ X) : ProbComp (Fin pts.length ↪ X))) := by
    rw [Functor.map_map]
  rw [hmap]
  refine (tvDist_map_le (List.ofFn : (Fin pts.length → X) → List X) _ _).trans ?_
  -- (d) The distance itself, and the two cardinalities.
  rw [tvDist_map_injective_uniformSample _ Function.Embedding.coe_injective,
    Fintype.card_embedding_eq, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  -- (e) The birthday arithmetic, after the single `ℕ → ℝ` cast. `pts.length = 0` is a real
  -- degenerate case (both sides are `0`); `pts.Nodup` makes `pts.length > card X` vacuous,
  -- although `two_mul_sub_descFactorial_le` covers that branch regardless.
  rcases Nat.eq_zero_or_pos pts.length with hq0 | hq1
  · rw [hq0]; simp
  have hD : (Fintype.card X).descFactorial pts.length ≤ Fintype.card X ^ pts.length :=
    Nat.descFactorial_le_pow _ _
  have hNq : (0 : ℝ) < (Fintype.card X : ℝ) ^ pts.length := by positivity
  have hB4 : 2 * (Fintype.card X : ℝ) * ((Fintype.card X : ℝ) ^ pts.length
        - (((Fintype.card X).descFactorial pts.length : ℕ) : ℝ))
      ≤ (pts.length : ℝ) * ((pts.length : ℝ) - 1) * (Fintype.card X : ℝ) ^ pts.length := by
    have h := two_mul_sub_descFactorial_le (Fintype.card X) pts.length
    have hcast : ((2 * Fintype.card X * (Fintype.card X ^ pts.length
          - (Fintype.card X).descFactorial pts.length) : ℕ) : ℝ)
        = 2 * (Fintype.card X : ℝ) * ((Fintype.card X : ℝ) ^ pts.length
          - (((Fintype.card X).descFactorial pts.length : ℕ) : ℝ)) := by
      push_cast [Nat.cast_sub hD]
      ring
    have hcast' : ((pts.length * (pts.length - 1) * Fintype.card X ^ pts.length : ℕ) : ℝ)
        = (pts.length : ℝ) * ((pts.length : ℝ) - 1)
          * (Fintype.card X : ℝ) ^ pts.length := by
      push_cast [Nat.cast_sub hq1]
      ring
    calc 2 * (Fintype.card X : ℝ) * ((Fintype.card X : ℝ) ^ pts.length
          - (((Fintype.card X).descFactorial pts.length : ℕ) : ℝ))
        = ((2 * Fintype.card X * (Fintype.card X ^ pts.length
            - (Fintype.card X).descFactorial pts.length) : ℕ) : ℝ) := hcast.symm
      _ ≤ ((pts.length * (pts.length - 1) * Fintype.card X ^ pts.length : ℕ) : ℝ) :=
          Nat.cast_le.mpr h
      _ = (pts.length : ℝ) * ((pts.length : ℝ) - 1)
          * (Fintype.card X : ℝ) ^ pts.length := hcast'
  have hsub : (1 : ℝ) - (((Fintype.card X).descFactorial pts.length : ℕ) : ℝ)
        / ((Fintype.card X : ℝ) ^ pts.length)
      = ((Fintype.card X : ℝ) ^ pts.length
          - (((Fintype.card X).descFactorial pts.length : ℕ) : ℝ))
        / ((Fintype.card X : ℝ) ^ pts.length) := by
    field_simp
  rw [hsub, div_le_div_iff₀ hNq (by positivity)]
  calc ((Fintype.card X : ℝ) ^ pts.length
        - (((Fintype.card X).descFactorial pts.length : ℕ) : ℝ)) * (2 * (Fintype.card X : ℝ))
      = 2 * (Fintype.card X : ℝ) * ((Fintype.card X : ℝ) ^ pts.length
        - (((Fintype.card X).descFactorial pts.length : ℕ) : ℝ)) := by ring
    _ ≤ (pts.length : ℝ) * ((pts.length : ℝ) - 1)
        * (Fintype.card X : ℝ) ^ pts.length := hB4

end OracleComp
