/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.Constructions.SampleableType
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.FinRange

/-!
# Fixed-list PRP/PRF switching infrastructure

Applying a uniformly random permutation `π : Equiv.Perm X` to a fixed list `pts` of
pairwise-distinct points is equal in distribution to drawing `pts.length` points of `X`
without replacement (`OracleComp.evalDist_map_uniformPerm_eq_uniformDistinct`). This is the
identity that lets a proof consume a random-permutation experiment without ever counting the
`(card X)!` permutations: post-composition by permutations acts transitively on the
duplicate-free lists of a given length (`List.exists_perm_map_eq`), and a distribution
invariant under a transitive action is uniform.

Only this non-adaptive, fixed-list form is provided; the adaptive lazy random-permutation
simulator of the textbook switching lemma is not built here, since the reductions that use
this file query the permutation on a fixed list of points. Candidate for upstream VCVio.
-/

open ENNReal OracleComp

namespace List

/-- Some permutation of a finite type carries any duplicate-free list onto any other of the
same length: post-composition acts transitively on such lists. -/
theorem exists_perm_map_eq {X : Type} [Finite X]
    (l l' : List X) (hl : l.Nodup) (hl' : l'.Nodup) (hlen : l.length = l'.length) :
    ∃ σ : Equiv.Perm X, l.map σ = l' := by
  letI : DecidableEq X := Classical.decEq X
  letI : Fintype X := Fintype.ofFinite X
  let e : {x // x ∈ l} ≃ {x // x ∈ l'} :=
    (hl.getEquiv l).symm.trans ((finCongr hlen).trans (hl'.getEquiv l'))
  refine ⟨Equiv.extendSubtype e, ?_⟩
  refine List.ext_getElem (by simpa using hlen) ?_
  intro i h₁ h₂
  have h₁' : i < l.length := by simpa using h₁
  have hmem : l[i] ∈ l := List.getElem_mem _
  simp only [List.getElem_map]
  rw [Equiv.extendSubtype_apply_of_mem e l[i] hmem]
  have hidx : List.idxOf l[i] l = i := hl.idxOf_getElem i h₁'
  simp [e, List.Nodup.getEquiv, finCongr, hidx]

end List

namespace OracleComp

/-- A computation with full support and the same probability at every output is the uniform
sample. -/
theorem evalDist_eq_uniformSample_of_uniform {β : Type} [SampleableType β]
    (oa : ProbComp β) (hsupp : ∀ x : β, x ∈ support oa)
    (huni : ∀ x y : β, Pr[= x | oa] = Pr[= y | oa]) :
    evalDist oa = evalDist ($ᵗ β) := by
  letI : Fintype β := Fintype.ofFinite β
  refine evalDist_ext fun x => ?_
  have h2 : Pr[= x | ($ᵗ β)] = (Fintype.card β : ℝ≥0∞)⁻¹ :=
    probOutput_uniformSample β x
  letI h : SampleableType β := ⟨oa, hsupp, huni⟩
  have h1 : Pr[= x | oa] = (Fintype.card β : ℝ≥0∞)⁻¹ :=
    probOutput_uniformSample (hα := h) β x
  exact h1.trans h2.symm

/-- A duplicate-free list of length `q` is an embedding `Fin q ↪ X`; this is how callers of
`sampleDistinctFrom` discharge its `Nonempty` argument. -/
theorem nonempty_embedding_of_nodup {X : Type} (pts : List X) (hpts : pts.Nodup) :
    Nonempty (Fin pts.length ↪ X) :=
  ⟨⟨fun i => pts[i], fun i j hij => Fin.ext (hpts.getElem_inj_iff.mp hij)⟩⟩

/-- The embedding `Fin pts.length ↪ X`, `i ↦ pts[i]`, given by a duplicate-free list. -/
def nodupEmbedding {X : Type} (pts : List X) (hpts : pts.Nodup) : Fin pts.length ↪ X :=
  ⟨fun i => pts[i], fun i j hij => Fin.ext (hpts.getElem_inj_iff.mp hij)⟩

/-- Drawing `q` points of `X` without replacement: a uniform injective `q`-tuple, as a list.

`hq` is an explicit argument rather than an instance because `Nonempty (Fin q ↪ X)` holds only
when `q ≤ Fintype.card X`, so it cannot be a global instance. -/
def sampleDistinctFrom (X : Type) [FinEnum X] (q : ℕ)
    (hq : Nonempty (Fin q ↪ X)) : ProbComp (List X) :=
  letI := hq
  (fun e : Fin q ↪ X => List.ofFn e) <$> ($ᵗ (Fin q ↪ X) : ProbComp (Fin q ↪ X))

/-- `List.exists_perm_map_eq` for embeddings: some permutation of the target carries one
embedding `Fin q ↪ X` onto another. -/
theorem exists_perm_comp_embedding_eq {X : Type} [Finite X] {q : ℕ}
    (e e' : Fin q ↪ X) : ∃ σ : Equiv.Perm X, ∀ i, σ (e i) = e' i := by
  -- `DecidableEq X` is supplied explicitly rather than by `classical`: instance search for
  -- `DecidableEq X` from a bare `Finite X`/`FinEnum X` context times out at 20000 synthesis
  -- heartbeats in this build, and `classical`'s `Classical.propDecidable` is low priority, so
  -- the search would still be attempted first.
  letI : DecidableEq X := Classical.decEq X
  letI : Fintype X := Fintype.ofFinite X
  obtain ⟨σ, hσ⟩ := List.exists_perm_map_eq (List.ofFn e) (List.ofFn e')
    (List.nodup_ofFn_ofInjective e.injective) (List.nodup_ofFn_ofInjective e'.injective)
    (by simp)
  refine ⟨σ, ?_⟩
  have : (fun i => σ (e i)) = fun i => e' i := by
    refine List.ofFn_inj.mp ?_
    simpa [List.map_ofFn, Function.comp_def] using hσ
  exact fun i => congrFun this i

/-- Post-composing a uniform permutation onto a fixed embedding gives a uniform embedding.
The pushed-forward law is invariant under post-composition by every `σ`, and that action is
transitive (`exists_perm_comp_embedding_eq`), so the law is uniform; no permutation is ever
counted. -/
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
  refine evalDist_eq_uniformSample_of_uniform _ ?_ ?_
  · -- Full support: transitivity of the action hits every embedding.
    intro e'
    obtain ⟨σ, hσ⟩ := exists_perm_comp_embedding_eq e₀ e'
    rw [support_map, support_uniformSample]
    exact ⟨σ, Set.mem_univ σ, Function.Embedding.ext fun i => hσ i⟩
  · -- Pointwise uniformity: transport the mass along the transitive action.
    intro e e'
    obtain ⟨σ, hσ⟩ := exists_perm_comp_embedding_eq e e'
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

/-- Applying a uniform permutation of `X` to a fixed list `pts` of pairwise-distinct points is
equal in distribution to drawing `pts.length` points of `X` without replacement. -/
theorem evalDist_map_uniformPerm_eq_uniformDistinct {X : Type} [FinEnum X]
    (pts : List X) (hpts : pts.Nodup) :
    evalDist ((fun π : Equiv.Perm X => pts.map π) <$>
        ($ᵗ (Equiv.Perm X) : ProbComp (Equiv.Perm X)))
      = evalDist (sampleDistinctFrom X pts.length (nonempty_embedding_of_nodup pts hpts)) := by
  haveI hq : Nonempty (Fin pts.length ↪ X) := nonempty_embedding_of_nodup pts hpts
  have hfun : ∀ π : Equiv.Perm X,
      pts.map π = List.ofFn ((nodupEmbedding pts hpts).trans π.toEmbedding) := by
    intro π
    rw [← List.ofFn_getElem_eq_map pts (π : X → X)]
    rfl
  have hRHS : sampleDistinctFrom X pts.length (nonempty_embedding_of_nodup pts hpts)
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

end OracleComp
