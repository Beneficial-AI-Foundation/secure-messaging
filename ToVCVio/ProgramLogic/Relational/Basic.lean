/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import VCVio.ProgramLogic.Relational.FromUnary

/-!
# Support-Refined Diagonal Triples

Helper lemmas for `RelTriple` between a computation and itself. VCVio's
`relTriple_refl` relates `mx` to itself by equality of outputs (`a = b`, the
diagonal). The variants here also record that the shared output lies in
`support mx`.

Also here: `relTriple_graph_of_evalDist_map_eq`, which turns a pushforward
equality `𝒟[f <$> mx] = 𝒟[my]` into a triple supported on the graph of `f`.
-/

open ENNReal OracleSpec OracleComp

namespace OracleComp.ProgramLogic.Relational

/-- Diagonal coupling refined by the support: a computation is related to
itself by equality of outputs together with membership in its support. -/
lemma relTriple_refl_support {α : Type} (mx : ProbComp α) :
    RelTriple mx mx (fun a b => a = b ∧ a ∈ support mx) := by
  rw [relTriple_iff_relWP, relWP_iff_couplingPost]
  refine ⟨_root_.SPMF.Coupling.refl (𝒟[mx]), ?_⟩
  intro z hz
  rcases (mem_support_bind_iff
    (𝒟[mx]) (fun a => (pure (a, a) : SPMF (α × α))) z).1 hz with
    ⟨a, ha, hz'⟩
  have hzEq : z = (a, a) := by
    simpa [support_pure, Set.mem_singleton_iff] using hz'
  subst hzEq
  have ha' : some a ∈ (𝒟[mx]).run.support := by
    rw [PMF.mem_support_iff]
    exact (SPMF.mem_support_iff (𝒟[mx]) a).1 ha
  exact ⟨rfl, mem_support_of_mem_support_evalDist mx a ha'⟩

/-- A triple between a computation and itself follows from the postcondition
holding on the diagonal of its support. -/
lemma relTriple_refl_support_post {α : Type} {mx : ProbComp α}
    {post : α → α → Prop} (h : ∀ a ∈ support mx, post a a) :
    RelTriple mx mx post := by
  refine relTriple_post_mono (relTriple_refl_support mx) ?_
  rintro p q ⟨rfl, hsup⟩
  exact h p hsup

/-- Mapping a single computation by two functions that are pointwise related
gives an `R`-triple of the two mapped computations.  Both sides share the draw
`mx`, so the outputs are perfectly correlated and `R (f a) (g a)` at each
sampled `a` suffices.  Taking `f := id` gives the map-right special case. -/
lemma relTriple_map_map_of_pointwise {α β γ : Type} (mx : ProbComp α)
    (f : α → β) (g : α → γ) {R : β → γ → Prop}
    (h : ∀ a, R (f a) (g a)) :
    RelTriple (f <$> mx) (g <$> mx) R :=
  relTriple_map (R := R) (relTriple_post_mono (relTriple_refl_support mx)
    (by rintro a b ⟨rfl, _⟩; exact h a))

/-- Let `h : 𝒟[f <$> mx] = 𝒟[my]`, i.e. `f x` for `x ← mx` has the same distribution as `my`.
Then `mx` and `my` have a coupling supported on the graph of `f`, that is, on pairs `(a, b)`
with `f a = b`. This is the converse of `evalDist_map_eq_of_relTriple` with `g := id`. -/
lemma relTriple_graph_of_evalDist_map_eq {α β : Type} {mx : ProbComp α} {my : ProbComp β}
    (f : α → β) (h : 𝒟[f <$> mx] = 𝒟[my]) :
    RelTriple mx my (fun a b => f a = b) :=
  relTriple_of_evalDist_eq_right h (by
    simpa using relTriple_map_map_of_pointwise mx id f (R := fun a b => f a = b) fun _ => rfl)

end OracleComp.ProgramLogic.Relational
