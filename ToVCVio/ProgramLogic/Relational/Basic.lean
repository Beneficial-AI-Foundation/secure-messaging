import VCVio.ProgramLogic.Relational.FromUnary

/-!
# Support-Refined Diagonal Triples

Helper lemmas for `RelTriple` between a computation and itself.  The plain
diagonal `relTriple_refl` forgets where the outputs come from; the variants
here keep membership in the support, which is what invariant-preservation
arguments consume.

Upstream candidates for `VCVio.ProgramLogic.Relational.Basic`.
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

end OracleComp.ProgramLogic.Relational
