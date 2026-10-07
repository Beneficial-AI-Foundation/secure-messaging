/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import VCVio.ProgramLogic.Relational.FromUnary

/-!
# Small `RelTriple` Helpers

Lemmas about `RelTriple` that VCVio's `VCVio/ProgramLogic/Relational/Basic.lean` does not yet
provide.

For `ProbComp` computations `A`, `B` and `C`:

* `relTriple_refl_support`: `RelTriple A A (fun a b => a = b ∧ a ∈ support A)`.
  Running `A` on both sides gives the same output, and that output is a possible output of `A`.
  This strengthens `relTriple_refl`.

* `relTriple_refl_support_post`: `RelTriple A A R` if `R a a` for every `a ∈ support A`.
  Running `A` on both sides, `R a a` only has to hold for outputs `a` that `A` can produce.

* `relTriple_map_map_of_pointwise`: `RelTriple (f <$> C) (g <$> C) R`
  if `R (f c) (g c)` for every `c`.
  Both sides share one run of `C`, so `R` only needs to hold for the pairs `(f c, g c)`.

* `relTriple_of_eq_map_map`: `RelTriple A B R`
  if `A = f <$> C`, `B = g <$> C` and `R (f c) (g c)` for every `c`.
  Same as the previous rule, with `A` and `B` given by equations.

For `A : OracleComp spec₁ α` and `B : OracleComp spec₂ β`, where both specs are
`IsUniformSpec`:

* `relTriple_of_eq_pure_pure`: `RelTriple A B R` if `A = pure a`, `B = pure b` and `R a b`.
  Computations that just return a value are related when their values are.

* `relTriple_eqRel_of_probOutput_true_eq`: `RelTriple A B (EqRel Bool)`
  if both return `Bool` and `Pr[= true | A] = Pr[= true | B]`.
  Games with the same success probability can be coupled to output the same bit.

Candidate for upstream VCVio, next to `relTriple_refl`, `relTriple_map`, `relTriple_pure_pure`
and `probOutput_true_eq_of_relTriple_eqRel` in that file.
-/

universe u v

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

/-- Let `oa` and `ob` be the images of a common computation `mx` under `f` and
`g`, and let `f a` and `g a` be `R`-related for every `a`. Then `oa` and `ob`
are `R`-related. -/
lemma relTriple_of_eq_map_map {α β γ : Type} {oa : ProbComp β} {ob : ProbComp γ}
    {mx : ProbComp α} {f : α → β} {g : α → γ} {R : β → γ → Prop}
    (hoa : oa = f <$> mx) (hob : ob = g <$> mx) (h : ∀ a, R (f a) (g a)) :
    RelTriple oa ob R :=
  hoa ▸ hob ▸ relTriple_map_map_of_pointwise mx f g h

section AnySpec

variable {ι₁ : Type u} {ι₂ : Type v} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
  [IsUniformSpec spec₁] [IsUniformSpec spec₂]

/-- Let `oa` and `ob` be the pure computations returning `a` and `b`, and let `a`
and `b` be `R`-related. Then `oa` and `ob` are `R`-related. -/
lemma relTriple_of_eq_pure_pure {α β : Type}
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {a : α} {b : β} {R : α → β → Prop}
    (hoa : oa = pure a) (hob : ob = pure b) (hR : R a b) :
    RelTriple oa ob R :=
  hoa ▸ hob ▸ relTriple_pure_pure hR

/-- Let `mx` and `my` be Boolean computations over uniform specs that output
`true` with equal probability. Then `mx` and `my` are related by output
equality. Neither can fail, so they also output `false` with equal probability.
Converse of upstream `probOutput_true_eq_of_relTriple_eqRel`. -/
lemma relTriple_eqRel_of_probOutput_true_eq
    {mx : OracleComp spec₁ Bool} {my : OracleComp spec₂ Bool}
    (h : Pr[= true | mx] = Pr[= true | my]) :
    RelTriple mx my (EqRel Bool) := by
  refine relTriple_eqRel_of_probOutput_eq fun x => ?_
  cases x
  · simp only [probOutput_false_eq_sub, probFailure_eq_zero, h]
  · exact h

end AnySpec

end OracleComp.ProgramLogic.Relational
