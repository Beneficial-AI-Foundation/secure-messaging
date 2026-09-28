/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Predicate query bounds under `simulateQ`

Two consequences of `IsQueryBoundP` for a stateful simulation:

* `simulateQ_run_add_inr_of_step` transfers a predicate query bound through an `add`
  handler whose left summand never matches the predicate;
* `support_state_measure_le_of_isQueryBoundP` bounds the growth of a state functional
  along any run by the query budget, given per-query growth bounds.
-/

open OracleSpec OracleComp

namespace OracleComp

universe u

/-- Query-bound transfer for an `add` handler whose left side never matches the predicate.

The proof delegates to `simulateQ_run_of_step`, so it requires
`[IsUniformSpec spec']` only for the base oracle. It does not require finite or
inhabited ranges for the adversary spec `spec₁ + spec₂`, so the adversary
interface may contain unbounded query-domain or response types. -/
theorem simulateQ_run_add_inr_of_step
    {ι₁ ι₂ ι' : Type u} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {spec' : OracleSpec ι'} [IsUniformSpec spec'] {σ α : Type u}
    {p : ι₁ ⊕ ι₂ → Prop} [DecidablePred p]
    {q : ι' → Prop} [DecidablePred q]
    {impl₁ : QueryImpl spec₁ (StateT σ (OracleComp spec'))}
    {impl₂ : QueryImpl spec₂ (StateT σ (OracleComp spec'))}
    {oa : OracleComp (spec₁ + spec₂) α} {n : ℕ}
    (hp_inl : ∀ t, ¬ p (.inl t))
    (h : IsQueryBoundP oa p n)
    (hstep_left : ∀ t s, IsQueryBoundP ((impl₁ t).run s) q 0)
    (hstep_p₂ : ∀ t, p (.inr t) → ∀ s, IsQueryBoundP ((impl₂ t).run s) q 1)
    (hstep_np₂ : ∀ t, ¬ p (.inr t) → ∀ s, IsQueryBoundP ((impl₂ t).run s) q 0)
    (s : σ) :
    IsQueryBoundP ((simulateQ (impl₁ + impl₂) oa).run s) q n :=
  IsQueryBoundP.simulateQ_run_of_step h
    (fun t hp s => by
      cases t with
      | inl t => exact absurd hp (hp_inl t)
      | inr t => exact hstep_p₂ t hp s)
    (fun t hnp s => by
      cases t with
      | inl t => exact hstep_left t s
      | inr t => exact hstep_np₂ t hnp s)
    s

/-- If a state functional `f` grows by at most one at every `p`-query and not at all at other
queries, then along any run in the support it grows by at most the `p`-query budget `n`. -/
theorem support_state_measure_le_of_isQueryBoundP
    {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (f : σ → ℕ)
    (p : ι → Prop) [DecidablePred p]
    (hstep_p : ∀ t, p t → ∀ s, ∀ z ∈ support ((impl t).run s), f z.2 ≤ f s + 1)
    (hstep_np : ∀ t, ¬ p t → ∀ s, ∀ z ∈ support ((impl t).run s), f z.2 ≤ f s)
    (oa : OracleComp spec α) (n : ℕ) (hq : oa.IsQueryBoundP p n) (s : σ) :
    ∀ z ∈ support ((simulateQ impl oa).run s), f z.2 ≤ f s + n := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure x =>
      intro z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simp
  | query_bind t oa ih =>
      intro z hz
      rw [isQueryBoundP_query_bind_iff] at hq
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨x, hx, hzx⟩ := hz
      have hrec := ih x.1 (if p t then n - 1 else n) (hq.2 x.1) x.2 z hzx
      by_cases hpt : p t
      · have h1 := hstep_p t hpt s x hx
        have h2 : 0 < n := hq.1.resolve_left (not_not_intro hpt)
        simp only [if_pos hpt] at hrec
        omega
      · have h1 := hstep_np t hpt s x hx
        simp only [if_neg hpt] at hrec
        omega

end OracleComp
