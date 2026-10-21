/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Predicate query bounds under `simulateQ`

`IsQueryBoundP oa p n` says that every run of `oa` makes at most `n` queries `t` with
`p t`; queries not satisfying `p` are unrestricted.

`support_state_measure_le_of_isQueryBoundP`: let `f : σ → ℕ` be a measure on the
simulation state. If one step of `impl` raises `f` by at most `1` on a `p`-query
and does not raise it otherwise, then every final state `s'` in the support of
`(simulateQ impl oa).run s` satisfies `f s' ≤ f s + n`.
-/

open OracleSpec OracleComp

namespace OracleComp

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
        simp only [hpt, ↓reduceIte] at hrec
        omega
      · have h1 := hstep_np t hpt s x hx
        simp only [hpt, ↓reduceIte] at hrec
        omega

end OracleComp
