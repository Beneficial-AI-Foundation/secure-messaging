/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.ProgramLogic.Unary.WP
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Expected-payoff bound for stateful simulation

The budget form `wp_simulateQ_run_le_budget` indexes the payoff by the number of counted queries
that remain, and the constant-allowance bound `wp_simulateQ_run_le` is derived from it.
-/

open OracleSpec ENNReal
open OracleComp.ProgramLogic

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {σ α : Type}

/-- Budget-indexed form of `wp_simulateQ_run_le`. Let:

- `impl : QueryImpl spec (StateT σ ProbComp)` be an implementation over states `σ`,
- `Inv : σ → Prop` be preserved by every `impl` query,
- `score k s : ℝ≥0∞` be a payoff indexed by the number `k` of queries satisfying `p` that
  remain available,
- `f : σ → ℝ≥0∞` be a final payoff with `f s ≤ score k s` whenever `Inv s`, for every `k`.

Assume that for every query `t`, budget `k` and state `s` with `Inv s`, the expected
`score k` of the state after `t` is at most `score (k + 1) s` if `p t` and at most
`score k s` otherwise. Then for every computation `oa` making at most `q` queries
satisfying `p` and every `s` with `Inv s`,

`E_{run oa from state s}[f] ≤ score q s.`

Unlike a constant allowance per query, the budget lets the charge of a `p`-query depend on
whether later `p`-queries remain. -/
lemma wp_simulateQ_run_le_budget
    (impl : QueryImpl spec (StateT σ ProbComp))
    (Inv : σ → Prop) (score : ℕ → σ → ℝ≥0∞)
    (p : ι → Prop) [DecidablePred p]
    (hpres : QueryImpl.PreservesInv impl Inv)
    (hstep : ∀ t k s, Inv s →
      wp ((impl t).run s) (fun z => score k z.2) ≤ score (if p t then k + 1 else k) s)
    (f : σ → ℝ≥0∞) (hf : ∀ k s, Inv s → f s ≤ score k s)
    (oa : OracleComp spec α) (q : ℕ) (hq : oa.IsQueryBoundP p q) :
    ∀ s, Inv s → wp ((simulateQ impl oa).run s) (fun z => f z.2) ≤ score q s := by
  induction oa using OracleComp.inductionOn generalizing q with
  | pure x =>
      intro s hs
      simpa only [simulateQ_pure, StateT.run_pure, ExactWPMonad.wp_pure] using hf q s hs
  | @query_bind t cont ih =>
      intro s hs
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hq
      obtain ⟨hcan, hcont⟩ := hq
      rw [simulateQ_query_bind, StateT.run_bind, wp_bind]
      -- The continuation runs with the remaining budget `q'`; a `p`-query uses one unit.
      set q' := if p t then q - 1 else q with hq'
      have hq'' : (if p t then q' + 1 else q') = q := by
        by_cases ht : p t
        · simp only [hq', ht, ↓reduceIte]
          exact Nat.sub_add_cancel (hcan.resolve_left (not_not_intro ht))
        · simp only [hq', ht, ↓reduceIte]
      calc
        wp ((impl t).run s)
            (fun z => wp ((simulateQ impl (cont z.1)).run z.2) (fun w => f w.2))
            ≤ wp ((impl t).run s) (fun z => score q' z.2) :=
          wp_mono_of_support _ fun z hz =>
            ih z.1 q' (hcont z.1) z.2 (hpres t s hs z hz)
        _ ≤ score (if p t then q' + 1 else q') s := hstep t q' s hs
        _ = score q s := by rw [hq'']

/-- Let:

- `impl : QueryImpl spec (StateT σ ProbComp)` be an implementation
  for oracles in `spec : OracleSpec ι`, over a state type `σ`,
- `Inv : σ → Prop` be a predicate on states,
- `score : σ → ℝ≥0∞` be a payoff function on states,
- `p : ι → Prop` be a predicate on the oracles in `spec`,
- `epsilon : ℝ≥0∞` be a fixed error bound,
- for any computation `X : ProbComp (β × σ)`, write
  `E_X[score] := wp X (fun z => score z.2)` for the expected
  score of `X`'s final state.

Assume:

(1) `Inv` is preserved by every `impl` query.
(2) For every oracle `t` and every state `s` satisfying `Inv s`:
- if `p t`, then `E_{(impl t).run s}[score] ≤ score s + epsilon`;
- otherwise, `E_{(impl t).run s}[score] ≤ score s`.

Then: for every computation `oa` making
at most `q` queries satisfying `p` and every state `s` satisfying `Inv s`, we have

`E_{run oa from state s}[score] ≤ score s + q · epsilon.` -/
lemma wp_simulateQ_run_le
    (impl : QueryImpl spec (StateT σ ProbComp))
    (Inv : σ → Prop) (score : σ → ℝ≥0∞)
    (p : ι → Prop) [DecidablePred p] (epsilon : ℝ≥0∞)
    (hpres : QueryImpl.PreservesInv impl Inv)
    (hstep : ∀ t s, Inv s →
      wp ((impl t).run s) (fun z => score z.2) ≤
        score s + if p t then epsilon else 0)
    (oa : OracleComp spec α) (q : ℕ) (hq : oa.IsQueryBoundP p q) :
    ∀ s, Inv s →
      wp ((simulateQ impl oa).run s) (fun z => score z.2) ≤
        score s + (q : ℝ≥0∞) * epsilon := by
  -- Budget `k` allows `k · epsilon` on top of the current score.
  refine wp_simulateQ_run_le_budget impl Inv (fun k s => score s + (k : ℝ≥0∞) * epsilon) p
    hpres (fun t k s hs => ?_) score (fun _ _ _ => le_self_add) oa q hq
  rw [wp_add, wp_const]
  refine (add_le_add (hstep t s hs) le_rfl).trans_eq ?_
  by_cases ht : p t
  · simp only [ht, ↓reduceIte, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    ac_rfl
  · simp only [ht, ↓reduceIte, add_zero]

/-- If every query preserves `Inv` and does not increase the expected score,
then an arbitrary adaptive computation does not increase it either.  No query
bound is needed. -/
lemma wp_simulateQ_run_le_of_nonincreasing
    (impl : QueryImpl spec (StateT σ ProbComp))
    (Inv : σ → Prop) (score : σ → ℝ≥0∞)
    (hpres : QueryImpl.PreservesInv impl Inv)
    (hstep : ∀ t s, Inv s →
      wp ((impl t).run s) (fun z => score z.2) ≤ score s)
    (oa : OracleComp spec α) :
    ∀ s, Inv s →
      wp ((simulateQ impl oa).run s) (fun z => score z.2) ≤ score s := by
  intro s hs
  have h := wp_simulateQ_run_le impl Inv score
    (fun _ => False) 0 hpres (by
      intro t s' hs'
      simpa using hstep t s' hs')
    oa 0 (isQueryBoundP_false oa 0) s hs
  simpa using h

end OracleComp
