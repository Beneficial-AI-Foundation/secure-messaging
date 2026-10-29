/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Sampling a key at the query that uses it

A stateful oracle implementation `impl k` depends on a key `k ← keygen`. The game samples `k`
before the adversary runs. If at most one query reads `k`, the key can instead be sampled inside
that query. `impl'` is the implementation that does so.

The predicate `fresh` on the state says that no query has read the key yet. Three conditions
make the two games equal in distribution:

* In a fresh state, each query either does not read the key and keeps the state fresh, or reads
  the key and leaves the state not fresh. A query of the second kind behaves like the
  corresponding `impl'` query once the key sample is moved inside it.
* In a state that is not fresh, `impl k` and `impl'` agree for every key `k`.
* A state that is not fresh stays not fresh.
-/

open OracleSpec OracleComp

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {K σ : Type}

/-- Let `fresh s` say that no query has read the key in state `s`, and let `impl k` and `impl'`
agree on every state that is not fresh, which stays not fresh. Then, from a state that is not
fresh, `impl k` and `impl'` give the same run for every key `k`. -/
theorem run_simulateQ_eq_of_not_fresh
    (impl : K → QueryImpl spec (StateT σ ProbComp)) (impl' : QueryImpl spec (StateT σ ProbComp))
    (fresh : σ → Prop)
    (h_eq : ∀ t s k, ¬ fresh s → (impl k t).run s = (impl' t).run s)
    (h_pres : ∀ t s k, ¬ fresh s → ∀ y ∈ support ((impl k t).run s), ¬ fresh y.2)
    {α : Type} (oa : OracleComp spec α) (s : σ) (hs : ¬ fresh s) (k : K) :
    (simulateQ (impl k) oa).run s = (simulateQ impl' oa).run s := by
  have h := map_run_simulateQ_eq_of_query_map_eq_inv' (impl k) impl' (fun s => ¬ fresh s) id
    (fun t s hs => h_pres t s k hs)
    (fun t s hs => by rw [Prod.map_id, id_map]; exact h_eq t s k hs) oa s hs
  rwa [Prod.map_id, id_map] at h

/-- Let `keygen` sample the key, and let `impl k` read the key in at most one query, as stated
by the hypotheses on `fresh`. Let `impl'` sample the key inside that query instead. Then, from a
fresh state, running the adversary against `impl k` for `k ← keygen` and against `impl'` gives
the same distribution of outputs and final states. -/
theorem keygen_bind_run_simulateQ_evalDistEq
    (keygen : ProbComp K)
    (impl : K → QueryImpl spec (StateT σ ProbComp)) (impl' : QueryImpl spec (StateT σ ProbComp))
    (fresh : σ → Prop)
    (h_fresh : ∀ t s, fresh s →
      ((∀ k, (impl k t).run s = (impl' t).run s) ∧
          ∀ y ∈ support ((impl' t).run s), fresh y.2) ∨
        ((keygen >>= fun k => (impl k t).run s) =ᵈ (impl' t).run s ∧
          ∀ k, ∀ y ∈ support ((impl k t).run s), ¬ fresh y.2))
    (h_eq : ∀ t s k, ¬ fresh s → (impl k t).run s = (impl' t).run s)
    (h_pres : ∀ t s k, ¬ fresh s → ∀ y ∈ support ((impl k t).run s), ¬ fresh y.2)
    {α : Type} (oa : OracleComp spec α) (s : σ) (hs : fresh s) :
    (keygen >>= fun k => (simulateQ (impl k) oa).run s) =ᵈ (simulateQ impl' oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact EvalDistEq.bind_const keygen _
  | query_bind t cont ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    rcases h_fresh t s hs with ⟨hk, hp⟩ | ⟨hd, hn⟩
    · -- The query does not read the key: swap it in front of `keygen`, then use `ih`.
      simp only [hk]
      exact (EvalDistEq.bind_bind_swap _ _ _).trans
        (EvalDistEq.bind_congr_of_support _ fun y hy => ih y.1 y.2 (hp y hy))
    · -- The query reads the key: afterwards `impl k` and `impl'` agree.
      have hrest : ∀ k, ∀ y ∈ support ((impl k t).run s),
          (simulateQ (impl k) (cont y.1)).run y.2 = (simulateQ impl' (cont y.1)).run y.2 :=
        fun k y hy => run_simulateQ_eq_of_not_fresh impl impl' fresh h_eq h_pres _ _ (hn k y hy) k
      refine (EvalDistEq.bind_congr_of_support _ fun k _ =>
        EvalDistEq.bind_congr_of_support _ fun y hy => by rw [hrest k y hy]).trans ?_
      simp only [← bind_assoc]
      exact hd.bind_left _

end OracleComp
