/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
import VCVio.ProgramLogic.Relational.SimulateQ
import ToVCVio.EvalDist.Monad.Basic

/-!
# Sampled-Parameter Lemmas for Relational simulateQ

Convenience lemmas for sampled-parameter simulations and handler normalization.
VCVio provides the generic relational `simulateQ` rules and their
distributional projections.

## Notation

`RelTriple oa ob R` is the relational Hoare-style triple with precondition
`True`: the two computations `oa` and `ob` are related so that their outputs
satisfy the postcondition `R`.

`oa =ᵈ ob` states that `oa` and `ob` are equal in distribution: every event has the same
probability under both.

For stateful computations, `.run` returns both the output and final state,
while `.run'` returns only the output.

-/
open ToVCVio ENNReal OracleSpec OracleComp
open scoped OracleSpec.PrimitiveQuery

universe u

namespace OracleComp.ProgramLogic.Relational

variable {ι : Type u} {spec : OracleSpec ι}
variable {α : Type}

/-- One query of a sampled-parameter simulation can be answered by a fixed reference handler.

Let `impl` be a family of stateful query handlers indexed by `param : θ`, let `base` be a
reference handler and let `sample : ProbComp θ`. Fix an initial state `s`, a query `t` and a
continuation `k`. Assume that
* (`h_impl_eq`) for every `param`, one call of `impl param t` from `s` is the same computation
  as `base t` from `s`;
* (`h_preserves`) every next state that `base t` can reach from `s` satisfies `Inv`;
* (`h_ih`) for every answer `u` and every state `s'` satisfying `Inv`, drawing
  `param ← sample` and simulating `k u` under `impl param` from `s'` gives the same output
  distribution as simulating `k u` under `base` from `s'`.

Then drawing `param ← sample` and simulating `query t >>= k` under `impl param` from `s` gives
the same output distribution as simulating it under `base` from `s`. -/
theorem evalDistEq_sample_param_query_bind_passthrough
    {ι : Type} {spec : OracleSpec ι} {σ θ α : Type}
    (sample : ProbComp θ)
    (impl : θ → QueryImpl spec (StateT σ ProbComp))
    (base : QueryImpl spec (StateT σ ProbComp))
    (Inv : σ → Prop) (s : σ) (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α)
    (h_impl_eq : ∀ param, (impl param t).run s = (base t).run s)
    (h_preserves : ∀ p, p ∈ support ((base t).run s) → Inv p.2)
    (h_ih : ∀ (u : spec.Range t) (s' : σ), Inv s' →
      (do
        let param ← sample
        (simulateQ (impl param) (k u)).run' s') =ᵈ
      (simulateQ base (k u)).run' s') :
    (do
      let param ← sample
      (simulateQ (impl param) (OracleSpec.query t >>= k)).run' s) =ᵈ
    (simulateQ base (OracleSpec.query t >>= k)).run' s := by
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
    OracleQuery.input_query, StateT.run'_eq, StateT.run_bind, map_bind, h_impl_eq]
  refine (EvalDistEq.bind_bind_swap sample ((base t).run s) _).trans ?_
  refine EvalDistEq.bind_congr_of_support _ fun p hp => ?_
  simpa only [StateT.run'_eq] using h_ih p.1 p.2 (h_preserves p hp)

/-- A parameter that does not affect the handlers' distributions can be fixed instead of sampled.

Let `impl` be a family of stateful query handlers indexed by `param : θ`, and let `x₀ : θ`.
Assume (`h`) that for every `param`, query `t` and state `s'`, one call of `impl param t` from
`s'` is equal in distribution, as a pair of answer and next state, to `impl x₀ t`. Then, from any
initial state `s`, drawing `param ← $ᵗ θ` and simulating `oa` under `impl param` is equal in
distribution to simulating `oa` under `impl x₀`. -/
theorem evalDistEq_sample_simulateQ_run'_of_param_indep
    {ι : Type} {spec : OracleSpec ι} {σ θ α : Type} [SampleableType θ]
    (impl : θ → QueryImpl spec (StateT σ ProbComp))
    (oa : OracleComp spec α) (s : σ) (x₀ : θ)
    (h : ∀ param t s', (impl param t).run s' =ᵈ (impl x₀ t).run s') :
    (do
      let param ← $ᵗ θ
      (simulateQ (impl param) oa).run' s) =ᵈ
    (simulateQ (impl x₀) oa).run' s :=
  (EvalDistEq.bind_right _ fun param => evalDistEq_of_relTriple_eqRel
    (relTriple_simulateQ_run'_of_impl_evalDistEq _ _ oa (h param) s s rfl)).trans
      (EvalDistEq.bind_const _ _)

/-- A deterministic handler call can be skipped after two parameter draws.

If (`h_run`) for every `param₁ param₂`

    (impl param₁ param₂ t).run s = pure (out param₁ param₂, post param₁ param₂),

then `Pr{let x ← P}[x = y] = Pr{let x ← Q}[x = y]`, where `P` makes the call to the oracle and
`Q` uses its result directly. -/
theorem prEvent_sample_param₂_handler_pure_eq
    {ι : Type} {spec : OracleSpec ι} {σ θ₁ θ₂ α : Type}
    (sample₁ : ProbComp θ₁) (sample₂ : ProbComp θ₂)
    (impl : θ₁ → θ₂ → QueryImpl spec (StateT σ ProbComp))
    (s : σ) (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α)
    (out : θ₁ → θ₂ → spec.Range t) (post : θ₁ → θ₂ → σ)
    (h_run : ∀ param₁ param₂, (impl param₁ param₂ t).run s =
      pure (out param₁ param₂, post param₁ param₂))
    (y : α) :
    Pr{let x ← (do
      let param₁ ← sample₁
      let param₂ ← sample₂
      let p ← (impl param₁ param₂ t).run s
      Prod.fst <$> (simulateQ (impl param₁ param₂) (k p.1)).run p.2)}[x = y] =
    Pr{let x ← (do
      let param₁ ← sample₁
      let param₂ ← sample₂
      Prod.fst <$> (simulateQ (impl param₁ param₂)
        (k (out param₁ param₂))).run (post param₁ param₂))}[x = y] := by
  simp only [h_run, pure_bind]

/-- Three-parameter version of `prEvent_sample_param₂_handler_pure_eq`. -/
theorem prEvent_sample_param₃_handler_pure_eq
    {ι : Type} {spec : OracleSpec ι} {σ θ₁ θ₂ θ₃ α : Type}
    (sample₁ : ProbComp θ₁) (sample₂ : ProbComp θ₂) (sample₃ : ProbComp θ₃)
    (impl : θ₁ → θ₂ → θ₃ → QueryImpl spec (StateT σ ProbComp))
    (s : σ) (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α)
    (out : θ₁ → θ₂ → θ₃ → spec.Range t) (post : θ₁ → θ₂ → θ₃ → σ)
    (h_run : ∀ param₁ param₂ param₃, (impl param₁ param₂ param₃ t).run s =
      pure (out param₁ param₂ param₃, post param₁ param₂ param₃))
    (y : α) :
    Pr{let x ← (do
      let param₁ ← sample₁
      let param₂ ← sample₂
      let param₃ ← sample₃
      let p ← (impl param₁ param₂ param₃ t).run s
      Prod.fst <$> (simulateQ (impl param₁ param₂ param₃) (k p.1)).run p.2)}[x = y] =
    Pr{let x ← (do
      let param₁ ← sample₁
      let param₂ ← sample₂
      let param₃ ← sample₃
      Prod.fst <$> (simulateQ (impl param₁ param₂ param₃)
        (k (out param₁ param₂ param₃))).run (post param₁ param₂ param₃))}[x = y] := by
  simp only [h_run, pure_bind]

/-- **Normalize a handler that samples before returning a pure post-state.**

Let `impl : QueryImpl spec (StateT σ ProbComp)` be one oracle implementation.
If the handler for query `t`, when run at state `s`, is exactly
`do let param ← sample; pure (out param, post param)`, then the
point-probability term containing `let p ← (impl t).run s` can be rewritten by
exposing the same sample and substituting `p.1 = out param` and
`p.2 = post param`.

This is only a normalization lemma: it exposes the handler's internal sample;
it does not couple that sample to anything else. -/
theorem prEvent_handler_sample_pure_eq
    {ι : Type} {spec : OracleSpec ι} {σ θ α : Type}
    (sample : ProbComp θ)
    (impl : QueryImpl spec (StateT σ ProbComp))
    (s : σ) (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α)
    (out : θ → spec.Range t) (post : θ → σ)
    (h_run : (impl t).run s = do
      let param ← sample
      pure (out param, post param))
    (y : α) :
    Pr{let x ← (do
      let p ← (impl t).run s
      Prod.fst <$> (simulateQ impl (k p.1)).run p.2)}[x = y] =
    Pr{let x ← (do
      let param ← sample
      Prod.fst <$> (simulateQ impl (k (out param))).run (post param))}[x = y] := by
  have h_term_eq :
      (impl t).run s >>= (fun p => Prod.fst <$> (simulateQ impl (k p.1)).run p.2) =
      sample >>= fun param =>
        Prod.fst <$> (simulateQ impl (k (out param))).run (post param) := by
    rw [h_run]
    rw [bind_assoc]
    refine bind_congr fun param => ?_
    rw [pure_bind]
  rw [h_term_eq]

/-- Two-sample version of `prEvent_handler_sample_pure_eq`. -/
theorem prEvent_handler_sample₂_pure_eq
    {ι : Type} {spec : OracleSpec ι} {σ θ₁ θ₂ α : Type}
    (sample₁ : ProbComp θ₁) (sample₂ : ProbComp θ₂)
    (impl : QueryImpl spec (StateT σ ProbComp))
    (s : σ) (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α)
    (out : θ₁ → θ₂ → spec.Range t) (post : θ₁ → θ₂ → σ)
    (h_run : (impl t).run s = do
      let param₁ ← sample₁
      let param₂ ← sample₂
      pure (out param₁ param₂, post param₁ param₂))
    (y : α) :
    Pr{let x ← (do
      let p ← (impl t).run s
      Prod.fst <$> (simulateQ impl (k p.1)).run p.2)}[x = y] =
    Pr{let x ← (do
      let param₁ ← sample₁
      let param₂ ← sample₂
      Prod.fst <$> (simulateQ impl (k (out param₁ param₂))).run
        (post param₁ param₂))}[x = y] := by
  have h_term_eq :
      (impl t).run s >>= (fun p => Prod.fst <$> (simulateQ impl (k p.1)).run p.2) =
      sample₁ >>= fun param₁ =>
        sample₂ >>= fun param₂ =>
          Prod.fst <$> (simulateQ impl (k (out param₁ param₂))).run
            (post param₁ param₂) := by
    rw [h_run]
    rw [bind_assoc]
    refine bind_congr fun param₁ => ?_
    rw [bind_assoc]
    refine bind_congr fun param₂ => ?_
    rw [pure_bind]
  rw [h_term_eq]

end OracleComp.ProgramLogic.Relational
