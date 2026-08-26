/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import VCVio.ProgramLogic.Relational.SimulateQ
import ToVCVio.EvalDist.Monad.Basic

/-!
# Sampled-Parameter Lemmas for Relational simulateQ

Convenience lemmas for sampled-parameter simulations and handler normalization.
VCVio provides the generic relational `simulateQ` rules and their `evalDist`
projections.

## Notation

`RelTriple oa ob R` is the relational Hoare-style triple with precondition
`True`: the two computations `oa` and `ob` are related so that their outputs
satisfy the postcondition `R`.

For a computation `oa`, `𝒟[oa]` denotes `evalDist oa`.

For stateful computations, `.run` returns both the output and final state,
while `.run'` returns only the output.

-/
open ToVCVio ENNReal OracleSpec OracleComp
open scoped OracleSpec.PrimitiveQuery

universe u

namespace OracleComp.ProgramLogic.Relational

variable {ι : Type u} {spec : OracleSpec ι}
variable {α : Type}

/-- Sampled-parameter passthrough for one `simulateQ` query. If the sampled
implementation `impl param` and the reference implementation `base` have the
same handler for the current query at state `s`, the reference handler reaches
only states satisfying `Inv`, and the continuation outputs agree from such
states, then the whole one-query program has the same output distribution with
the sampled implementation as with `base`. -/
theorem evalDist_sample_param_query_bind_passthrough
    {ι : Type} {spec : OracleSpec ι} {σ θ α : Type}
    (sample : ProbComp θ)
    (impl : θ → QueryImpl spec (StateT σ ProbComp))
    (base : QueryImpl spec (StateT σ ProbComp))
    (Inv : σ → Prop) (s : σ) (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α)
    (h_impl_eq : ∀ param, (impl param t).run s = (base t).run s)
    (h_preserves : ∀ p, p ∈ support ((base t).run s) → Inv p.2)
    (h_ih : ∀ (u : spec.Range t) (s' : σ), Inv s' →
      evalDist (do
        let param ← sample
        (simulateQ (impl param) (k u)).run' s') =
      evalDist ((simulateQ base (k u)).run' s')) :
    evalDist (do
      let param ← sample
      (simulateQ (impl param) (OracleSpec.query t >>= k)).run' s) =
    evalDist ((simulateQ base (OracleSpec.query t >>= k)).run' s) := by
  apply evalDist_ext
  intro y
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
    OracleQuery.input_query, StateT.run'_eq, StateT.run_bind, map_bind]
  have h_align : Pr[= y | do
        let param ← sample
        let p ← (impl param t).run s
        Prod.fst <$> (simulateQ (impl param) (k p.1)).run p.2] =
      Pr[= y | do
        let param ← sample
        let p ← (base t).run s
        Prod.fst <$> (simulateQ (impl param) (k p.1)).run p.2] := by
    refine probOutput_bind_congr' _ y fun param => ?_
    rw [h_impl_eq param]
  rw [h_align]
  rw [probOutput_bind_bind_swap (mx := sample) (my := (base t).run s)
    (f := fun param p =>
      Prod.fst <$> (simulateQ (impl param) (k p.1)).run p.2) (z := y)]
  refine probOutput_bind_congr ?_
  intro p hp_support
  have hi := h_ih p.1 p.2 (h_preserves p hp_support)
  simp only [StateT.run'_eq] at hi
  exact probOutput_eq_of_evalDist_eq hi y

/-- Normalize a sampled family of pure query handlers. If, for each sampled
parameter `param`, the handler for query `t` at state `s` is already the pure
answer/post-state pair `(out param, post param)`, then binding the handler result
and passing its components to the continuation has the same point probability as
passing `out param` and `post param` directly. -/
theorem probOutput_sample_param_handler_pure_eq
    {ι : Type} {spec : OracleSpec ι} {σ θ α : Type}
    (sample : ProbComp θ)
    (impl : θ → QueryImpl spec (StateT σ ProbComp))
    (s : σ) (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α)
    (out : θ → spec.Range t) (post : θ → σ)
    (h_run : ∀ param, (impl param t).run s = pure (out param, post param))
    (y : α) :
    Pr[= y | do
      let param ← sample
      let p ← (impl param t).run s
      Prod.fst <$> (simulateQ (impl param) (k p.1)).run p.2] =
    Pr[= y | do
      let param ← sample
      Prod.fst <$> (simulateQ (impl param) (k (out param))).run (post param)] := by
  refine probOutput_bind_congr' _ y fun param => ?_
  rw [h_run param]
  rfl

/-- Two-parameter version of `probOutput_sample_param_handler_pure_eq`. -/
theorem probOutput_sample_param₂_handler_pure_eq
    {ι : Type} {spec : OracleSpec ι} {σ θ₁ θ₂ α : Type}
    (sample₁ : ProbComp θ₁) (sample₂ : ProbComp θ₂)
    (impl : θ₁ → θ₂ → QueryImpl spec (StateT σ ProbComp))
    (s : σ) (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α)
    (out : θ₁ → θ₂ → spec.Range t) (post : θ₁ → θ₂ → σ)
    (h_run : ∀ param₁ param₂, (impl param₁ param₂ t).run s =
      pure (out param₁ param₂, post param₁ param₂))
    (y : α) :
    Pr[= y | do
      let param₁ ← sample₁
      let param₂ ← sample₂
      let p ← (impl param₁ param₂ t).run s
      Prod.fst <$> (simulateQ (impl param₁ param₂) (k p.1)).run p.2] =
    Pr[= y | do
      let param₁ ← sample₁
      let param₂ ← sample₂
      Prod.fst <$> (simulateQ (impl param₁ param₂)
        (k (out param₁ param₂))).run (post param₁ param₂)] := by
  refine probOutput_bind_congr' _ y fun param₁ => ?_
  refine probOutput_bind_congr' _ y fun param₂ => ?_
  rw [h_run param₁ param₂]
  rfl

/-- Three-parameter version of `probOutput_sample_param_handler_pure_eq`. -/
theorem probOutput_sample_param₃_handler_pure_eq
    {ι : Type} {spec : OracleSpec ι} {σ θ₁ θ₂ θ₃ α : Type}
    (sample₁ : ProbComp θ₁) (sample₂ : ProbComp θ₂) (sample₃ : ProbComp θ₃)
    (impl : θ₁ → θ₂ → θ₃ → QueryImpl spec (StateT σ ProbComp))
    (s : σ) (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α)
    (out : θ₁ → θ₂ → θ₃ → spec.Range t) (post : θ₁ → θ₂ → θ₃ → σ)
    (h_run : ∀ param₁ param₂ param₃, (impl param₁ param₂ param₃ t).run s =
      pure (out param₁ param₂ param₃, post param₁ param₂ param₃))
    (y : α) :
    Pr[= y | do
      let param₁ ← sample₁
      let param₂ ← sample₂
      let param₃ ← sample₃
      let p ← (impl param₁ param₂ param₃ t).run s
      Prod.fst <$> (simulateQ (impl param₁ param₂ param₃) (k p.1)).run p.2] =
    Pr[= y | do
      let param₁ ← sample₁
      let param₂ ← sample₂
      let param₃ ← sample₃
      Prod.fst <$> (simulateQ (impl param₁ param₂ param₃)
        (k (out param₁ param₂ param₃))).run (post param₁ param₂ param₃)] := by
  refine probOutput_bind_congr' _ y fun param₁ => ?_
  refine probOutput_bind_congr' _ y fun param₂ => ?_
  refine probOutput_bind_congr' _ y fun param₃ => ?_
  rw [h_run param₁ param₂ param₃]
  rfl

/-- **Normalize a handler that samples before returning a pure post-state.**

Let `impl : QueryImpl spec (StateT σ ProbComp)` be one oracle implementation.
If the handler for query `t`, when run at state `s`, is exactly
`do let param ← sample; pure (out param, post param)`, then the
point-probability term containing `let p ← (impl t).run s` can be rewritten by
exposing the same sample and substituting `p.1 = out param` and
`p.2 = post param`.

This is only a normalization lemma: it exposes the handler's internal sample;
it does not couple that sample to anything else. -/
theorem probOutput_handler_sample_pure_eq
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
    Pr[= y | do
      let p ← (impl t).run s
      Prod.fst <$> (simulateQ impl (k p.1)).run p.2] =
    Pr[= y | do
      let param ← sample
      Prod.fst <$> (simulateQ impl (k (out param))).run (post param)] := by
  have h_term_eq :
      (impl t).run s >>= (fun p => Prod.fst <$> (simulateQ impl (k p.1)).run p.2) =
      sample >>= fun param =>
        Prod.fst <$> (simulateQ impl (k (out param))).run (post param) := by
    rw [h_run]
    rw [bind_assoc]
    refine bind_congr fun param => ?_
    rw [pure_bind]
  exact probOutput_eq_of_evalDist_eq (congrArg evalDist h_term_eq) y

/-- Two-sample version of `probOutput_handler_sample_pure_eq`. -/
theorem probOutput_handler_sample₂_pure_eq
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
    Pr[= y | do
      let p ← (impl t).run s
      Prod.fst <$> (simulateQ impl (k p.1)).run p.2] =
    Pr[= y | do
      let param₁ ← sample₁
      let param₂ ← sample₂
      Prod.fst <$> (simulateQ impl (k (out param₁ param₂))).run
        (post param₁ param₂)] := by
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
  exact probOutput_eq_of_evalDist_eq (congrArg evalDist h_term_eq) y

end OracleComp.ProgramLogic.Relational
