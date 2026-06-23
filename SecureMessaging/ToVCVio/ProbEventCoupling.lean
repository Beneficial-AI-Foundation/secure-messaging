/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# `probEvent` monotonicity from a coupling / relational triple (missing VCVio brick)

The Encrypt-then-MAC authenticity hop relates the *forge event* of two different oracle
experiments running the same adversary: an instrumented game (`authInstImpl`) whose bad flag is
set on every successful non-challenge decrypt, and a forgery reduction (`forgeReduction` under
`forgeImpl`) whose flag is set on a successful verify at a not-eval'd point. The two flags live
in *different* state spaces, so we cannot relate them by a plain distribution equality — only by
an *implication on the support of a coupling*.

This file isolates the generic probabilistic bridge: given a coupling between the output-state
distributions of two computations (e.g. produced by VCVio's `relTriple_simulateQ_run`), if the
coupled output pairs satisfy a relation `R` and `R` forces the source event to imply the target
event, then the source event probability is at most the target event probability.

## Main result

* `probEvent_le_of_couplingPost` — coupling-level statement (any two `OracleComp`s).
* `probEvent_snd_le_of_relTriple` — the state-event corollary used by the EtM auth hop: from a
  `RelTriple` whose postcondition relates the final *states*, transport an implication between
  state predicates into a `probEvent ≤ probEvent` between the two `simulateQ` runs.

Both are generic facts about `OracleComp`/`SPMF` couplings, independent of `SecureMessaging`.
TODO(upstream): contribute alongside `VCVio.ProgramLogic.Relational`.
-/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

namespace ToVCVio

variable {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
  [IsUniformSpec spec₁] [IsUniformSpec spec₂]
  {α β : Type}

/-- **`probEvent` monotonicity from a coupling postcondition.**

If `oa` and `ob` admit a coupling whose support satisfies `R`, and `R a b` forces `p a → q b`,
then `Pr[p | oa] ≤ Pr[q | ob]`.

The proof routes both probabilities through the coupling SPMF `c`: its first marginal is `𝒟[oa]`
and its second marginal is `𝒟[ob]`, so `Pr[p | oa] = Pr[p ∘ fst | c]` and
`Pr[q | ob] = Pr[q ∘ snd | c]`; the support implication then gives `probEvent_mono`. -/
theorem probEvent_le_of_couplingPost
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {R : α → β → Prop}
    (h : CouplingPost oa ob R)
    {p : α → Prop} {q : β → Prop}
    (himp : ∀ a b, R a b → p a → q b) :
    Pr[p | oa] ≤ Pr[q | ob] := by
  obtain ⟨c, hc⟩ := h
  -- Rewrite both event probabilities as events on the coupling `c`, via its marginals.
  -- `Pr[· | oa] = Pr[· | 𝒟[oa]]` definitionally, and `𝒟[oa] = Prod.fst <$> c.1`.
  have hfst : Pr[p | oa] = Pr[(p ∘ Prod.fst) | c.1] := by
    have hm : Pr[p | (𝒟[oa] : SPMF α)] = Pr[p | (Prod.fst <$> c.1 : SPMF α)] := by
      rw [c.2.map_fst]
    rw [show Pr[p | oa] = Pr[p | (𝒟[oa] : SPMF α)] from rfl, hm, probEvent_map]
  have hsnd : Pr[q | ob] = Pr[(q ∘ Prod.snd) | c.1] := by
    have hm : Pr[q | (𝒟[ob] : SPMF β)] = Pr[q | (Prod.snd <$> c.1 : SPMF β)] := by
      rw [c.2.map_snd]
    rw [show Pr[q | ob] = Pr[q | (𝒟[ob] : SPMF β)] from rfl, hm, probEvent_map]
  rw [hfst, hsnd]
  refine probEvent_mono ?_
  intro z hz hpz
  exact himp z.1 z.2 (hc z hz) hpz

/-- **State-event monotonicity from a relational `simulateQ` triple.**

If simulating the *same* adversary `oa` with two `StateT`-valued implementations (over base
oracles `spec₁`/`spec₂`) is related by a `RelTriple` whose postcondition equates the outputs and
relates the final states by `R_state`, and `R_state` forces a source state predicate `flag₁` to
imply a target state predicate `flag₂`, then the probability of `flag₁` on the source run is at
most the probability of `flag₂` on the target run.

This is the exact shape consumed by the EtM authenticity hop: `flag₁` = "instrumented game's bad
flag set", `flag₂` = "forge experiment's `forged` flag set". -/
theorem probEvent_snd_le_of_relTriple
    {ι : Type} {spec : OracleSpec ι}
    {σ₁ σ₂ : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec₁)))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec₂)))
    (R_state : σ₁ → σ₂ → Prop)
    (oa : OracleComp spec α)
    (himpl : ∀ (t : spec.Domain) (s₁ : σ₁) (s₂ : σ₂),
      R_state s₁ s₂ →
      RelTriple ((impl₁ t).run s₁) ((impl₂ t).run s₂)
        (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_state p₁.2 p₂.2))
    (s₁ : σ₁) (s₂ : σ₂) (hs : R_state s₁ s₂)
    {flag₁ : σ₁ → Prop} {flag₂ : σ₂ → Prop}
    (himp : ∀ a b, R_state a b → flag₁ a → flag₂ b) :
    Pr[fun z : α × σ₁ => flag₁ z.2 | (simulateQ impl₁ oa).run s₁] ≤
      Pr[fun z : α × σ₂ => flag₂ z.2 | (simulateQ impl₂ oa).run s₂] := by
  have hrel := relTriple_simulateQ_run impl₁ impl₂ R_state oa himpl s₁ s₂ hs
  refine probEvent_le_of_couplingPost
    (R := fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_state p₁.2 p₂.2)
    ((relTriple_iff_relWP).1 hrel) ?_
  rintro ⟨a, sa⟩ ⟨b, sb⟩ ⟨-, hR⟩ hflag
  exact himp sa sb hR hflag

end ToVCVio
