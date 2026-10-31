/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.ProgramLogic.Unary.WP
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv

/-!
# Query-wise facts over a sum of stateful implementations

Let `i₁ : QueryImpl spec₁ (StateT σ ProbComp)` and `i₂ : QueryImpl spec₂ (StateT σ ProbComp)`.
A query to `i₁ + i₂` is a query to `i₁` or to `i₂`. So a property of one query that holds for
every query of `i₁` and every query of `i₂` holds for every query of `i₁ + i₂`. This module states
this for the step properties used in hybrid arguments: a counter bound, a relation between the
states before and after a query, an equality of runs, a projection of the state, and an
expected-payoff bound.
-/

open OracleSpec ENNReal
open OracleComp.ProgramLogic

namespace OracleComp

variable {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {σ : Type}

/-- Query-wise counter bounds combine over a sum of implementations: the counter never decreases,
and it increases by at most one exactly on the queries selected by `Sum.elim p₁ p₂`. -/
theorem countStep_add (count : σ → ℕ)
    {i₁ : QueryImpl spec₁ (StateT σ ProbComp)} {i₂ : QueryImpl spec₂ (StateT σ ProbComp)}
    (p₁ : ι₁ → Bool) (p₂ : ι₂ → Bool)
    (h₁ : ∀ t s z, z ∈ support ((i₁ t).run s) →
      count s ≤ count z.2 ∧ count z.2 ≤ count s + if p₁ t then 1 else 0)
    (h₂ : ∀ t s z, z ∈ support ((i₂ t).run s) →
      count s ≤ count z.2 ∧ count z.2 ≤ count s + if p₂ t then 1 else 0) :
    ∀ t s z, z ∈ support (((i₁ + i₂) t).run s) →
      count s ≤ count z.2 ∧ count z.2 ≤ count s + if Sum.elim p₁ p₂ t then 1 else 0
  | .inl t, s, z, hz => h₁ t s z hz
  | .inr t, s, z, hz => h₂ t s z hz

/-- Query-wise step relations combine over a sum of oracle implementations. -/
theorem relStep_add (R : σ → σ → Prop) {i₁ : QueryImpl spec₁ (StateT σ ProbComp)}
    {i₂ : QueryImpl spec₂ (StateT σ ProbComp)}
    (h₁ : ∀ t s z, z ∈ support ((i₁ t).run s) → R s z.2)
    (h₂ : ∀ t s z, z ∈ support ((i₂ t).run s) → R s z.2) :
    ∀ t s z, z ∈ support (((i₁ + i₂) t).run s) → R s z.2
  | .inl t, s, z, hz => h₁ t s z hz
  | .inr t, s, z, hz => h₂ t s z hz

/-- Query-wise equality, or commitment of both outcomes, combine over a sum of implementations. -/
theorem queryEqOr_add (Inv C : σ → Prop) {i₁ j₁ : QueryImpl spec₁ (StateT σ ProbComp)}
    {i₂ j₂ : QueryImpl spec₂ (StateT σ ProbComp)}
    (h₁ : ∀ t s, Inv s → (i₁ t).run s = (j₁ t).run s ∨
      ((∀ z ∈ support ((i₁ t).run s), C z.2) ∧ ∀ z ∈ support ((j₁ t).run s), C z.2))
    (h₂ : ∀ t s, Inv s → (i₂ t).run s = (j₂ t).run s ∨
      ((∀ z ∈ support ((i₂ t).run s), C z.2) ∧ ∀ z ∈ support ((j₂ t).run s), C z.2)) :
    ∀ t s, Inv s → ((i₁ + i₂) t).run s = ((j₁ + j₂) t).run s ∨
      ((∀ z ∈ support (((i₁ + i₂) t).run s), C z.2) ∧
        ∀ z ∈ support (((j₁ + j₂) t).run s), C z.2)
  | .inl t, s, hs => h₁ t s hs
  | .inr t, s, hs => h₂ t s hs

/-- Query-wise equalities on states satisfying `Inv` combine over a sum of implementations. -/
theorem queryEq_add (Inv : σ → Prop) {i₁ j₁ : QueryImpl spec₁ (StateT σ ProbComp)}
    {i₂ j₂ : QueryImpl spec₂ (StateT σ ProbComp)}
    (h₁ : ∀ t s, Inv s → (i₁ t).run s = (j₁ t).run s)
    (h₂ : ∀ t s, Inv s → (i₂ t).run s = (j₂ t).run s) :
    ∀ t s, Inv s → ((i₁ + i₂) t).run s = ((j₁ + j₂) t).run s
  | .inl t, s, hs => h₁ t s hs
  | .inr t, s, hs => h₂ t s hs

/-- Query-wise projection equalities combine over a sum of oracle implementations. -/
theorem queryMap_add {τ : Type} (proj : σ → τ)
    {i₁ : QueryImpl spec₁ (StateT σ ProbComp)} {i₂ : QueryImpl spec₂ (StateT σ ProbComp)}
    {j₁ : QueryImpl spec₁ (StateT τ ProbComp)} {j₂ : QueryImpl spec₂ (StateT τ ProbComp)}
    (h₁ : ∀ t s, Prod.map id proj <$> (i₁ t).run s = (j₁ t).run (proj s))
    (h₂ : ∀ t s, Prod.map id proj <$> (i₂ t).run s = (j₂ t).run (proj s)) :
    ∀ t s, Prod.map id proj <$> ((i₁ + i₂) t).run s = ((j₁ + j₂) t).run (proj s)
  | .inl t, s => h₁ t s
  | .inr t, s => h₂ t s

/-- Query-wise expected-score bounds combine over a sum of implementations, charging `ε` exactly
on the queries selected by `Sum.elim p₁ p₂`. -/
theorem payoff_add (Inv : σ → Prop) (score : σ → ℝ≥0∞) (ε : ℝ≥0∞)
    {i₁ : QueryImpl spec₁ (StateT σ ProbComp)} {i₂ : QueryImpl spec₂ (StateT σ ProbComp)}
    (p₁ : ι₁ → Bool) (p₂ : ι₂ → Bool)
    (h₁ : ∀ t s, Inv s → wp ((i₁ t).run s) (fun z => score z.2) ≤
      score s + if p₁ t then ε else 0)
    (h₂ : ∀ t s, Inv s → wp ((i₂ t).run s) (fun z => score z.2) ≤
      score s + if p₂ t then ε else 0) :
    ∀ t s, Inv s → wp (((i₁ + i₂) t).run s) (fun z => score z.2) ≤
      score s + if Sum.elim p₁ p₂ t then ε else 0
  | .inl t, s, hs => h₁ t s hs
  | .inr t, s, hs => h₂ t s hs

end OracleComp
