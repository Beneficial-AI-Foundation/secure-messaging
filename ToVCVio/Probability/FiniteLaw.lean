/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
module

public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.OracleComp.ProbComp

/-!
# Finite output laws of probabilistic computations

`finiteLaw` is the output distribution of a `ProbComp`, as a measure on the discrete σ-algebra.
This file proves that two computations have the same `finiteLaw` exactly when they give each
output with the same probability, and that `finiteLaw` respects bind and map.
-/

@[expose] public section

namespace ToVCVio

open OracleComp MeasureTheory

/-- The complete discrete output measure of a finite probabilistic computation. -/
noncomputable abbrev finiteLaw {α : Type} (mx : ProbComp α) :
    @Measure α ⊤ := @evalDist _ _ _ ⊤ mx

/-- Two computations have the same `finiteLaw` exactly when they give each output with the same
probability. -/
theorem finiteLaw_ext_iff {α : Type} {mx my : ProbComp α} :
    finiteLaw mx = finiteLaw my ↔
      ∀ x, Pr{let y ← mx}[y = x] = Pr{let y ← my}[y = x] := by
  let : MeasurableSpace α := ⊤
  constructor
  · intro h x
    exact (EvalDistEq.of_evalDist_eq h).prEvent_eq (· = x)
  · intro h
    exact (OracleComp.evalDistEq_of_forall_prEvent_eq_output h).evalDist_eq

/-- If the two continuations have the same law for each first output, the two binds have the same
law. -/
theorem finiteLaw_bind_congr {α β : Type} (mx : ProbComp α)
    {ob₁ ob₂ : α → ProbComp β} (h : ∀ x, finiteLaw (ob₁ x) = finiteLaw (ob₂ x)) :
    finiteLaw (mx >>= ob₁) = finiteLaw (mx >>= ob₂) := by
  let : MeasurableSpace β := ⊤
  exact OracleComp.evalDist_bind_congr_of_support mx ob₁ ob₂ fun x _ => h x

/-- Mapping a function over two computations with the same law gives the same law. -/
theorem finiteLaw_map_congr {α β : Type} {mx my : ProbComp α}
    (h : finiteLaw mx = finiteLaw my) (f : α → β) :
    finiteLaw (f <$> mx) = finiteLaw (f <$> my) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  exact ((EvalDistEq.of_evalDist_eq h).map f).evalDist_eq

/-- Replacing the head of a bind by one with the same finite law preserves the law. -/
theorem finiteLaw_bind_head {α β : Type} {mx my : ProbComp α}
    (h : finiteLaw mx = finiteLaw my) (k : α → ProbComp β) :
    finiteLaw (mx >>= k) = finiteLaw (my >>= k) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  exact ((EvalDistEq.of_evalDist_eq h).bind (fun _ => EvalDistEq.refl _)).evalDist_eq

/-- A discarded first computation does not change the finite law. -/
theorem finiteLaw_bind_const {α β : Type}
    (mx : ProbComp α) (my : ProbComp β) :
    finiteLaw (mx >>= fun _ => my) = finiteLaw my := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  exact (EvalDistEq.bind_const mx my).evalDist_eq

end ToVCVio
