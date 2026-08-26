/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.ProbComp
import ToVCVio.Control.StateT

/-!
# Support tactics for VCV-io stateful computations

These tactics package the proof plumbing that appears after unfolding a
`StateT` oracle handler and looking at a hypothesis of the form
`h : z ∈ support ((...).run s)`.

`vcvSupport h` normalizes the common `StateT`/`support` combinators in the
named support hypothesis and repeatedly extracts witnesses introduced by
`support_bind`.

Bare `vcvSupport` is a bundled closer for the same proof shape: it normalizes
support facts in the local context, substitutes forced equalities, and then
tries small general solvers such as `grind`.  This form is meant for
`<;> vcvSupport` and `all_goals vcvSupport`.

After unfolding a single oracle handler, the support hypothesis falls into one
of three recurring shapes, all closed by `vcvSupport`:

* *bounded-union support* — a state-preserving oracle behind a lifted
  `unifSpec` query, where `support_bind`/`Set.mem_iUnion₂` expose the sampled
  value while the state is pinned to the incoming one;
* *guarded-pure support* — a state-preserving oracle gated by an `if`, where
  `split_ifs` leaves a `support_pure` singleton in each branch;
* *one-counter-bump support* — a counter-bumping send oracle, where the bumped
  record is definitionally equal to the goal's projection but not syntactically,
  handled by the explicit pair closers below.
-/

namespace ToVCVio

/-- Simplify common `StateT` and support combinators in a support hypothesis. -/
macro "vcv_simp_support" " at " h:ident : tactic =>
  `(tactic|
    simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_monadLift,
      monadLift_self, StateT.run_pure, pure_bind, bind_assoc, support_bind,
      support_pure, Set.mem_singleton_iff] at $h:ident)

/-- Repeatedly peel bind-support witnesses produced by `support_bind`. -/
macro "vcv_extract_support_binds" " at " h:ident : tactic =>
  `(tactic| repeat (obtain ⟨_, _, $h⟩ := Set.mem_iUnion₂.mp $h))

/-- Normalize a support hypothesis for a stateful VCV-io computation. -/
macro "vcvSupport" h:ident : tactic =>
  `(tactic|
    (vcv_simp_support at $h:ident
     vcv_extract_support_binds at $h:ident))

/-- Normalize a named support hypothesis and close the common counter-monotonicity goal. -/
macro "vcvSupport" " at " h:ident : tactic =>
  `(tactic|
    (vcvSupport $h:ident
     try simp only [Set.mem_range, Set.mem_singleton_iff] at $h:ident
     first
       | obtain ⟨_, rfl⟩ := $h:ident
       | subst $h:ident
     first
       | exact ⟨le_refl _, le_refl _⟩
       | exact ⟨Nat.le_succ _, le_refl _⟩
       | exact ⟨le_refl _, Nat.le_succ _⟩
       | exact ⟨rfl, rfl⟩))

/-- Normalize local support facts and close common support-generated goals.

After normalization the bind witnesses sit under existentials, so they are
destructured before substitution; the explicit pair closers handle the
one-counter-bump send shapes, where the bumped record is definitionally equal
to the goal's projection but not syntactically. -/
macro "vcvSupport" : tactic =>
  `(tactic|
    (try simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_monadLift,
      monadLift_self, StateT.run_pure, pure_bind, bind_assoc, support_bind,
      support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at *
     try casesm* Exists _, _ ∧ _
     try subst_vars
     first
       | exact ⟨le_refl _, le_refl _⟩
       | exact ⟨Nat.le_succ _, le_refl _⟩
       | exact ⟨le_refl _, Nat.le_succ _⟩
       | exact ⟨rfl, rfl⟩
       | omega
       | simp_all
       | grind))

/-! ## Reference examples

These small examples mirror the recurring support shapes that appear in
stateful oracle proofs: a state-preserving lifted sample, a guarded pure oracle,
and a one-counter-bump oracle.  They are kept next to `vcvSupport` as regression
examples for the tactic without depending on any protocol-specific files.
-/

private structure VcvSupportExampleState where
  tA : ℕ
  tB : ℕ

/-- A state-preserving oracle behind a lifted probabilistic sample. -/
private def samplePreserving {α : Type} (mx : ProbComp α) :
    StateT VcvSupportExampleState ProbComp α := do
  let x ← liftM mx
  pure x

private lemma exp_sample {α : Type} (mx : ProbComp α)
    (σ : VcvSupportExampleState) (z : α × VcvSupportExampleState)
    (hz : z ∈ support ((samplePreserving mx).run σ)) :
    σ.tA ≤ z.2.tA ∧ σ.tB ≤ z.2.tB := by
  unfold samplePreserving at hz
  vcvSupport

/-- A guarded pure oracle that leaves the state unchanged in every branch. -/
private def guardedPure (cond : VcvSupportExampleState → Bool) :
    StateT VcvSupportExampleState ProbComp Unit := do
  let σ ← get
  if cond σ then
    pure ()
  else
    pure ()

private lemma exp_guarded (cond : VcvSupportExampleState → Bool)
    (σ : VcvSupportExampleState) (z : Unit × VcvSupportExampleState)
    (hz : z ∈ support ((guardedPure cond).run σ)) :
    σ.tA ≤ z.2.tA ∧ σ.tB ≤ z.2.tB := by
  unfold guardedPure at hz
  vcvSupport

/-- A one-counter-bump oracle. -/
private def bumpA : StateT VcvSupportExampleState ProbComp Unit := do
  let σ ← get
  set { σ with tA := σ.tA + 1 }
  pure ()

private lemma exp_bumpA (σ : VcvSupportExampleState) (z : Unit × VcvSupportExampleState)
    (hz : z ∈ support (bumpA.run σ)) :
    σ.tA ≤ z.2.tA ∧ σ.tB ≤ z.2.tB := by
  unfold bumpA at hz
  vcvSupport

end ToVCVio
