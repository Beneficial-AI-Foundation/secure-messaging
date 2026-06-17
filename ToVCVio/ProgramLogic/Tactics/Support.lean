import VCVio.EvalDist.Monad.Basic
import ToVCVio.Control.StateT

/-!
# Support tactics for VCV-io stateful computations

These tactics package the proof plumbing that appears after unfolding a
`StateT` oracle handler and looking at a hypothesis of the form
`h : z ∈ support ((...).run s)`.

`vcv_support h` normalizes the common `StateT`/`support` combinators in the
named support hypothesis and repeatedly extracts witnesses introduced by
`support_bind`.

Bare `vcv_support` is a bundled closer for the same proof shape: it normalizes
support facts in the local context, substitutes forced equalities, and then
tries small general solvers such as `grind`.  This form is meant for
`<;> vcv_support` and `all_goals vcv_support`.

After unfolding a single oracle handler, the support hypothesis falls into one
of three recurring shapes, all closed by `vcv_support`:

* *bounded-union support* — a state-preserving oracle behind a lifted
  `unifSpec` query, where `support_bind`/`Set.mem_iUnion₂` expose the sampled
  value while the state is pinned to the incoming one;
* *guarded-pure support* — a state-preserving oracle gated by an `if`, where
  `split_ifs` leaves a `support_pure` singleton in each branch;
* *one-counter-bump support* — a counter-bumping send oracle, where the bumped
  record is definitionally equal to the goal's projection but not syntactically,
  handled by the explicit pair closers below.
-/

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
macro "vcv_support" h:ident : tactic =>
  `(tactic|
    (vcv_simp_support at $h:ident
     vcv_extract_support_binds at $h:ident))

/-- Normalize local support facts and close common support-generated goals.

After normalization the bind witnesses sit under existentials, so they are
destructured before substitution; the explicit pair closers handle the
one-counter-bump send shapes, where the bumped record is definitionally equal
to the goal's projection but not syntactically. -/
macro "vcv_support" : tactic =>
  `(tactic|
    (simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_monadLift,
      monadLift_self, StateT.run_pure, pure_bind, bind_assoc, support_bind,
      support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at *
     try casesm* Exists _, _ ∧ _
     try subst_vars
     first
       | grind
       | omega
       | exact ⟨le_refl _, le_refl _⟩
       | exact ⟨Nat.le_succ _, le_refl _⟩
       | exact ⟨le_refl _, Nat.le_succ _⟩
       | simp_all))
