/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.Attr.Register

/-!
# `stateT_run` simp attribute

This file declares the named simp set `stateT_run` for evaluating
`StateT.run` over the structure of a stateful oracle program: the
run-projection equations for `bind`, `get`, `set`, `pure`, and `monadLift`,
plus `pure_bind`. The members are tagged in `ToVCVio/Control/StateT.lean`.

Use `simp only [stateT_run, ...]` at call sites instead of re-listing the
run-projection equations. The set deliberately excludes `bind_assoc`: it
reshapes the program instead of evaluating `run`, so call sites that need it
list it explicitly.

The attribute is registered in its own file because `register_simp_attr`
does not take effect within the Lean file that declares it.
-/

/-- Simp set that evaluates `StateT.run` over the program structure: the
run-projection equations for `bind`/`get`/`set`/`pure`/`monadLift` plus
`pure_bind`. -/
register_simp_attr stateT_run
