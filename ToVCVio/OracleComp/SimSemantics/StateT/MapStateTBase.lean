/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.SimSemantics.StateT.Basic
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Base-state invariant preservation through `mapStateTBase` / `flattenStateT`

`mapStateTBase` simulates the base computation of an inner query implementation
without changing its `σ`-state component. Therefore any per-query invariant on
`σ` is preserved by `outer.mapStateTBase inner`. After `flattenStateT`, the same
invariant holds on the first component of the product state `σ × τ`.
-/

open OracleSpec OracleComp

namespace OracleComp

universe u

variable {ι₀ ι₁ ι' : Type} {spec₀ : OracleSpec ι₀} {spec₁ : OracleSpec ι₁}
  {spec' : OracleSpec ι'} {σ τ : Type}

/-- Running `(outer.mapStateTBase inner).flattenStateT t` from `(s, q)` simulates
`(inner t).run s` with `outer` from state `q`, then maps
`((u, s'), q')` to `(u, (s', q'))`. -/
theorem flattenStateT_mapStateTBase_apply_run
    (outer : QueryImpl spec₁ (StateT τ (OracleComp spec')))
    (inner : QueryImpl spec₀ (StateT σ (OracleComp spec₁)))
    (t : spec₀.Domain) (s : σ) (q : τ) :
    ((outer.mapStateTBase inner).flattenStateT t).run (s, q) =
      ((simulateQ outer ((inner t).run s)).run q >>=
        fun y : (spec₀.Range t × σ) × τ => pure (y.1.1, (y.1.2, y.2))) := by
  simp [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, map_eq_bind_pure_comp]

/-- The outer reinterpretation `outer.mapStateTBase inner` preserves any per-query `σ`-invariant of
`inner`. The outer query implementation acts on the base computation `(inner t).run s : OracleComp
spec₁ (Range × σ)`, so the `σ`-component of every reachable value is one reachable by `inner`
itself (`support_simulateQ_run'_subset`). -/
theorem mapStateTBase_run_preserves_inv
    (outer : QueryImpl spec₁ (StateT τ (OracleComp spec')))
    (inner : QueryImpl spec₀ (StateT σ (OracleComp spec₁)))
    (inv : σ → Prop)
    (hinv : ∀ (t : spec₀.Domain) (s : σ), inv s →
      ∀ y ∈ support ((inner t).run s), inv y.2)
    (t : spec₀.Domain) (s : σ) (hs : inv s) (q : τ) :
    ∀ y ∈ support (((outer.mapStateTBase inner) t).run s |>.run q), inv y.1.2 := by
  intro y hy
  -- `((outer.mapStateTBase inner) t).run s = simulateQ outer ((inner t).run s)` by `rfl`.
  have hy' : y.1 ∈ support ((simulateQ outer ((inner t).run s)).run' q) := by
    rw [StateT.run'_eq, support_map]
    exact ⟨y, hy, rfl⟩
  exact hinv t s hs y.1 (support_simulateQ_run'_subset outer ((inner t).run s) q hy')

/-- The `flattenStateT` reassociation transports a per-query `σ`-invariant of `inner` onto the
first (`σ`) component of the flattened product state of `(outer.mapStateTBase inner).flattenStateT`.
This is exactly the `hinv` side condition of `run'_simulateQ_eq_of_query_map_eq_inv'` for the
composed handler. -/
theorem flattenStateT_mapStateTBase_run_preserves_inv
    (outer : QueryImpl spec₁ (StateT τ (OracleComp spec')))
    (inner : QueryImpl spec₀ (StateT σ (OracleComp spec₁)))
    (inv : σ → Prop)
    (hinv : ∀ (t : spec₀.Domain) (s : σ), inv s →
      ∀ y ∈ support ((inner t).run s), inv y.2)
    (t : spec₀.Domain) (s : σ × τ) (hs : inv s.1) :
    ∀ y ∈ support (((outer.mapStateTBase inner).flattenStateT t).run s), inv y.2.1 := by
  obtain ⟨s, q⟩ := s
  intro y hy
  -- Unfold the flattened run to a bind over the composed-base run; the `σ`-component `.2.1`
  -- comes from the inner value `.1.2`.
  rw [flattenStateT_mapStateTBase_apply_run, mem_support_bind_iff] at hy
  obtain ⟨z, hz, hyz⟩ := hy
  simp only [support_pure, Set.mem_singleton_iff] at hyz
  subst hyz
  exact mapStateTBase_run_preserves_inv outer inner inv hinv t s hs q z hz

end OracleComp
