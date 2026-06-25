/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.SimSemantics.StateT.Basic
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Base-state invariant preservation through `mapStateTBase` / `flattenStateT`

When a reduction is run inside an outer experiment, its handler ends up composed as
`(outer.mapStateTBase inner).flattenStateT` — an `inner` handler on
`StateT σ (OracleComp specₒ)` reinterpreted by `outer` and then reassociated into a single
`StateT (σ × τ) (OracleComp spec')` handler. Projection lemmas such as
`OracleComp.run'_simulateQ_eq_of_query_map_eq_inv'` carry a per-query invariant side condition

```
hinv : ∀ t s, inv s → ∀ y ∈ support ((impl₁ t).run s), inv y.2
```

at the *fully composed* level. In practice the invariant of interest is almost always a property
of the **inner** handler's `σ`-state alone (e.g. "the reduction never writes its inner cache, so
the inner cache stays `∅`"): neither the outer reinterpretation nor the `flattenStateT`
reassociation can touch the `σ`-component. This file proves that transparency once and for all, so
the composed `hinv` premise reduces to an `inner`-only statement.

`OracleComp.simulateQ_run_preserves_inv_of_query` is the simulation-level analogue; these are the
composition-level `mapStateTBase` / `flattenStateT` invariant-transparency lemmas.

## Main results

* `mapStateTBase_run_preserves_inv` — a per-query `σ`-invariant of `inner` is preserved by the
  outer reinterpretation `outer.mapStateTBase inner` (the `σ`-component is untouched).
* `flattenStateT_mapStateTBase_run_preserves_inv` — the same invariant, transported through the
  `flattenStateT` reassociation, lives on the `σ`-component of the flattened product state.
-/

open OracleSpec OracleComp

namespace OracleComp

universe u

variable {ι₀ ι₁ ι' : Type} {spec₀ : OracleSpec ι₀} {spec₁ : OracleSpec ι₁}
  {spec' : OracleSpec ι'} {σ τ : Type}

/-- Run-shape of the composed `(outer.mapStateTBase inner).flattenStateT` handler: running it on
the product state `(s, q)` runs `inner`'s base computation `(inner t).run s` under the outer
interpreter at outer-state `q`, then reassociates `((u, s'), q')` to `(u, (s', q'))`. This packages
the `flattenStateT` + `mapStateTBase` definitional unfolding into one rewrite, so projection proofs
do not pay the cost of expanding both composition stages by `simp`/defeq. -/
theorem flattenStateT_mapStateTBase_apply_run
    (outer : QueryImpl spec₁ (StateT τ (OracleComp spec')))
    (inner : QueryImpl spec₀ (StateT σ (OracleComp spec₁)))
    (t : spec₀.Domain) (s : σ) (q : τ) :
    ((outer.mapStateTBase inner).flattenStateT t).run (s, q) =
      ((simulateQ outer ((inner t).run s)).run q >>=
        fun y : (spec₀.Range t × σ) × τ => pure (y.1.1, (y.1.2, y.2))) := by
  rfl

/-- The outer reinterpretation `outer.mapStateTBase inner` preserves any per-query `σ`-invariant of
`inner`. The outer interpreter only acts on the base computation `(inner t).run s : OracleComp
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
  simp only [QueryImpl.flattenStateT, support_bind, Set.mem_iUnion,
    StateT.run_mk, support_pure, Set.mem_singleton_iff, exists_prop] at hy
  obtain ⟨z, hz, hyz⟩ := hy
  subst hyz
  exact mapStateTBase_run_preserves_inv outer inner inv hinv t s hs q z hz

end OracleComp
