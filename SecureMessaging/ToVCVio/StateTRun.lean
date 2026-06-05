/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VCVio.OracleComp.SimSemantics.StateT.Basic

/-!
# Small `StateT` run helpers (missing VCVio bricks)

Generic plumbing lemmas about `StateT` runs that the EtM security proof re-derives inline many
times. Hoisted here as named lemmas; intended for upstream alongside VCVio's `StateT` lemmas.

* `runStateT_bind_fst_eq_run'` — running a `StateT` computation and keeping only the value equals
  `run'`. (Re-proven 8× inline in the EtM proof as `htail`.)
* `run'_monadLift_bind` — pushing `run'` through a `monadLift` bind. (The EtM PRF hop's `hpush`.)
-/

namespace ToVCVio

universe u v

variable {σ : Type u} {n : Type u → Type v} [Monad n] [LawfulMonad n]

/-- Running a `StateT` computation and projecting the value component equals `run'`:
`(x.run s >>= fun p => pure p.1) = x.run' s`. -/
theorem runStateT_bind_fst_eq_run' {α : Type u} (x : StateT σ n α) (s : σ) :
    (x.run s >>= fun p => pure p.1) = x.run' s := by
  simp [StateT.run'_eq, bind_pure_comp]

/-- Push `run'` through a `monadLift` bind: a lifted base computation `ma` binds before the state
is threaded, so `((liftM ma : StateT σ n α) >>= G).run' s = ma >>= fun a => (G a).run' s`. -/
theorem run'_monadLift_bind {α β : Type u} (ma : n α) (G : α → StateT σ n β) (s : σ) :
    ((liftM ma : StateT σ n α) >>= G).run' s = ma >>= fun a => (G a).run' s := by
  simp [StateT.run'_eq, StateT.run_bind, StateT.run_monadLift, bind_map_left, map_bind]

end ToVCVio
