/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VCVio.OracleComp.SimSemantics.QueryImpl.Basic

/-!
# The canonical `unifSpec → StateT σ` lift handler (shared helper)

The game and reduction definitions across the EtM development each need the same handler: forward
every `unifSpec` (uniform-sampling) query through the base monad `OracleComp spec`, threading the
local game state `σ : Type` unchanged. It was written out verbatim ~7 times as
`(QueryImpl.ofLift unifSpec (OracleComp spec)).liftTarget (StateT σ (OracleComp spec))`
(the `ProbComp` instances are the `spec := unifSpec` case, since `ProbComp = OracleComp unifSpec`).

`unifLiftStateT` is that single source of truth. It is `@[reducible]` so existing call sites that
`unfold`/`simp [gameUnifImpl, …]` continue to expose the underlying `.liftTarget` form.
-/

open OracleSpec OracleComp

namespace ToVCVio

/-- Forward `unifSpec` queries through `OracleComp spec`, threading the state `σ` unchanged:
the canonical lift of the identity uniform-sampling handler into `StateT σ (OracleComp spec)`.

Specializes to the `ProbComp` handlers via `spec := unifSpec` (`ProbComp = OracleComp unifSpec`). -/
@[reducible] def unifLiftStateT (σ : Type) {ι : Type} (spec : OracleSpec ι)
    [MonadLiftT (OracleQuery unifSpec) (OracleComp spec)] :
    QueryImpl unifSpec (StateT σ (OracleComp spec)) :=
  (QueryImpl.ofLift unifSpec (OracleComp spec)).liftTarget (StateT σ (OracleComp spec))

end ToVCVio
