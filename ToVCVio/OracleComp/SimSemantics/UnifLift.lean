/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.SimSemantics.QueryImpl.Basic

/-!
# The canonical `unifSpec → StateT σ` lift handler (shared helper)

`unifLiftStateT` is the single handler shared by the EtM game and reduction definitions: forward
every `unifSpec` (uniform-sampling) query through the base monad `OracleComp spec`, threading the
local game state `σ` unchanged (the `ProbComp` case is `spec := unifSpec`, since
`ProbComp = OracleComp unifSpec`). It is `@[reducible]`, so call sites that `unfold`/`simp` still
expose the underlying `.liftTarget` form.
-/

open OracleSpec OracleComp


/-- Forward `unifSpec` queries through `OracleComp spec`, threading the state `σ` unchanged:
the canonical lift of the identity uniform-sampling handler into `StateT σ (OracleComp spec)`.

Specializes to the `ProbComp` handlers via `spec := unifSpec` (`ProbComp = OracleComp unifSpec`). -/
@[reducible] def unifLiftStateT (σ : Type) {ι : Type} (spec : OracleSpec ι)
    [MonadLiftT (OracleQuery unifSpec) (OracleComp spec)] :
    QueryImpl unifSpec (StateT σ (OracleComp spec)) :=
  (QueryImpl.ofLift unifSpec (OracleComp spec)).liftTarget (StateT σ (OracleComp spec))
