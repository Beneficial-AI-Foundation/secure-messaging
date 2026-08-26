/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.SimSemantics.QueryImpl.Basic

/-!
# The canonical `unifSpec → StateT σ` lift handler

`unifLiftStateT` forwards every `unifSpec` query through the base monad
`OracleComp spec` while threading state `σ` unchanged. The `ProbComp` case is
obtained with `spec := unifSpec`, since `ProbComp = OracleComp unifSpec`.
-/

namespace ToVCVio

open OracleSpec OracleComp


/-- Forward `unifSpec` queries through `OracleComp spec`, threading the state `σ` unchanged:
the canonical lift of the identity uniform-sampling handler into `StateT σ (OracleComp spec)`.

Specializes to the `ProbComp` handlers via `spec := unifSpec` (`ProbComp = OracleComp unifSpec`). -/
@[reducible] def unifLiftStateT (σ : Type) {ι : Type} (spec : OracleSpec ι)
    [MonadLiftT (OracleQuery unifSpec) (OracleComp spec)] :
    QueryImpl unifSpec (StateT σ (OracleComp spec)) :=
  (QueryImpl.ofLift unifSpec (OracleComp spec)).liftTarget (StateT σ (OracleComp spec))

end ToVCVio
