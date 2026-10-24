/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.SimSemantics.QueryImpl.Basic
import VCVio.OracleComp.Support

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

/-- `unifLiftStateT` returns a uniform answer and leaves the state unchanged. -/
lemma support_unifLiftStateT_run (σ : Type) (n : unifSpec.Domain) (s : σ) :
    support ((unifLiftStateT σ unifSpec n).run s) =
      Set.range fun a : unifSpec.Range n => (a, s) := by
  simp only [unifLiftStateT, PFunctor.Handler.liftTarget_apply, ofPFunctor_toPFunctor,
    QueryImpl.ofLift_apply, StateT.run_monadLift, monadLift_self, bind_pure_comp,
    MonadAttach.support_map, support_liftM, OracleQuery.input_query, OracleQuery.cont_query,
    Set.range_id, Set.image_univ]

end ToVCVio
