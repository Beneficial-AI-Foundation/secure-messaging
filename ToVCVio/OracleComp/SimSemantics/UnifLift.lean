/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import VCVio.OracleComp.Support
public import VCVio.OracleComp.ProbComp.Basic

/-!
# The canonical `unifSpec → StateT σ` lift handler

`unifLiftStateT` forwards every `unifSpec` query through the base monad
`OracleComp spec` while threading state `σ` unchanged. The `ProbComp` case is
obtained with `spec := unifSpec`, since `ProbComp = OracleComp unifSpec`.
-/

@[expose] public section

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

/-- Lifted uniform randomness keeps any state. -/
theorem liftTarget_unif_run {σ : Type} (t : ℕ) (s : σ) :
    (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp)) t).run s =
      (fun a => (a, s)) <$> (QueryImpl.ofLift unifSpec ProbComp) t := by
  simp only [QueryImpl.ofLift_eq_id', PFunctor.Handler.liftTarget_apply, ofPFunctor_toPFunctor,
    QueryImpl.id'_apply, StateT.run_monadLift, monadLift_self, bind_pure_comp,
    map_eq_bind_pure_comp, QueryImpl.ofLift_apply]

end ToVCVio
