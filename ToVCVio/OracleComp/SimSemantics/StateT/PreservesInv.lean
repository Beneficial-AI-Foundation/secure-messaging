/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv

/-!
# Invariant preservation for sums and lifted computations

These lemmas are backports from [VCVio PR #656](https://github.com/Verified-zkEVM/VCVio/pull/656),
commit `41ead83`. The pinned VCVio revision `7607103` does not contain them. They retain the
upstream names and statements. Once the VCVio pin includes these declarations, remove the local
backports and import `VCVio.OracleComp.SimSemantics.StateT.PreservesInv` directly.
-/

open OracleSpec OracleComp

namespace QueryImpl

variable {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {σ : Type}

/-- If `impl₁` and `impl₂` preserve `Inv`, then so does `impl₁ + impl₂`. -/
lemma PreservesInv.add {impl₁ : QueryImpl spec₁ (StateT σ ProbComp)}
    {impl₂ : QueryImpl spec₂ (StateT σ ProbComp)} {Inv : σ → Prop}
    (h₁ : PreservesInv impl₁ Inv) (h₂ : PreservesInv impl₂ Inv) :
    PreservesInv (impl₁ + impl₂) Inv
  | .inl t => h₁ t
  | .inr t => h₂ t

end QueryImpl

namespace StateT

/-- Lifting a probabilistic computation to `StateT` leaves the state unchanged. -/
lemma statePreserving_monadLift {σ α : Type} (mx : ProbComp α) :
    StatePreserving (monadLift mx : StateT σ ProbComp α) := by
  intro σ0 z hz
  simp only [StateT.run_monadLift, monadLift_eq_self, support_bind, support_pure,
    Set.mem_iUnion, Set.mem_singleton_iff] at hz
  obtain ⟨_, -, rfl⟩ := hz
  rfl

/-- Lifting a probabilistic computation to `StateT` preserves every state invariant. -/
lemma preservesInv_monadLift {σ α : Type} (mx : ProbComp α) (Inv : σ → Prop) :
    PreservesInv (monadLift mx : StateT σ ProbComp α) Inv :=
  preservesInv_of_statePreserving _ _ (statePreserving_monadLift mx)

end StateT
