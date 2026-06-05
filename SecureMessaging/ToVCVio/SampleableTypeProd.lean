/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VCVio.OracleComp.Constructions.SampleableType
import VCVio.EvalDist.Prod

/-!
# `SampleableType` instance for `Prod`

Provides `SampleableType (α × β)` from `SampleableType α` and `SampleableType β`,
sampling each component independently.

This is intended for eventual upstream to VCVio.
-/

open OracleComp ENNReal

private lemma selectElem_prod_as_seq (α β : Type) [SampleableType α] [SampleableType β] :
    (do let a ← ($ᵗ α : ProbComp α); let b ← ($ᵗ β : ProbComp β); pure (a, b) :
      ProbComp (α × β)) =
    Prod.mk <$> ($ᵗ α : ProbComp α) <*> ($ᵗ β : ProbComp β) := by
  simp [seq_eq_bind_map, monad_norm]

noncomputable instance instSampleableTypeProd
    {α β : Type} [SampleableType α] [SampleableType β] :
    SampleableType (α × β) where
  selectElem := do
    let a ← $ᵗ α
    let b ← $ᵗ β
    pure (a, b)
  mem_support_selectElem := fun ⟨a, b⟩ => by
    rw [selectElem_prod_as_seq]
    simp [uniformSample, SampleableType.mem_support_selectElem]
  probOutput_selectElem_eq := fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ => by
    rw [selectElem_prod_as_seq]
    simp only [uniformSample, probOutput_seq_map_prod_mk_eq_mul]
    congr 1 <;> exact SampleableType.probOutput_selectElem_eq _ _

/-- Uniform sampling on a product decomposes into independent sampling of each component. -/
lemma uniformSample_prod_eq_bind (α β : Type) [SampleableType α] [SampleableType β] :
    ($ᵗ (α × β) : ProbComp (α × β)) = (do
      let a ← ($ᵗ α : ProbComp α)
      let b ← ($ᵗ β : ProbComp β)
      pure (a, b)) := rfl
