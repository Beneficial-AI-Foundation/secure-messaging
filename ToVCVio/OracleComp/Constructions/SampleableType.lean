/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.Constructions.SampleableType
import VCVio.EvalDist.Prod

/-!
# `SampleableType` instance for `Prod`

Provides `SampleableType (α × β)` from `SampleableType α` and `SampleableType β`,
sampling each component independently.
-/

open OracleComp ENNReal

private lemma selectElem_prod_as_seq (α β : Type) [SampleableType α] [SampleableType β] :
    (do let a ← ($ᵗ α : ProbComp α); let b ← ($ᵗ β : ProbComp β); pure (a, b) :
      ProbComp (α × β)) =
    Prod.mk <$> ($ᵗ α : ProbComp α) <*> ($ᵗ β : ProbComp β) := by
  simp [seq_eq_bind_map, monad_norm]

/-- Uniform sampling on a product decomposes into independent sampling of each component. -/
lemma uniformSample_prod_eq_bind (α β : Type) [SampleableType α] [SampleableType β] :
    ($ᵗ (α × β) : ProbComp (α × β)) = (do
      let a ← ($ᵗ α : ProbComp α)
      let b ← ($ᵗ β : ProbComp β)
      pure (a, b)) := by
  change Prod.mk <$> ($ᵗ α : ProbComp α) <*> ($ᵗ β : ProbComp β) = _
  exact (selectElem_prod_as_seq α β).symm
