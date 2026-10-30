/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import VCVio.OracleComp.Constructions.SampleableType

/-!
# Uniform choice of an index in `{1, …, q}`

Hybrid arguments over `q` steps often build one reduction that first picks a step uniformly at
random and then runs the reduction for that step. `epochChoice q` is this random choice.
-/

@[expose] public section

namespace ToVCVio

/-- Draws an index uniformly from `{1, …, q}` when `q > 0`, and returns `1` when `q = 0`. -/
def epochChoice (q : ℕ) : ProbComp ℕ :=
  if hq : q = 0 then pure 1
  else
    letI : NeZero q := ⟨hq⟩
    (fun i : Fin q => i.val + 1) <$> ($ᵗ (Fin q) : ProbComp (Fin q))

end ToVCVio
