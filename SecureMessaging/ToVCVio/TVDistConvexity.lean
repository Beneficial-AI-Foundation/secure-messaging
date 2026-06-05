/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VCVio.ProgramLogic.Relational.Quantitative

/-!
# Real-valued TV-distance convexity over a `bind` (missing VCVio brick)

VCVio's `ofReal_tvDist_bind_left_le_const` states the convex-combination bound in `ℝ≥0∞`
(`ENNReal.ofReal`):

```
ofReal (tvDist (mx >>= f) (mx >>= g)) ≤ ε
```

The EtM authenticity hop wants the plain real-valued statement `tvDist (mx >>= f) (mx >>= g) ≤ c`.
This is the direct real-valued companion, derived from the upstream `ofReal` lemma.

TODO(upstream): contribute alongside `ofReal_tvDist_bind_left_le_const` in
`VCVio/ProgramLogic/Relational/Quantitative.lean`.
-/

open ENNReal OracleComp.ProgramLogic.Relational

namespace ToVCVio

universe u v

/-- If `tvDist (f a) (g a) ≤ c` for every `a` (with `0 ≤ c`), then
`tvDist (mx >>= f) (mx >>= g) ≤ c`. Real-valued companion of `ofReal_tvDist_bind_left_le_const`. -/
theorem tvDist_bind_left_le_const {m : Type u → Type v} [Monad m] [LawfulMonad m] [HasEvalPMF m]
    {α β : Type u} (mx : m α) (f g : α → m β) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ a, tvDist (f a) (g a) ≤ c) :
    tvDist (mx >>= f) (mx >>= g) ≤ c :=
  (ENNReal.ofReal_le_ofReal_iff hc).mp
    (ofReal_tvDist_bind_left_le_const mx f g (ENNReal.ofReal c)
      (fun a _ => ENNReal.ofReal_le_ofReal (h a)))

end ToVCVio
