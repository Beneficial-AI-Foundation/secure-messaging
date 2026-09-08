/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.Constructions.SampleableType
import VCVio.EvalDist.BitVec
import VCVio.EvalDist.Prod

/-!
# Uniform `BitVec` block concatenation

Uniformity of truncated concatenation of uniform blocks — staging for upstream
VCVio (mirrors `VCVio/OracleComp/Constructions/BitVec.lean`, whose lemmas are
top-level): if each 128-bit block is uniform and independent, then the first `p`
bits of their concatenation are uniform on `BitVec p` (Phase 1 criterion 3,
generic half).
-/
