/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.NormNum

/-!
# Closed arithmetic for the Frodo Challenge key-exchange pair bound

This file checks the two rational inequalities used by the pairwise Chernoff
argument.  Their probabilistic interpretation is proved in the neighboring
challenge modules; this module contains only exact rational arithmetic.
-/

namespace lweCKA

/-- Exact rational bounds for the shared-coordinate and disjoint-coordinate Chernoff estimates.
`ChallengePairBound` applies these inequalities to the first-exchange, uniform-public-matrix model
with the exact Challenge D1 sampler; this theorem itself is solely an arithmetic statement. -/
theorem challenge_pair_chernoff_arithmetic :
    (4 * ((5 : ℚ) / 6) ^ 512 *
        ((127847491742921604065083548949681 : ℚ) /
          120367356051456000000000000000000) ^ 704 *
        ((784927 : ℚ) / 768000) ^ 2 ≤ (1 : ℚ) / 2 ^ 70) ∧
    (4 * ((5 : ℚ) / 6) ^ 512 *
        ((73796729825894041 : ℚ) / 71663616000000000) ^ 1408 *
        ((784927 : ℚ) / 768000) ^ 2 ≤ (1 : ℚ) / 2 ^ 70) := by
  constructor <;> norm_num [div_pow] <;> decide +kernel

end lweCKA
