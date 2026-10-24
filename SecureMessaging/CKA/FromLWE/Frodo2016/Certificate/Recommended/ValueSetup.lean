/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Recommended.WeightSetup

namespace lweCKA.Frodo2016.Certificate

/-- Semantic endpoint extraction for the Recommended bridge. -/
def recommendedValuePair (x : ℕ) : ℕ × ℕ :=
  (((x * recommendedExtraPack * recommendedWeightPack) >>>
      (recommendedBits * (2 * recommendedCenter))) % recommendedRadix,
    2 ^ 128 - x % (recommendedRadix - 1))

/-- Semantic Recommended extraction matches arithmetic-core extraction. -/
theorem recommendedValuePair_eq_core :
    recommendedValuePair = Frodo2016.Certificate.Arithmetic.Recommended.valuePair := by
  funext x
  unfold recommendedValuePair Frodo2016.Certificate.Arithmetic.Recommended.valuePair
  rw [recommendedExtraPack_eq_core, recommendedWeightPack_eq_core, recommendedRadix_eq_core]
  rfl

end lweCKA.Frodo2016.Certificate
