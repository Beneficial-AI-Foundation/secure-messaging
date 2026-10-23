/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.HistoricalCertificateRecommendedArithmeticRunBridge

namespace lweCKA.HistoricalCertificate

/-- Center of the semantic Recommended certificate window. -/
def recommendedCenter : ℕ := center recommendedConfig

/-- Semantic reversed weight pack for the Recommended bridge. -/
def recommendedWeightPack : ℕ :=
  weightPack recommendedConfig

/-- The semantic Recommended weight pack matches the arithmetic core. -/
theorem recommendedWeightPack_eq_core :
    recommendedWeightPack = HistoricalCertificateArithmeticCore.Recommended.weightPack := by
  rfl

end lweCKA.HistoricalCertificate
