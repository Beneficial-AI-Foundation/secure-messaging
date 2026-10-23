/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.HistoricalCertificateRecommendedArithmeticValueSetup

namespace lweCKA.HistoricalCertificate

set_option maxRecDepth 65536 in
set_option exponentiation.threshold 4096 in
/-- Unfold the shared Recommended certificate into the semantic packed recurrence. -/
theorem recommended_certificateValues_eq_runList :
    certificateValues recommendedConfig = recommendedValuePair recommendedRunList := by
  rw [certificateValues_eq_components, recommendedRun_eq_shared]
  simp only [recommendedValuePair, recommendedExtraPack, recommendedWeightPack,
    recommendedBits, recommendedCenter, recommendedRadix]

end lweCKA.HistoricalCertificate
