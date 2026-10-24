/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.HistoricalCertificateRecommendedCertificateUnfold

namespace lweCKA.HistoricalCertificate

/-- The semantic Recommended certificate equals the closed arithmetic recurrence. -/
theorem recommended_certificateValues_eq_core :
    certificateValues recommendedConfig =
      HistoricalCertificateArithmeticCore.Recommended.valuePair
        (HistoricalCertificateArithmeticCore.Recommended.packedRun 1504
          HistoricalCertificateArithmeticCore.Recommended.initial) := by
  rw [recommended_certificateValues_eq_runList, recommendedValuePair_eq_core,
    recommendedRunList_eq_core]

end lweCKA.HistoricalCertificate
