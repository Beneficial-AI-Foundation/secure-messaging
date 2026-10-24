/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.HistoricalCertificateRecommendedArithmeticBridge
import SecureMessaging.CKA.FromLWE.HistoricalCertificateRecommendedArithmeticCore

/-! # Exact arithmetic certificate for the historical Frodo Recommended row -/

namespace lweCKA.HistoricalCertificate

/-- The kernel-checked values for the historical Frodo Recommended certificate. -/
theorem recommended_certificateValues :
    certificateValues recommendedConfig =
      (10543492551966859497706958378128, 8988175038920) :=
  recommended_certificateValues_eq_core.trans
    HistoricalCertificateArithmeticCore.Recommended.certificateValues_eq

end lweCKA.HistoricalCertificate
