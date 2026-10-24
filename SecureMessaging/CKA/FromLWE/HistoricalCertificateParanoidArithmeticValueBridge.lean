/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.HistoricalCertificateParanoidCertificateUnfold
import SecureMessaging.CKA.FromLWE.HistoricalCertificateParanoidArithmeticValueSetup

namespace lweCKA.HistoricalCertificate

/-- The semantic Paranoid certificate equals the closed arithmetic recurrence. -/
theorem paranoid_certificateValues_eq_core :
    certificateValues paranoidConfig =
      HistoricalCertificateArithmeticCore.Paranoid.valuePair
        (HistoricalCertificateArithmeticCore.Paranoid.packedRun 1728
          HistoricalCertificateArithmeticCore.Paranoid.initial) := by
  rw [paranoid_certificateValues_eq_runList, paranoidValuePair_eq_core,
    paranoidRunList_eq_core]

end lweCKA.HistoricalCertificate
