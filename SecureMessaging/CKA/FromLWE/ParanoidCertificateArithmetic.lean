/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.HistoricalCertificateParanoidArithmeticBridge
import SecureMessaging.CKA.FromLWE.HistoricalCertificateParanoidArithmeticCore

/-! # Exact arithmetic certificate for the historical Frodo Paranoid row -/

namespace lweCKA.HistoricalCertificate

/-- The kernel-checked values for the historical Frodo Paranoid certificate. -/
theorem paranoid_certificateValues :
    certificateValues paranoidConfig =
      (6030337663305705867094998372466972, 14272300219351570) :=
  paranoid_certificateValues_eq_core.trans
    HistoricalCertificateArithmeticCore.Paranoid.certificateValues_eq

end lweCKA.HistoricalCertificate
