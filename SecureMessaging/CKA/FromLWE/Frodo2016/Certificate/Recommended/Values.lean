/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Recommended.Bridge
import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Recommended.Core

/-! # Exact arithmetic certificate for the historical Frodo Recommended row -/

namespace lweCKA.Frodo2016.Certificate

/-- The kernel-checked values for the historical Frodo Recommended certificate. -/
theorem recommended_certificateValues :
    certificateValues recommendedConfig =
      (10543492551966859497706958378128, 8988175038920) :=
  recommended_certificateValues_eq_core.trans
    Frodo2016.Certificate.Arithmetic.Recommended.certificateValues_eq

end lweCKA.Frodo2016.Certificate
