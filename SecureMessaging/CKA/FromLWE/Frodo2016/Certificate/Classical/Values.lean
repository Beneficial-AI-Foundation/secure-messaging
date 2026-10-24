/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Classical.Bridge
import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Classical.Core

/-! # Exact arithmetic certificate for the historical Frodo Classical row -/

namespace lweCKA.Frodo2016.Certificate

/-- The kernel-checked values for the historical Frodo Classical certificate. -/
theorem classical_certificateValues :
    certificateValues classicalConfig =
      (69032097099755389459452237865466, 2128885962681258) :=
  classical_certificateValues_eq_core.trans
    Frodo2016.Certificate.Arithmetic.Classical.certificateValues_eq

end lweCKA.Frodo2016.Certificate
