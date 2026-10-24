/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Classical.ValueSetup

namespace lweCKA.Frodo2016.Certificate

/-- The semantic Classical certificate equals the closed arithmetic recurrence. -/
theorem classical_certificateValues_eq_core :
    certificateValues classicalConfig =
      Frodo2016.Certificate.Arithmetic.Classical.valuePair
        (Frodo2016.Certificate.Arithmetic.Classical.packedRun 1184
          Frodo2016.Certificate.Arithmetic.Classical.initial) := by
  rw [classical_certificateValues_eq_runList, classicalValuePair_eq_core,
    classicalRunList_eq_core]

end lweCKA.Frodo2016.Certificate
