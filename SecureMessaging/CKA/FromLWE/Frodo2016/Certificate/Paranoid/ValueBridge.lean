/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Paranoid.CertificateUnfold
import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Paranoid.ValueSetup

namespace lweCKA.Frodo2016.Certificate

/-- The semantic Paranoid certificate equals the closed arithmetic recurrence. -/
theorem paranoid_certificateValues_eq_core :
    certificateValues paranoidConfig =
      Frodo2016.Certificate.Arithmetic.Paranoid.valuePair
        (Frodo2016.Certificate.Arithmetic.Paranoid.packedRun 1728
          Frodo2016.Certificate.Arithmetic.Paranoid.initial) := by
  rw [paranoid_certificateValues_eq_runList, paranoidValuePair_eq_core,
    paranoidRunList_eq_core]

end lweCKA.Frodo2016.Certificate
