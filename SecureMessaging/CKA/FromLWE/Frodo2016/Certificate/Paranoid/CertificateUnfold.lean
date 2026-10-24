/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Paranoid.WeightSetup

namespace lweCKA.Frodo2016.Certificate

/-- Unfold the shared Paranoid certificate into the semantic packed recurrence. -/
theorem paranoid_certificateValues_eq_runList :
    certificateValues paranoidConfig = paranoidValuePair paranoidRunList :=
  (certificateValues_eq_components paranoidConfig).trans
    ((paranoidValuePair_eq_components (run paranoidConfig)).symm.trans
      (congrArg paranoidValuePair paranoidRun_eq_shared))

end lweCKA.Frodo2016.Certificate
