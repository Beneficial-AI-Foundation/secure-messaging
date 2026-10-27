/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Recommended.Midpoint

/-! # Checked suffix for the historical Frodo Recommended row -/

namespace lweCKA.Frodo2016.Certificate.Arithmetic.Recommended

set_option maxRecDepth 65536 in
set_option maxHeartbeats 20000000 in
-- The closed 736-step recurrence and endpoint extraction need a larger reduction budget.
set_option exponentiation.threshold 4096 in
/-- Kernel-checked Recommended endpoint after the midpoint suffix. -/
theorem checkpointSuffix_values :
    valuePair (packedRun 736 checkpointPack768) =
      (10543492551966859497706958378128, 8988175038920) := by
  decide +kernel

end lweCKA.Frodo2016.Certificate.Arithmetic.Recommended
