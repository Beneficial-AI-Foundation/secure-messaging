/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Classical.Midpoint

/-!
# Classical-parameter certificate suffix

This file verifies the remaining recurrence steps after the midpoint checkpoint.
-/

namespace lweCKA.Frodo2016.Certificate.Arithmetic.Classical

set_option maxRecDepth 65536 in
set_option maxHeartbeats 20000000 in
-- The closed 544-step recurrence and endpoint extraction need a larger reduction budget.
set_option exponentiation.threshold 4096 in
/-- The kernel-checked Classical endpoint after the midpoint recurrence suffix. -/
theorem checkpointSuffix_values :
    valuePair (packedRun 544 checkpointPack640) =
      (69032097099755389459452237865466, 2128885962681258) := by
  decide +kernel

end lweCKA.Frodo2016.Certificate.Arithmetic.Classical
