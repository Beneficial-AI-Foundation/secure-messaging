/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Classical.Suffix

/-! # Assembled exact arithmetic for the historical Frodo Classical certificate -/

namespace lweCKA.Frodo2016.Certificate.Arithmetic.Classical

/-- The kernel-checked endpoint for the historical Frodo Classical row. -/
theorem certificateValues_eq :
    valuePair (packedRun 1184 initial) =
      (69032097099755389459452237865466, 2128885962681258) := by
  change valuePair (packedRun (640 + 544) initial) = _
  rw [packedRun_add, packedRun_eq_checkpointPack]
  exact checkpointSuffix_values

end lweCKA.Frodo2016.Certificate.Arithmetic.Classical
