/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Recommended.Suffix

/-! # Assembled arithmetic for the historical Frodo Recommended row -/

namespace lweCKA.Frodo2016.Certificate.Arithmetic.Recommended

/-- Kernel-checked endpoint for the historical Frodo Recommended row. -/
theorem certificateValues_eq :
    valuePair (packedRun 1504 initial) =
      (10543492551966859497706958378128, 8988175038920) := by
  change valuePair (packedRun (768 + 736) initial) = _
  rw [packedRun_add, packedRun_eq_checkpointPack]
  exact checkpointSuffix_values

end lweCKA.Frodo2016.Certificate.Arithmetic.Recommended
