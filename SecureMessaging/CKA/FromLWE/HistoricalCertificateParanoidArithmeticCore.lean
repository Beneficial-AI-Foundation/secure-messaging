/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.HistoricalCertificateParanoidArithmeticSuffix

/-! # Assembled arithmetic for the historical Frodo Paranoid row -/

namespace lweCKA.HistoricalCertificateArithmeticCore.Paranoid

/-- Kernel-checked endpoint for the historical Frodo Paranoid row. -/
theorem certificateValues_eq :
    valuePair (packedRun 1728 initial) =
      (6030337663305705867094998372466972, 14272300219351570) := by
  change valuePair (packedRun (896 + 832) initial) = _
  rw [packedRun_add, packedRun_eq_checkpointPack]
  exact checkpointSuffix_values

end lweCKA.HistoricalCertificateArithmeticCore.Paranoid
