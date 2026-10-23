/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.HistoricalCertificateParanoidArithmeticMidpoint

/-! # Checked suffix for the historical Frodo Paranoid row -/

namespace lweCKA.HistoricalCertificateArithmeticCore.Paranoid

set_option maxRecDepth 65536 in
set_option maxHeartbeats 20000000 in
-- The closed 832-step recurrence and endpoint extraction need a larger reduction budget.
set_option exponentiation.threshold 4096 in
/-- Kernel-checked Paranoid endpoint after the midpoint suffix. -/
theorem checkpointSuffix_values :
    valuePair (packedRun 832 checkpointPack896) =
      (6030337663305705867094998372466972, 14272300219351570) := by
  decide +kernel

end lweCKA.HistoricalCertificateArithmeticCore.Paranoid
