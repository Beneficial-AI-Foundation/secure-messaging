/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Certificate.ClosedForm

/-! # Kernel-checked failure certificate for FrodoKEM-1344 -/

namespace FrodoKEM.Certificate

/-- The modern semantic certificate has the kernel-checked exact output pair. -/
theorem certificate1344 :
    FailureCertificate.RoundedConvolution.certificateValues
      (config .FrodoKEM1344) (badWeight .FrodoKEM1344) =
        (198663617378549905966698, 4264645) := by
  rw [certificateValues_eq_closed .FrodoKEM1344 2048 2566 (by decide) (by decide) (by decide)]
  decide +kernel

end FrodoKEM.Certificate
