/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Certificate.ClosedForm

/-! # Kernel-checked failure certificate for FrodoKEM-976 -/

namespace FrodoKEM.Certificate

/-- The modern semantic certificate has the kernel-checked exact output pair. -/
theorem certificate976 :
    FailureCertificate.RoundedConvolution.certificateValues
      (config .FrodoKEM976) (badWeight .FrodoKEM976) =
        (97175197777440479084, 6213051) := by
  rw [certificateValues_eq_closed .FrodoKEM976 4096 4618 (by decide) (by decide) (by decide)]
  decide +kernel

end FrodoKEM.Certificate
