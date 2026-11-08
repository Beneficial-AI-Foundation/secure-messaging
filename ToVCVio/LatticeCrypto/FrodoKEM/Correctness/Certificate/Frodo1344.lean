/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Certificate.ClosedForm

/-!
# Kernel-checked failure certificate for FrodoKEM-1344

The certificate also covers eFrodoKEM-1344, which has the same parameters.
-/

@[expose] public section

namespace FrodoKEM.Certificate

/-- The certificate values `(v₁, v₂)` for FrodoKEM-1344, computed by the kernel. -/
theorem certificate1344 :
    FailureCertificate.RoundedConvolution.certificateValues
      (config .FrodoKEM1344) (badWeight .FrodoKEM1344) =
        (198663617378549905966698, 4264645) := by
  rw [certificateValues_eq_closed .FrodoKEM1344 2048 2566 (by decide) (by decide) (by decide)]
  decide +kernel

end FrodoKEM.Certificate
