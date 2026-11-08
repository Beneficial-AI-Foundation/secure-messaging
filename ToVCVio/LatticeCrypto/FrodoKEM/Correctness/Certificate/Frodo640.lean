/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Certificate.ClosedForm

/-!
# Kernel-checked failure certificate for FrodoKEM-640

The certificate also covers eFrodoKEM-640, which has the same parameters.
-/

@[expose] public section

namespace FrodoKEM.Certificate

/-- The certificate values `(v₁, v₂)` for FrodoKEM-640, computed by the kernel. -/
theorem certificate640 :
    FailureCertificate.RoundedConvolution.certificateValues
      (config .FrodoKEM640) (badWeight .FrodoKEM640) =
        (10891243206164296039, 4220411) := by
  rw [certificateValues_eq_closed .FrodoKEM640 4096 4620 (by decide) (by decide) (by decide)]
  decide +kernel

end FrodoKEM.Certificate
