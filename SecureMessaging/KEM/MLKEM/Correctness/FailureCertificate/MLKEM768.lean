/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

-- Imported only to serialize the heavy kernel checks: lake builds imports first, so
-- at most one certificate module elaborates at a time.
import SecureMessaging.KEM.MLKEM.Correctness.FailureCertificate.MLKEM512

/-!
# The ML-KEM-768 failure certificate

The per-set kernel check, kept in its own module so the elaboration process holds a
single heavy `decide`.
-/

open LatticeCrypto
open scoped ENNReal

namespace MLKEM

set_option exponentiation.threshold 30000 in
/-- The fifth-power Table 1 certificate at parameter set ML-KEM-768. -/
theorem decodeFailureMass_pow_five_le_mlkem768 :
    (ringDegree * decodeFailureMass .MLKEM768) ^ 5 * 2 ^ scaledFailureExponent .MLKEM768 ≤
      (2 * noiseDenominator .MLKEM768) ^ 5 := by
  have hR : (2 : ℕ) ≤ 2 ^ 21312 := Nat.le_self_pow (by norm_num) 2
  have hwin : LawWindow (coefficientNoiseLaw .MLKEM768) (-9322)
      (-9322 + ((modulus * 6 : ℕ) : ℤ) - 1) :=
    lawWindow_coefficientNoiseLaw_mlkem768.mono (le_refl _) (by norm_num [modulus])
  have hden : 2 * totalMass (coefficientNoiseLaw .MLKEM768) < 2 ^ 21312 := by
    have h : totalMass (coefficientNoiseLaw .MLKEM768) = 2 ^ 12292 * 3329 ^ 769 :=
      noiseDenominator_mlkem768
    rw [h]; decide +kernel
  rw [decodeFailureMass_eq .MLKEM768 hR hwin hden, lawPack_coefficientNoiseLaw_mlkem768,
    weightPack_blocked, noiseDenominator_mlkem768, scaledFailureExponent, ringDegree]
  decide +kernel

end MLKEM
