/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

-- Imported only to serialize the heavy kernel checks: lake builds imports first, so
-- at most one certificate module elaborates at a time.
import SecureMessaging.KEM.MLKEM.Correctness.FailureCertificate.MLKEM768

/-!
# The ML-KEM-1024 failure certificate

The per-set kernel check, kept in its own module so the elaboration process holds a
single heavy `decide`.
-/

open LatticeCrypto
open scoped ENNReal

namespace MLKEM

set_option exponentiation.threshold 30000 in
/-- The fifth-power Table 1 certificate at parameter set ML-KEM-1024. -/
theorem decodeFailureMass_pow_five_le_mlkem1024 :
    (ringDegree * decodeFailureMass .MLKEM1024) ^ 5 * 2 ^ scaledFailureExponent .MLKEM1024 ≤
      (2 * noiseDenominator .MLKEM1024) ^ 5 := by
  have hR : (2 : ℕ) ≤ 2 ^ 28416 := Nat.le_self_pow (by norm_num) 2
  have hwin : LawWindow (coefficientNoiseLaw .MLKEM1024) (-10294)
      (-10294 + ((modulus * 7 : ℕ) : ℤ) - 1) :=
    lawWindow_coefficientNoiseLaw_mlkem1024.mono (le_refl _) (by norm_num [modulus])
  have hden : 2 * totalMass (coefficientNoiseLaw .MLKEM1024) < 2 ^ 28416 := by
    have h : totalMass (coefficientNoiseLaw .MLKEM1024) = 2 ^ 16388 * 3329 ^ 1025 :=
      noiseDenominator_mlkem1024
    rw [h]; decide +kernel
  rw [decodeFailureMass_eq .MLKEM1024 hR hwin hden, lawPack_coefficientNoiseLaw_mlkem1024,
    weightPack_blocked, noiseDenominator_mlkem1024, scaledFailureExponent, ringDegree]
  decide +kernel

end MLKEM
