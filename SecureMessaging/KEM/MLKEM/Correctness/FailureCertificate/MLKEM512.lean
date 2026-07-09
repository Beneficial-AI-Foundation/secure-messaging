/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.MLKEM.Correctness.FailureCertificate.PackedLaws

/-!
# The ML-KEM-512 failure certificate

The per-set kernel check, kept in its own module so the elaboration process holds a
single heavy `decide`.
-/

open LatticeCrypto
open scoped ENNReal

namespace MLKEM

-- Raise the threshold so `whnf` does not warn on the closed `2 ^ W` bases (W ≤ 28416),
-- which are bounded by monotonicity, never evaluated; nested `(2 ^ W) ^ q` stays kernel-only.
set_option exponentiation.threshold 30000 in
/-- The fifth-power Table 1 certificate at parameter set ML-KEM-512. -/
theorem decodeFailureMass_pow_five_le_mlkem512 :
    (ringDegree * decodeFailureMass .MLKEM512) ^ 5 * 2 ^ scaledFailureExponent .MLKEM512 ≤
      (2 * noiseDenominator .MLKEM512) ^ 5 := by
  have hR : (2 : ℕ) ≤ 2 ^ 17280 := Nat.le_self_pow (by norm_num) 2
  have hwin : LawWindow (coefficientNoiseLaw .MLKEM512) (-10858)
      (-10858 + ((modulus * 7 : ℕ) : ℤ) - 1) :=
    lawWindow_coefficientNoiseLaw_mlkem512.mono (le_refl _) (by norm_num [modulus])
  have hden : 2 * totalMass (coefficientNoiseLaw .MLKEM512) < 2 ^ 17280 := by
    have h : totalMass (coefficientNoiseLaw .MLKEM512) = 2 ^ 11268 * 3329 ^ 513 :=
      noiseDenominator_mlkem512
    rw [h]; decide +kernel
  rw [decodeFailureMass_eq .MLKEM512 hR hwin hden, lawPack_coefficientNoiseLaw_mlkem512,
    weightPack_blocked, noiseDenominator_mlkem512, scaledFailureExponent, ringDegree]
  decide +kernel

end MLKEM
