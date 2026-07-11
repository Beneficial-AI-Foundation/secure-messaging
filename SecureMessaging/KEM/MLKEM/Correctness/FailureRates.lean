/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import LatticeCrypto.MLKEM.Params
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# FIPS 203 decapsulation-failure rates

FIPS 203 Section 3.2 defines decapsulation failure as the event that an honest
ML-KEM decapsulation output differs from the shared secret produced by the
matching honest encapsulation. Table 1 records the failure probability of each
approved parameter set as a power of two, `δ_p = 2 ^ (-e_p)`.

This file records the exponent `e_p` exactly, as a rational, and the bound
`δ_p = 2 ^ (-e_p)` as a probability in `ℝ≥0∞`. Correctness theorems consuming
the bound are stated in `SecureMessaging.KEM.MLKEM.Correctness.FIPS203Correctness`.
-/

open scoped ENNReal

namespace MLKEM

/-- FIPS 203 Table 1 decapsulation-failure exponent `e_p`: the approved parameter
set `p` has failure probability `2 ^ (-e_p)`.

* ML-KEM-512:  `138.8`
* ML-KEM-768:  `164.8`
* ML-KEM-1024: `174.8`
-/
-- ANCHOR: decapsulationFailureExponent
def decapsulationFailureExponent : ParameterSet → ℚ
  | .MLKEM512 => 138.8
  | .MLKEM768 => 164.8
  | .MLKEM1024 => 174.8
-- ANCHOR_END: decapsulationFailureExponent

/-- FIPS 203 Section 3.2 decapsulation-failure bound `δ_p = 2 ^ (-e_p)` for an
approved parameter set `p`, as a probability in `ℝ≥0∞`. Table 1 records the
concrete exponents `e_p` (see `decapsulationFailureExponent`). -/
-- ANCHOR: fips203DecapsulationFailureBound
noncomputable def fips203DecapsulationFailureBound (p : ParameterSet) : ℝ≥0∞ :=
  2 ^ (-(decapsulationFailureExponent p : ℝ))
-- ANCHOR_END: fips203DecapsulationFailureBound

end MLKEM
