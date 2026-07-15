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
matching honest encapsulation. Table 1 lists the design rate for each approved
parameter set as a power of two, `δ_p = 2 ^ (-e_p)`.

The number `e_p` is therefore the base-two failure exponent, equivalently
`e_p=-log₂(δ_p)`.  It is not a probability or a random variable: it is a
compact logarithmic way to state the proposed upper bound.  A larger `e_p`
means a smaller failure threshold `δ_p`.

This file defines the exponent `e_p` exactly as a rational number and defines
the corresponding threshold constant `δ_p=2^(-e_p)` in `ℝ≥0∞`.  These are the
three numerical thresholds appearing on the right-hand side of the
correctness inequalities.  The probability inequality itself is stated and
proved conditionally in `SecureMessaging.KEM.MLKEM.Correctness`.

The use of `ℝ≥0∞` rather than `ℝ≥0` comes from the probability-library
interface: probabilities elsewhere in the library may be countable sums, for
which an infinite value must be representable before normalization is proved.
The constants in this file are finite positive real numbers smaller than one,
so nothing in their mathematical meaning requires the point at infinity.  In
particular, this file merely defines the proposed upper bounds; the substantive
theorem is that a failure probability is at most one of these numbers.
-/

open scoped ENNReal

namespace MLKEM

/-- FIPS 203 Table 1 decapsulation-failure exponent `e_p`: Table 1 assigns the
design rate `2 ^ (-e_p)` to parameter set `p`.

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

/-- The FIPS 203 Section 3.2 threshold constant `δ_p=2^(-e_p)` for parameter set
`p`.  It is represented in `ℝ≥0∞` to match the probability API, although this
particular value is finite and could equivalently be regarded as an element of
`ℝ≥0`.  This definition introduces the proposed bound; it does not itself
prove a probability inequality. -/
-- ANCHOR: fips203DecapsulationFailureBound
noncomputable def fips203DecapsulationFailureBound (p : ParameterSet) : ℝ≥0∞ :=
  2 ^ (-(decapsulationFailureExponent p : ℝ))
-- ANCHOR_END: fips203DecapsulationFailureBound

end MLKEM
