/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Numerical
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.RandomOracle.Correctness

/-!
# FrodoKEM correctness in the finite random-oracle model

These bounds average over one shared random oracle table and the honest KEM coins.
The public matrix generator is fixed independently of that table. They are not bounds for
concrete SHAKE, for each fixed oracle table, or for multiple encapsulations.
-/

namespace FrodoKEM.ROM

/-- Honest KEM failure in the finite random-oracle model meets the checked rational bound. -/
theorem honestFailureProb_le_failureBound
    (ps : ParameterSet) (gen : Generator ps) :
    honestFailureProb ps gen ≤ Certificate.failureBound ps :=
  (honestFailureProb_le_idealNoiseBadProb ps gen).trans
    (Certificate.noiseBadProb_le_failureBound ps)

/-- The oracle-averaged honest KEM experiment meets all three exact fractional-bit targets. -/
theorem honestFailureProb_tenth_power_le
    (ps : ParameterSet) (gen : Generator ps) :
    honestFailureProb ps gen ^ 10 *
      2 ^ Certificate.exponentTenths ps ≤ 1 :=
  (mul_le_mul' (pow_le_pow_left' (honestFailureProb_le_failureBound ps gen) 10)
    le_rfl).trans (Certificate.failureBound_tenth_power_le ps)

end FrodoKEM.ROM
