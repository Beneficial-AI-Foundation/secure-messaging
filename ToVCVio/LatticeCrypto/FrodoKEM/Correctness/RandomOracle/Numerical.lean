/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Numerical
public import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.RandomOracle.Correctness

/-!
# FrodoKEM correctness in the finite random-oracle model

These bounds average over one random table and the honest KEM coins. The public matrix
generator is fixed and does not read the table. They are not bounds for concrete SHAKE, for one
fixed table, or for many encapsulations.
-/

@[expose] public section

namespace FrodoKEM.ROM

/-- In the random-oracle model, the honest KEM failure probability is at most `failureBound`. -/
theorem honestFailureProb_le_failureBound
    (ps : ParameterSet) (gen : Generator ps) :
    honestFailureProb ps gen ≤ Certificate.failureBound ps :=
  (honestFailureProb_le_indepNoiseBadProb ps gen).trans
    (Certificate.noiseBadProb_le_failureBound ps)

/-- In the random-oracle model, the honest KEM failure probability `p` satisfies
`p ^ 10 * 2 ^ exponentTenths ps ≤ 1`, that is, `p ≤ 2 ^ (-exponentTenths ps / 10)`. -/
-- ANCHOR: frodoKEM_correctness
theorem honestFailureProb_tenth_power_le
    (ps : ParameterSet) (gen : Generator ps) :
    honestFailureProb ps gen ^ 10 *
      2 ^ Certificate.exponentTenths ps ≤ 1
-- ANCHOR_END: frodoKEM_correctness
    :=
  (mul_le_mul' (pow_le_pow_left' (honestFailureProb_le_failureBound ps gen) 10)
    le_rfl).trans (Certificate.failureBound_tenth_power_le ps)

end FrodoKEM.ROM
