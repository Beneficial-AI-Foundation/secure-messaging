/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromKEM.Correctness
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.CorrectnessError
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.RandomOracle.Numerical

/-!
# CKA from FrodoKEM — correctness in the finite random-oracle model

Instantiate the CKA-from-KEM construction with FrodoKEM for a parameter set `ps`, a public
matrix generator `gen` fixed independently of the oracle, and one finite random-oracle table
`H`, sampled uniformly before the game. The table answers every SHAKE call of key
generation, encapsulation, and decapsulation in every epoch. The adversary is fixed before
`H` is sampled and has no direct oracle access to `H`; it observes only the messages and keys
returned by the send oracles.

For a fixed table, `kemCKA.correctness_failure_le` bounds the failure probability by
`q · δ_H`, where `δ_H` is the generic correctness error of FrodoKEM with that table.
Averaging over the table turns `δ_H` into the random-oracle honest failure probability
(`FrodoKEM.ROM.honestFailureProb_eq_tsum_correctnessError`), which the FrodoKEM certificates
bound by `FrodoKEM.Certificate.failureBound ps`. No independence between epochs is used.

The statements average over the table; they are not bounds for each fixed table or for
concrete SHAKE. The leak package is `RandLeak.noLeak`: the correctness game never queries
the randomness-leaking send oracles, and `correctness_failure_le` holds for every leak
package. Each generated key-pair instance is used for at most one encapsulation; the
construction does not enforce distinct public-key values, so this is not a proof of the
eFrodoKEM usage limit of fewer than 256 ciphertexts per public key.
-/

open OracleSpec OracleComp ENNReal KEMScheme

namespace kemCKA

/-- FrodoKEM instantiation, failure-probability form. If `adv` makes at most `q` send
queries, the CKA-from-FrodoKEM correctness game, averaged over one shared finite
random-oracle table, fails with probability at most `q · Certificate.failureBound ps`. -/
-- ANCHOR: frodoKEMCorrectnessFailureLe
theorem frodoKEM_correctness_failure_le
    (ps : FrodoKEM.ParameterSet) (gen : FrodoKEM.ROM.Generator ps)
    (adv : CKAScheme.CKACorrectnessAdversary
      (Message (FrodoKEM.Ciphertext ps) (FrodoKEM.PublicKey ps)) (FrodoKEM.SharedSecretBits ps))
    (q : ℕ) (hq : CKAScheme.SendQueryBound adv q) :
    Pr{
      let H ← ToVCVio.FiniteXOF.sampleTable
        (FrodoKEM.ROM.inputLengths ps) (FrodoKEM.ROM.outputBits ps)
      let x ← CKAScheme.correctnessExp
        (scheme (FrodoKEM.KEM.asKEMScheme (FrodoKEM.ROM.operations ps gen H))
          (FrodoKEM.KEM.deterministicDecaps (FrodoKEM.ROM.operations ps gen H))
          (RandLeak.noLeak (FrodoKEM.KEM.asKEMScheme (FrodoKEM.ROM.operations ps gen H))))
        adv
    }[x = false] ≤ (q : ℝ≥0∞) * FrodoKEM.Certificate.failureBound ps
-- ANCHOR_END: frodoKEMCorrectnessFailureLe
    := by
  -- Split the table draw, apply the generic bound for each table, and average.
  rw [OracleComp.prEvent_bind_eq_tsum_prEvent]
  refine (ENNReal.tsum_le_tsum fun H =>
    mul_le_mul_right (correctness_failure_le _ _ _ adv q hq) _).trans ?_
  simp_rw [mul_left_comm _ (q : ℝ≥0∞)]
  rw [ENNReal.tsum_mul_left, ← FrodoKEM.ROM.honestFailureProb_eq_tsum_correctnessError]
  exact mul_le_mul_right (FrodoKEM.ROM.honestFailureProb_le_failureBound ps gen) _

/-- FrodoKEM instantiation, fractional-bit form: the averaged failure probability `P`
satisfies `P ^ 10 · 2 ^ exponentTenths ps ≤ q ^ 10`, that is `P ≤ q · 2 ^ (−e / 10)` with
`e / 10` equal to 138.7, 199.6 and 252.5 bits for FrodoKEM-640, -976 and -1344 and their
ephemeral variants. -/
-- ANCHOR: frodoKEMCorrectnessTenthPowerLe
theorem frodoKEM_correctness_failure_tenth_power_le
    (ps : FrodoKEM.ParameterSet) (gen : FrodoKEM.ROM.Generator ps)
    (adv : CKAScheme.CKACorrectnessAdversary
      (Message (FrodoKEM.Ciphertext ps) (FrodoKEM.PublicKey ps)) (FrodoKEM.SharedSecretBits ps))
    (q : ℕ) (hq : CKAScheme.SendQueryBound adv q) :
    Pr{
      let H ← ToVCVio.FiniteXOF.sampleTable
        (FrodoKEM.ROM.inputLengths ps) (FrodoKEM.ROM.outputBits ps)
      let x ← CKAScheme.correctnessExp
        (scheme (FrodoKEM.KEM.asKEMScheme (FrodoKEM.ROM.operations ps gen H))
          (FrodoKEM.KEM.deterministicDecaps (FrodoKEM.ROM.operations ps gen H))
          (RandLeak.noLeak (FrodoKEM.KEM.asKEMScheme (FrodoKEM.ROM.operations ps gen H))))
        adv
    }[x = false] ^ 10 * 2 ^ FrodoKEM.Certificate.exponentTenths ps ≤ (q : ℝ≥0∞) ^ 10
-- ANCHOR_END: frodoKEMCorrectnessTenthPowerLe
    := by
  refine (mul_le_mul' (pow_le_pow_left' (frodoKEM_correctness_failure_le ps gen adv q hq) 10)
    le_rfl).trans ?_
  rw [mul_pow, mul_assoc]
  exact mul_le_of_le_one_right' (FrodoKEM.Certificate.failureBound_tenth_power_le ps)

end kemCKA
