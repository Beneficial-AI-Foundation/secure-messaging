/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Defs

/-!
# Epoch-indexed security hybrids

**Construction.** Fix a scheme and exposure policies. For each `i : ℕ`,
`epochHybridImpl i` answers eligible challenges with uniform keys exactly
at epochs `t` satisfying `0 < t ∧ t ≤ i`. Other eligible challenges return
recorded keys. The game guards and honest key tables are retained.
`epochHybridExp` returns the adversary's output from the initial state.

**Results.** Hybrid zero equals the real-key fixed-bit experiment. For every
`i : ℕ` and `t : ℕ` with `t ≠ i + 1`, the challenge computations in hybrids
`i` and `i + 1` agree.

**Proof.** Simplify the arithmetic predicate selecting the challenge bit.
`OppUniKEM.Security.IdealHybrids` uses this epoch convention with its
auxiliary encapsulated-key receive operation.
-/

open OracleSpec OracleComp

namespace SCKAScheme

variable {IK StA StB I Rho Rand : Type} [SampleableType I] [DecidableEq I]

/-- Hybrid `i` uses random responses exactly for positive epochs at most
`i`. Challenge eligibility, corruption, leakage, and message delivery use
the same guards and state transitions as the security experiment. -/
-- ANCHOR: epochHybridImpl
def epochHybridImpl (i : ℕ) (exposureA : ExposurePolicy StA Rand)
    (exposureB : ExposurePolicy StB Rand)
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) :
    QueryImpl (sckaSecuritySpec StA StB I Rho Rand)
      (StateT (GameState StA StB I Rho) ProbComp) :=
  sckaCorrectnessImpl scka
    + oracleSendArleak exposureA.send scka + oracleSendBrleak exposureB.send scka
    + (fun t => oracleChall (decide (0 < t ∧ t ≤ i)) StA StB I Rho t)
    + oracleCorruptA exposureA.corrupt StB I Rho + oracleCorruptB exposureB.corrupt StA I Rho
-- ANCHOR_END: epochHybridImpl

/-- Run adversary `A` in epoch hybrid `i`, returning its raw Boolean guess.
Initialization is identical to the fixed-bit security experiments. -/
def epochHybridExp (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (adv : SCKAAdversary StA StB I Rho Rand) (i : ℕ)
    (exposureA : ExposurePolicy StA Rand)
      (exposureB : ExposurePolicy StB Rand) : ProbComp Bool := do
  let ik ← scka.initKeyGen
  let stA ← scka.initA ik
  let stB ← scka.initB ik
  let (guess, _) ← (simulateQ (epochHybridImpl i exposureA exposureB scka) adv).run
    (initGameState stA stB)
  return guess

/-- Hybrid zero uses the real-key mode at every epoch, so its oracle implementation is
exactly the real fixed-bit implementation, on every game state. -/
theorem epochHybridImpl_zero (exposureA : ExposurePolicy StA Rand)
    (exposureB : ExposurePolicy StB Rand)
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) :
    epochHybridImpl 0 exposureA exposureB scka =
      sckaSecurityImpl false exposureA exposureB scka := by
  have h : (fun t => oracleChall (decide (0 < t ∧ t ≤ 0)) StA StB I Rho t) =
      oracleChall false StA StB I Rho := by
    funext t
    change ℕ at t
    have ht : ¬(0 < t ∧ t ≤ 0) := by omega
    simp only [ht, decide_false]
  unfold epochHybridImpl sckaSecurityImpl
  rw [h]

/-- Hybrid zero has exactly the real fixed-bit experiment's computation. -/
theorem epochHybridExp_zero (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (adv : SCKAAdversary StA StB I Rho Rand)
    (exposureA : ExposurePolicy StA Rand) (exposureB : ExposurePolicy StB Rand) :
    epochHybridExp scka adv 0 exposureA exposureB =
      securityExpFixedBit scka adv false exposureA exposureB := by
  simp only [epochHybridExp, epochHybridImpl_zero, securityExpFixedBit]

omit [DecidableEq I] in
/-- Adjacent hybrids use identical challenge algorithms at every epoch
except `i + 1`; only that epoch is newly randomized. -/
theorem epochHybrid_challenge_eq_of_ne (i t : ℕ) (hne : t ≠ i + 1) :
    oracleChall (decide (0 < t ∧ t ≤ i + 1)) StA StB I Rho t =
      oracleChall (decide (0 < t ∧ t ≤ i)) StA StB I Rho t := by
  have h : (0 < t ∧ t ≤ i + 1) ↔ (0 < t ∧ t ≤ i) := by omega
  simp only [h]

end SCKAScheme
