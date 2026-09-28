/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.OneStep
import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction.Composition
import ToVCVio.OracleComp.SimSemantics.StateT.ExpectedPayoffBound

/-!
# KEM-failure probability in the security game

**Assumptions.** Fix deterministic KEM decapsulation, correct erasure codes,
and on/off and leakage witnesses. Write `ε = kem.correctnessError`.

**Statement.** For every bit `b : Bool`, budget `q : ℕ`, and adversary `A`
with `SecuritySendQueryBound A q`, the tracked fixed-bit execution from
`(initialGame, false)` satisfies `Pr[bad_final = true] ≤ q · ε`.
If `ε = 0`, that probability is zero. The persistent flag records detected
KEM inconsistency, including after erasure of the affected epoch's material.

**Proof.** Compose the `OneStep` expectation bound over A's query budget.
The initial potential is zero and the final potential dominates the failure
indicator. On/off factorization identifies the error allowance with `ε`.
`Endpoints` uses this probability to bound each real/auxiliary acceptance gap.
-/

open OracleSpec OracleComp KEMScheme ENNReal

namespace oppUniKemCKA.Security

open Reduction.Internal

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Assume deterministic decapsulation, correct erasure codes, and on/off
and leakage witnesses. For every bit `b`, budget `q`, and adversary `adv`
with `SecuritySendQueryBound adv q`, the tracked execution from
`(initialGame, false)` satisfies `Pr[bad_final = true] ≤ q · ε`, where
`ε = kem.correctnessError ProbCompRuntime.probComp`. Persistence of `bad`
includes detected inconsistencies whose local material has since been erased. -/
-- ANCHOR: security_kem_failure_le
theorem kem_failure_probability_le
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff) (b : Bool)
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q) :
    Pr[fun z => z.2.2 = true |
      (simulateQ (trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b) adv).run
        (initialGame (Sym := Sym) kem onoff, false)] ≤
      (q : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp := by
  have hpres := trackedSecurityImpl_preserves kem onoff hDet ecEk hEk ecCt0 hCt0
    ecCt1 hCt1 leak b
  have hinit := tracked_initial_inv kem onoff hDet ecEk ecCt0 ecCt1
    ecEk.ec.nchunk_pos ecCt0.ec.nchunk_pos
  have hscore₀ : trackedFailureScore kem onoff
      (initialGame (Sym := Sym) kem onoff, false) = 0 := by
    simp [trackedFailureScore, currentFailurePotential, initialGame, initialA, initialB,
      SCKAScheme.initGameState, Option.map₂]
  have hscore := expectedPayoff_simulateQ_run_le
    (trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b)
    (trackedInv kem onoff hDet ecEk ecCt0 ecCt1)
    (trackedFailureScore kem onoff) (fun t => isSecuritySendQuery t = true)
    (factorCorrectnessError kem onoff) hpres
    (trackedSecurity_score_step_le kem onoff hDet ecEk ecCt0 ecCt1 leak b)
    adv q hq (initialGame kem onoff, false) hinit
  rw [hscore₀, zero_add, factorCorrectnessError_eq] at hscore
  exact (tracked_bad_probability_le_score kem onoff _).trans hscore
-- ANCHOR_END: security_kem_failure_le

/-- Under the assumptions of `kem_failure_probability_le`, for every
fixed bit and adversary with a finite send budget, zero KEM correctness
error implies `Pr[bad_final = true] = 0`. -/
theorem kem_failure_probability_eq_zero
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff) (b : Bool)
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q)
    (hPerfect : kem.correctnessError ProbCompRuntime.probComp = 0) :
    Pr[fun z => z.2.2 = true |
      (simulateQ (trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b) adv).run
        (initialGame (Sym := Sym) kem onoff, false)] = 0 := by
  have h := kem_failure_probability_le kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
    leak b adv q hq
  simpa only [hPerfect, mul_zero, nonpos_iff_eq_zero] using h

end oppUniKemCKA.Security
