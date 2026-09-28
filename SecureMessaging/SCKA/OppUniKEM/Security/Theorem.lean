/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Adjacent
import SecureMessaging.SCKA.OppUniKEM.Security.HybridBound
import SecureMessaging.SCKA.OppUniKEM.Security.ZeroSend

/-!
# Opp-UniKEM security bound

**Parameters.** Let `Π` be Opp-UniKEM instantiated with a KEM, its on/off
factorization and leakage witnesses, deterministic decapsulation, and correct
erasure codes. Let `A` make at most `q` ordinary or leaking sends. Write `ε`
for the KEM correctness error and `B = Embedding.securityReduction … A q`.

**Theorem.** `AdvGuess_SCKA(Π,A) ≤ (q/2) AdvINDCPA_KEM(B) + q ε`.
SCKA guessing advantage is half its fixed-bit distinguishing gap; KEM
IND-CPA advantage uses the full distinguishing gap. Perfect correctness
removes the additive term. The zero-send case has advantage zero.

**Proof.** `HybridBound` contributes the two correctness endpoints, costing
`q ε` in guessing advantage. `Reduction.Adjacent` identifies the remaining
hybrid gap with `q` times B's IND-CPA advantage by signed telescoping and
uniform epoch selection. The zero-send theorem handles `q = 0` directly.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Assume deterministic KEM decapsulation, correct erasure codes, and
on/off factorization and leakage witnesses. For every full-interface SCKA
adversary `adv` making at most `q` ordinary or leaking sends, its guessing
advantage against the corrected Opp-UniKEM game is at most `(q/2)` times
the explicit reduction's KEM IND-CPA advantage plus `q` times the KEM
correctness error. This includes `q = 0`, adaptive challenges and corruptions,
and arbitrary delivery of previously sent messages. -/
-- ANCHOR: security
theorem security
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff)
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q) :
    SCKAScheme.sckaGuessAdvantage (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)
      adv (exposureA kem onoff leak) (exposureB kem onoff leak) ≤
    ((q : ℝ) / 2) * kem.IND_CPA_Advantage ProbCompRuntime.probComp
      (Security.Embedding.securityReduction kem onoff ecEk ecCt0 ecCt1 leak adv q) +
      (q : ℝ) * (kem.correctnessError ProbCompRuntime.probComp).toReal := by
  by_cases hzero : q = 0
  · subst q
    rw [security_zero_sends kem onoff hDet ecEk ecCt0 ecCt1 leak adv hq]
    simp
  · have h := Security.security_guess_le_hybrid_gap kem onoff hDet ecEk hEk
      ecCt0 hCt0 ecCt1 hCt1 leak adv q hq
    rw [Security.Embedding.hybrid_gap_eq_query_factor kem onoff hDet ecEk hEk
      ecCt0 hCt0 ecCt1 hCt1 leak adv q hzero] at h
    convert h using 1
    ring
-- ANCHOR_END: security

/-- Under the assumptions of `security`, if the KEM is perfectly correct,
then every adversary with send budget `q` has SCKA guessing advantage at most
`(q/2)` times the explicit reduction's IND-CPA advantage. -/
-- ANCHOR: security_perfectKEM
theorem security_perfectKEM
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff) (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : SecuritySendQueryBound adv q) :
    SCKAScheme.sckaGuessAdvantage (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)
      adv (exposureA kem onoff leak) (exposureB kem onoff leak) ≤
    ((q : ℝ) / 2) * kem.IND_CPA_Advantage ProbCompRuntime.probComp
      (Security.Embedding.securityReduction kem onoff ecEk ecCt0 ecCt1 leak adv q) := by
  have herror := (KEMScheme.correctnessError_eq_zero_iff_perfectlyCorrect
    kem ProbCompRuntime.probComp).2 hkem
  simpa only [herror, ENNReal.toReal_zero, mul_zero, add_zero] using
    security kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1 leak adv q hq
-- ANCHOR_END: security_perfectKEM

end oppUniKemCKA
