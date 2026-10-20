/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Adjacent
import SecureMessaging.SCKA.OppUniKEM.Security.Endpoints
import SecureMessaging.SCKA.OppUniKEM.Security.IdealHybrids

/-!
# Opp-UniKEM security bound

Let `Π := scheme kem onoff hDet ecEk ecCt0 ecCt1 leak` be Opp-UniKEM with deterministic
decapsulation and correct erasure codes, and with exposure policies `exposureA`, `exposureB`.
Let `adv` be a security adversary with `SecuritySendQueryBound adv q`, let
`ε := (kem.correctnessError ProbCompRuntime.probComp).toReal`, and let
`B := Security.Embedding.securityReduction … adv q` be the explicit IND-CPA adversary of
`Reduction/Simulator`. Then `security` proves, for every `q : ℕ`,

`AdvGuess_SCKA(Π, adv) ≤ (q / 2) · Adv_IND-CPA(kem, B) + q · ε`,

and `security_perfectKEM` omits `q · ε` for a perfectly correct KEM. Here `AdvGuess_SCKA` is
`|Pr[win] - 1/2|`, half the acceptance gap of the two fixed-bit games, and `Adv_IND-CPA`
(`IND_CPA_Advantage`) is the full acceptance gap of the two IND-CPA branches
(`IND_CPA_Advantage_eq_fixed_branch_dist`).
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Assume deterministic decapsulation and correct erasure codes. For every adversary `adv` and
every `q : ℕ`, without a send bound, the ideal hybrids satisfy
`|Pr[H_0 = true] - Pr[H_q = true]| / 2 ≤ (q / 2) · Adv_IND-CPA(kem, B)` for
`B := Embedding.securityReduction … adv q`. -/
theorem ideal_security_guess_le
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff)
    (adv : SecurityAdversary leak Sym) (q : ℕ) :
    |(Pr[= true | idealEpochHybridExp kem onoff hDet ecEk ecCt0 ecCt1 leak adv 0]).toReal -
      (Pr[= true | idealEpochHybridExp kem onoff hDet ecEk ecCt0 ecCt1 leak adv q]).toReal| / 2 ≤
    ((q : ℝ) / 2) * kem.IND_CPA_Advantage ProbCompRuntime.probComp
      (Embedding.securityReduction kem onoff ecEk ecCt0 ecCt1 leak adv q) := by
  have h := Embedding.hybrid_gap_eq_query_factor kem onoff hDet ecEk hEk
    ecCt0 hCt0 ecCt1 hCt1 leak adv q
  linarith

end oppUniKemCKA.Security

namespace oppUniKemCKA

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Let `kem` have deterministic decapsulation `hDet`, an on/off factorization `onoff`, and a
leakage witness `leak`, and let the three erasure codes be correct. For every SCKA adversary `adv`
against `Π := scheme kem onoff hDet ecEk ecCt0 ecCt1 leak` with exposure policies `exposureA`,
`exposureB`, if `adv` makes at most `q` ordinary and leaking sends on every oracle-response path,
then `AdvGuess_SCKA(Π, adv) ≤ (q / 2) · Adv_IND-CPA(kem, B) + q · ε`, where
`B := Security.Embedding.securityReduction … adv q` and `ε` is the KEM correctness error.
Challenges, corruptions, and receives of recorded messages are adaptive and unbounded. -/
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
      (q : ℝ) * (kem.correctnessError ProbCompRuntime.probComp).toReal
-- ANCHOR_END: security
    := by
  have h := Security.security_guess_le_hybrid_gap kem onoff hDet ecEk hEk
    ecCt0 hCt0 ecCt1 hCt1 leak adv q hq
  have hideal := Security.ideal_security_guess_le kem onoff hDet ecEk hEk
    ecCt0 hCt0 ecCt1 hCt1 leak adv q
  linarith

/-- Under the assumptions of `security`, if the KEM is perfectly correct, then
`AdvGuess_SCKA(Π, adv) ≤ (q / 2) · Adv_IND-CPA(kem, B)`. -/
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
      (Security.Embedding.securityReduction kem onoff ecEk ecCt0 ecCt1 leak adv q)
-- ANCHOR_END: security_perfectKEM
    := by
  have herror := (KEMScheme.correctnessError_eq_zero_iff_perfectlyCorrect
    kem ProbCompRuntime.probComp).2 hkem
  simpa only [herror, ENNReal.toReal_zero, mul_zero, add_zero] using
    security kem onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1 leak adv q hq

end oppUniKemCKA
