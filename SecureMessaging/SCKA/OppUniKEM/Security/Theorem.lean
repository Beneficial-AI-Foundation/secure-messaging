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

**Setting.** Let `Π := scheme kem onoff hDet ecEk ecCt0 ecCt1 leak` be Opp-UniKEM with
deterministic decapsulation, correct erasure codes for the public key and both ciphertext
components, and the on/off and leakage witnesses `onoff`, `leak`. Let `adv` be a security
adversary with `SecuritySendQueryBound adv q`, let `ε := (kem.correctnessError).toReal`, and let
`B := Security.Embedding.securityReduction … adv q` be the explicit IND-CPA adversary of
`Reduction/Simulator`. Write `p_i := Pr[idealEpochHybridExp adv i = true]`.

**Results.** `IdealHybrids` proved `security_guess_le_hybrid_gap`: the guessing advantage of
`adv` is at most `|p_0 - p_q| / 2 + q · ε`. Here:

- `ideal_security_guess_le`: half the auxiliary `H_0`/`H_q` acceptance gap is at most
  `(q / 2) · Adv_IND-CPA(kem, B)`. This ideal-world bound needs no correctness hypothesis.
- `security`: the guessing advantage of `adv` against `Π` with exposure policies `exposureA`,
  `exposureB` is at most `(q / 2) · Adv_IND-CPA(kem, B) + q · ε`, for every `q` including `0`.
- `security_perfectKEM`: for a perfectly correct KEM the bound is `(q / 2) · Adv_IND-CPA(kem, B)`.

At `q = 0` both sides of `security` vanish, so no sends give guessing advantage `0`.

The SCKA guessing advantage is `|Pr[win] - 1/2|`, half the distinguishing gap of the two
fixed-bit games; `IND_CPA_Advantage` is the full gap of the two IND-CPA branches
(`IND_CPA_Advantage_eq_fixed_branch_dist`).
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Ideal-world bound: half the auxiliary `H_0`/`H_q` acceptance gap is at most
`(q / 2)` times the explicit reduction's KEM IND-CPA advantage. This uses only
deterministic decapsulation, correct erasure codes, and the on/off and leakage
witnesses; in particular it needs no KEM correctness hypothesis. -/
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
  have h := Security.security_guess_le_hybrid_gap kem onoff hDet ecEk hEk
    ecCt0 hCt0 ecCt1 hCt1 leak adv q hq
  have hideal := Security.ideal_security_guess_le kem onoff hDet ecEk hEk
    ecCt0 hCt0 ecCt1 hCt1 leak adv q
  linarith
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
