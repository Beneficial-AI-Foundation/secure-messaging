/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Security.Proofs

/-!
# Opp-BiKEM — Security

**Note** This is a fixed module containing only theorem statements (whose proofs are in `Proofs`).

**Setting.** Throughout this module, we consider:

- the Opp-BiKEM protocol `scka := scheme kem hDet ecEk ecCt leak` over a KEM `kem` with
  deterministic decapsulation `hDet`, randomness-leakage package `leak`, and correct erasure
  codes `ecEk` (public keys) and `ecCt` (ciphertexts);
- an SCKA adversary `adv : SecurityAdversary leak Sym` making at most `q` ordinary and leaking
  sends in total on every oracle-response path (`SecuritySendQueryBound adv q`);
- for each *target epoch* `t`, the IND-CPA adversary against `kem`: `R_t := reduction … adv t`,
  constructed from `adv`, which embeds the KEM challenge in the key generation and encapsulation
  of epoch `t` and runs `adv` (`Defs`, explained in `Reduction`);
- the combined adversary `B := securityReduction … adv q`, which chooses one target uniformly
  from `1, …, 2q` and runs its reduction; for `q = 0`, it chooses target `1`.

**Security game and advantage functions.**

Let:
- `G_b` be the SCKA security game of `scka` with its challenge bit fixed to `b`
  (`securityExpFixedBit`), under the exposure policy `exposure` (`Exposure`);
- `AdvGuess_SCKA(scka, adv) := |Pr[b' = b] − 1/2| = |Pr[G_true = true] − Pr[G_false = true]| / 2`
  be the advantage of `adv` in guessing the challenge bit (`sckaGuessAdvantage`). In
  `Pr[b' = b]`, `b ←$ Bool` is drawn once for the run, and `b'` is the adversary's guess.
  The advantage is the distance of its winning probability from `1/2`;
- `AdvINDCPA_KEM(kem, R) := |Pr[R_real = true] − Pr[R_random = true]|` be the advantage of an
  IND-CPA adversary `R` against `kem` (`IND_CPA_Advantage_eq_fixed_branch_dist`), where
  `R_real` and `R_random` are the IND-CPA experiments handing `R` the encapsulated key and an
  independent uniform key;
- `ε` be the KEM correctness error (`kem.correctnessError`): the probability that an honest
  encapsulation `(c, k) ← Encaps(pk)` under `(pk, sk) ← KeyGen` does not decapsulate to `k`.

**Theorem** (`security`). For every `q : ℕ`,

`AdvGuess_SCKA(scka, adv) ≤ q · ε + q · AdvINDCPA_KEM(kem, B)`.

The family bound `security_positive` is
`AdvGuess_SCKA(scka, adv) ≤ q · ε + (1/2) · Σ_{t=1}^{2q} AdvINDCPA_KEM(kem, R_t)`.
Its corollary `security_sum` includes the nonnegative summand at zero, and `security_uniform`
gives `q · ε + q · δ` when every positive-target reduction up to `2q` has advantage at most
`δ`.

The proofs are in `Proofs`, whose module docstring gives the proof structure; the theorems here
delegate to the lemmas of the same name in the namespace `Proofs`. Together with `Defs`, this
module fixes what is proved: a change to a statement here or to a definition in `Defs` changes the
meaning of the result, while the proof modules may change freely.
-/

open OracleSpec OracleComp KEMScheme ENNReal

namespace oppBiKemCKA

variable {K PK SK C Sym : Type} [DecidableEq K] [DecidableEq Sym] [SampleableType K]
  (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
  (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct) (leak : kem.RandLeak)

include hEk hCt in
/-- Assume:

* `ecEk` and `ecCt` are correct erasure codes;
* `0 < t`.

Then the hop at `t` is the IND-CPA advantage of the reduction at target `t`:
`|p_{t+1} − p_t| = AdvINDCPA_KEM(kem, R_t)`, where `p_T := Pr[hybridExp … T adv = true]` and
`R_t := reduction … adv t`. -/
theorem hybrid_hop_eq_reduction (adv : SecurityAdversary leak Sym) (t : ℕ) (ht : 0 < t) :
    |(Pr{let x ← hybridExp kem hDet ecEk ecCt leak (t + 1) adv}[x = true]).toReal -
        (Pr{let x ← hybridExp kem hDet ecEk ecCt leak t adv}[x = true]).toReal| =
      (kem.IND_CPA_Advantage ProbCompRuntime.probComp
        (reduction kem hDet ecEk ecCt leak adv t)).toReal :=
  Proofs.hybrid_hop_eq_reduction kem hDet ecEk ecCt hEk hCt leak adv t ht

include hEk hCt in
/-- Assume:

* `kem` has deterministic decapsulation;
* `ecEk` and `ecCt` are correct erasure codes;
* `adv` makes at most `q` ordinary or leaking sends.

Then `AdvGuess_SCKA(scka, adv) ≤ q · ε + q · AdvINDCPA_KEM(kem, B)`, where `ε` is the
correctness error of `kem` and `B := securityReduction … adv q` chooses a positive target
uniformly from `1, …, 2q` and runs its reduction. For `q = 0`, the bound is zero. -/
-- ANCHOR: security
theorem security (adv : SecurityAdversary leak Sym) (q : ℕ)
    (hq : SecuritySendQueryBound adv q) :
    SCKAScheme.sckaGuessAdvantage (scheme kem hDet ecEk ecCt leak) adv
        (exposure .A leak) (exposure .B leak) ≤
      (q : ℝ) * (kem.correctnessError ProbCompRuntime.probComp).toReal +
      (q : ℝ) * (kem.IND_CPA_Advantage ProbCompRuntime.probComp
        (securityReduction kem hDet ecEk ecCt leak adv q)).toReal
-- ANCHOR_END: security
    :=
  Proofs.security kem hDet ecEk ecCt hEk hCt leak adv q hq

include hEk hCt in
/-- Assume:

* `kem` has deterministic decapsulation;
* `ecEk` and `ecCt` are correct erasure codes;
* `adv` makes at most `q` ordinary or leaking sends.

Then `AdvGuess_SCKA(scka, adv) ≤ q · ε + (1/2) · Σ_{t=1}^{2q} AdvINDCPA_KEM(kem, R_t)`, where `ε`
is the correctness error of `kem` and `R_t := reduction … adv t`. -/
-- ANCHOR: securityPositive
theorem security_positive (adv : SecurityAdversary leak Sym) (q : ℕ)
    (hq : SecuritySendQueryBound adv q) :
    SCKAScheme.sckaGuessAdvantage (scheme kem hDet ecEk ecCt leak) adv
        (exposure .A leak) (exposure .B leak) ≤
      (q : ℝ) * (kem.correctnessError ProbCompRuntime.probComp).toReal +
      (1 / 2 : ℝ) * ∑ i ∈ Finset.range (2 * q), (kem.IND_CPA_Advantage ProbCompRuntime.probComp
        (reduction kem hDet ecEk ecCt leak adv (i + 1))).toReal
-- ANCHOR_END: securityPositive
    :=
  Proofs.security_positive kem hDet ecEk ecCt hEk hCt leak adv q hq

include hEk hCt in
/-- Assume:

* `kem` has deterministic decapsulation;
* `ecEk` and `ecCt` are correct erasure codes;
* `adv` makes at most `q` ordinary or leaking sends.

Then `AdvGuess_SCKA(scka, adv) ≤ q · ε + (1/2) · Σ_{t=0}^{2q} AdvINDCPA_KEM(kem, R_t)`, where `ε`
is the correctness error of `kem` and `R_t := reduction … adv t`. The summand at `t = 0` only
adds its non-negativity to `security_positive`. -/
theorem security_sum (adv : SecurityAdversary leak Sym) (q : ℕ)
    (hq : SecuritySendQueryBound adv q) :
    SCKAScheme.sckaGuessAdvantage (scheme kem hDet ecEk ecCt leak) adv
        (exposure .A leak) (exposure .B leak) ≤
      (q : ℝ) * (kem.correctnessError ProbCompRuntime.probComp).toReal +
      (1 / 2 : ℝ) * ∑ t ∈ Finset.range (2 * q + 1),
        (kem.IND_CPA_Advantage ProbCompRuntime.probComp
          (reduction kem hDet ecEk ecCt leak adv t)).toReal :=
  Proofs.security_sum kem hDet ecEk ecCt hEk hCt leak adv q hq

include hEk hCt in
/-- Assume:

* `kem` has deterministic decapsulation;
* `ecEk` and `ecCt` are correct erasure codes;
* `adv` makes at most `q` ordinary or leaking sends;
* every reduction `reduction adv t` at a positive target `t ≤ 2q` has IND-CPA advantage at
  most `δ`.

Then `AdvGuess_SCKA(scka, adv) ≤ q · ε + q · δ`, where `ε` is the correctness error of `kem`. -/
-- ANCHOR: securityUniform
theorem security_uniform (adv : SecurityAdversary leak Sym) (q : ℕ)
    (hq : SecuritySendQueryBound adv q) (δ : ℝ)
    (hδ : ∀ t, 0 < t → t ≤ 2 * q →
      (kem.IND_CPA_Advantage ProbCompRuntime.probComp
        (reduction kem hDet ecEk ecCt leak adv t)).toReal ≤ δ) :
    SCKAScheme.sckaGuessAdvantage (scheme kem hDet ecEk ecCt leak) adv
        (exposure .A leak) (exposure .B leak) ≤
      (q : ℝ) * (kem.correctnessError ProbCompRuntime.probComp).toReal + (q : ℝ) * δ
-- ANCHOR_END: securityUniform
    :=
  Proofs.security_uniform kem hDet ecEk ecCt hEk hCt leak adv q hq δ hδ

end oppBiKemCKA
