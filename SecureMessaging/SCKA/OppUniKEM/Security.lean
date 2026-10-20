/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Endpoints
import SecureMessaging.SCKA.OppUniKEM.Security.IdealHybrids
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Adjacent
import SecureMessaging.SCKA.Security

/-!
# Opp-UniKEM SCKA security

**Setting.** Let

- `kem` be a KEM with a finite nonempty key space and deterministic decapsulation `hDet`,
  `onoff` an on/off factorization of its encapsulation, and `leak` leaking samplers whose
  coin-forgetting marginals equal key generation and the two encapsulation phases;
- `ecEk`, `ecCt0`, `ecCt1` be correct erasure codes for the public key and both ciphertext
  components, and `Π := scheme kem onoff hDet ecEk ecCt0 ecCt1 leak`;
- `adv : SecurityAdversary leak Sym` be an adaptive SCKA adversary with
  `SecuritySendQueryBound adv q`: on every oracle-response path, `adv` makes at most `q`
  ordinary and leaking sends in total, including rejected ones. Receive, challenge, corruption,
  and uniform queries are unbounded; a receive delivers a recorded message by index, so
  messages may be delayed, reordered, and replayed.

The game is the SCKA security game of `SCKA.Defs` with the exposure policies `exposureA`,
`exposureB` of `OppUniKEM.Construction`. A challenge at epoch `t` is *eligible* if `t` is neither
exposed nor challenged and a key is recorded for `t`.

**Advantages.** For `b : Bool`, `G_b` answers eligible challenges with recorded keys if
`b = false` and with independent uniform keys if `b = true`. The guessing advantage
`AdvGuess_SCKA(Π, adv) := |Pr[b' = b] - 1/2|`, for a uniform bit `b` and the output `b'` of
`adv`, equals `|Pr[G_true = true] - Pr[G_false = true]| / 2`. The IND-CPA advantage
`AdvINDCPA_KEM(kem, B)` of an adversary `B` equals the full gap between its acceptance
probabilities given the encapsulated key and an independent uniform key
(`IND_CPA_Advantage_eq_fixed_branch_dist`). The correctness error `ε` is the probability that
decapsulation of an honest encapsulation does not return the encapsulated key, including
decapsulation failure.

**Theorem** (`security`). For every `q : ℕ`, with
`B := Security.Embedding.securityReduction … adv q`,

`AdvGuess_SCKA(Π, adv) ≤ (q / 2) · AdvINDCPA_KEM(kem, B) + q · ε`.

`security_perfectKEM` omits `q · ε` for a perfectly correct KEM. The reduction `B` is explicit;
its running time is not formalized.

## Source map

Paths are relative to `OppUniKEM/Security/`, in the order of the proof. The Verso Opp-UniKEM
chapter presents the reduction algorithms and a proof outline.

1. This module: `security` combines `security_guess_le_hybrid_gap` and
   `hybrid_gap_eq_query_factor`.
2. `Endpoints`, `IdealHybrids`: the ideal game `I_b` replaces A's decapsulation by B's recorded
   key, and `security_correctness_endpoint_le` gives
   `|Pr[G_b = true] - Pr[I_b = true]| ≤ q · ε`.
   The ideal hybrid `H_i` answers eligible challenges at epochs `1, …, i` with uniform keys and
   all others with recorded keys, so `H_0 = I_false` and `Pr[H_q = true] = Pr[I_true = true]`.
   Hence `security_guess_le_hybrid_gap`:
   `AdvGuess_SCKA(Π, adv) ≤ |Pr[H_0 = true] - Pr[H_q = true]| / 2 + q · ε`.
3. `Reduction/Simulator`, `Reduction/Material`: `securityReduction` selects an epoch `e`
   uniformly from `1, …, q` and embeds the KEM challenge in the key generation and encapsulation
   of epoch `e`. The simulator's private values are absent, present but unavailable, or known. A
   permitted disclosure of unavailable material terminates the simulation with output `false`; a
   query rejected by an exposure guard returns its rejection. `fixedBranch adv e b` fixes the
   epoch and the IND-CPA bit. `Material` stores one epoch's sampling outputs and coins; a
   *pinned* sampling phase returns them.
4. `Reduction/Simulation`: `run_eq_honestStopped` and `fixedBranch_eq_honestStopped` equate the
   simulator's acceptance probability, for fixed and for averaged material, with that of the
   honest intermediate game stopped at the first query exposing `e`. `Reduction/Relation`, `Game`,
   `Oracle`, and `Sources` give the marking relation, the intermediate games, the per-query
   comparison, and the stored-material invariant.
5. `Reduction/HybridGame`: `fixedBranch_eq_pinnedHybrid` equates the acceptance probability of
   `fixedBranch adv e b` with that of the stopped pinned hybrid with mode bit `!b`, averaged over
   material; its sampling stages defer the stored samples to their protocol calls.
   `Reduction/SourceUse` shows that each stored sample is used at most once, and
   `Reduction/{Online,Offline,Keygen}Deferral` prove the three deferrals.
6. `IdealHybrids`, `Reduction/Adjacent`: `fixedBranch_eq_ideal` equates the acceptance
   probability of `fixedBranch adv e b` with that of the ideal game with mode
   `adjacentMode e (!b)`, stopped at the exposure of `e`. Stopping preserves the signed difference
   of adjacent hybrids (`idealEpochHybrid_signed_gap_stop_eq`), so `fixedBranch_signed_gap_eq`
   gives `Pr[fixedBranch adv (i+1) true = true] - Pr[fixedBranch adv (i+1) false = true] =
   Pr[H_i = true] - Pr[H_{i+1} = true]`. Averaging over `e` and telescoping gives
   `hybrid_gap_eq_query_factor`: `|Pr[H_0 = true] - Pr[H_q = true]| = q · AdvINDCPA_KEM(kem, B)`.

Supporting modules: `Basic` (interface, send budget, leakage marginals); `Invariant`
(transcript consistency, send and epoch accounting); `SCKA.Security` and `SCKA/Security/`
(shared guard and bookkeeping results); ToVCVio (generic sampling, stopping, and probability
results).
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- In the setting above, every adversary `adv` with `SecuritySendQueryBound adv q` satisfies
`AdvGuess_SCKA(Π, adv) ≤ (q / 2) · AdvINDCPA_KEM(kem, B) + q · ε` for
`B := Security.Embedding.securityReduction … adv q`. -/
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
  have hgap := Security.Embedding.hybrid_gap_eq_query_factor kem onoff hDet ecEk hEk
    ecCt0 hCt0 ecCt1 hCt1 leak adv q
  linarith

/-- Under the assumptions of `security`, if the KEM is perfectly correct, then
`AdvGuess_SCKA(Π, adv) ≤ (q / 2) · AdvINDCPA_KEM(kem, B)`. -/
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
