/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Endpoints
import SecureMessaging.SCKA.OppUniKEM.Security.IdealInvariants
import SecureMessaging.SCKA.OppUniKEM.Security.IdealStopping
import SecureMessaging.SCKA.OppUniKEM.Security.Theorem
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Relation
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Oracle
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.HybridGame
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

1. `Theorem`: `security` combines `security_guess_le_hybrid_gap` and
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
5. `Reduction/HybridGame`, `Reduction/SamplingStages`: `fixedBranch_eq_pinnedHybrid` equates the
   acceptance probability of `fixedBranch adv e b` with that of the stopped pinned hybrid with
   mode bit `!b`, averaged over material; the stored samples are then deferred to their protocol
   calls. `Reduction/SourceUse` shows that each stored sample is used at most once, and
   `Reduction/{Online,Offline,Keygen}Deferral` prove the three deferrals.
6. `IdealStopping`, `Reduction/Adjacent`: `fixedBranch_eq_ideal` equates the acceptance
   probability of `fixedBranch adv e b` with that of the ideal game with mode
   `adjacentMode e (!b)`, stopped at the exposure of `e`. Stopping preserves the signed difference
   of adjacent hybrids (`idealEpochHybrid_signed_gap_stop_eq`), so `fixedBranch_signed_gap_eq`
   gives `Pr[fixedBranch adv (i+1) true = true] - Pr[fixedBranch adv (i+1) false = true] =
   Pr[H_i = true] - Pr[H_{i+1} = true]`. Averaging over `e` and telescoping gives
   `hybrid_gap_eq_query_factor`: `|Pr[H_0 = true] - Pr[H_q = true]| = q · AdvINDCPA_KEM(kem, B)`.

Supporting modules: `Basic` (interface, send budget, leakage marginals); `Invariant` and
`IdealInvariants` (transcript consistency, send and epoch accounting); `SCKA.Security` and
`SCKA/Security/` (shared guard and bookkeeping results); ToVCVio (generic sampling, stopping, and
probability results).
-/
