/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Endpoints
import SecureMessaging.SCKA.OppUniKEM.Security.IdealBounds
import SecureMessaging.SCKA.OppUniKEM.Security.IdealStopping
import SecureMessaging.SCKA.OppUniKEM.Security.ZeroEpoch
import SecureMessaging.SCKA.OppUniKEM.Security.ZeroSend
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Relation
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Oracle
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.ChallengeSampling
import SecureMessaging.SCKA.OppUniKEM.Security.Theorem
import SecureMessaging.SCKA.OppUniKEM.Security.HybridBound
import SecureMessaging.SCKA.Security.Bookkeeping

/-!
# Opp-UniKEM SCKA security

## Parameters and security statement

Let `kem` be a KEM with finite nonempty key space `K`, public-key space `PK`,
secret-key space `SK`, and ciphertext space `C`. Keys are sampled uniformly
when a challenge is randomized. An `OnOffStructure` splits a ciphertext into
`(ct₀, ct₁)` and factors encapsulation into a public-key-independent offline
phase and an online phase. Let `Π` be `oppUniKemCKA.scheme` instantiated with
this structure, deterministic decapsulation, and correct erasure codes for
`PK`, `onoff.C₀`, and `onoff.C₁`, with symbol type `Sym`.
The witness `OnOffRandLeak` supplies leaking versions
of the three sampling algorithms whose coin-forgetting marginals equal
the ordinary algorithms.

An adversary `A : SecurityAdversary leak Sym` may adaptively send, request
send coins, corrupt either party, challenge epochs, and deliver any
previously sent message by its index. Delivery may be delayed, reordered,
or repeated. For `q : ℕ`, `SecuritySendQueryBound A q` bounds the combined
number of ordinary and leaking sends by `q` on every response path.
Other queries may occur adaptively in any number and order.

Write `ε` for the KEM correctness error, interpreted as a real number.
The theorem `oppUniKemCKA.security`, with explicit reduction
`B := Security.Embedding.securityReduction … A q`, is

`AdvGuess_SCKA(Π, A) ≤ (q / 2) · AdvINDCPA_KEM(kem, B) + q · ε`.

Here `AdvGuess_SCKA` is the absolute deviation of guessing success from
`1/2`. The fixed-bit SCKA distinguishing advantage is the absolute difference
of acceptance probabilities when eligible challenges return real keys
(`b = false`) or fresh uniform keys (`b = true`); it is twice the guessing
advantage. The existing KEM IND-CPA advantage equals the absolute difference
between its real-key and uniform-key branch acceptance probabilities.

**Results.** `security` proves the bound for every send budget, including
zero. `security_perfectKEM` removes the correctness term when the KEM is
perfectly correct; `security_zero_sends` proves advantage zero with no sends.
The reduction is explicit. Its two fixed branches are identified with the
stopped adjacent auxiliary hybrids, whose signed differences equal those
of the original hybrids by exposure cancellation.

## Corrected exposure game

For a leaking send with old state `s`, new state `s'`, and returned coins `r`,
the game computes `E = exposure.send s s' r` using that party's exposure policy.
It rejects the send if `E` intersects the challenged set; otherwise it adds
`E` to the exposed set. For corruption it uses `exposure.corrupt s`. These
policies are game parameters, separate from the protocol algorithms. In
Opp-UniKEM, key-generation, offline, and online coins expose the current
epoch. Deterministic retransmissions add nothing.
An exposed or previously challenged epoch cannot be challenged again.

This corrects the earlier rule that considered only the change in state
vulnerability. Online coins can reveal the key even when the vulnerable set
remains `{t}`. The correction therefore weakens the original SCKA requirement
by excluding such compromised challenges. The KEM IND-CPA game is unchanged.
The trace explaining this issue is documented in `OppUniKEM.Construction`.

## Constructions and proof strategy

1. **Transcript and failure monitor.** Reuse `EpochTranscript`,
   `TranscriptConsistent`, and `reachableInv` from correctness. Coin-forgetting
   equalities transfer send invariants to leaking sends. A persistent flag
   records any KEM inconsistency, even after its local material is erased.
   The tracked failure potential increases in expectation by at most `ε`
   per counted send, proving a total failure probability at most `q · ε`.
2. **Auxiliary execution.** At completion of an online ciphertext, A uses
   B's recorded encapsulated key. Before KEM inconsistency this equals the
   actual decapsulation result. The identical-until-bad theorem therefore
   bounds each fixed-bit real/auxiliary acceptance gap by `q · ε`.
3. **Epoch hybrids.** Auxiliary hybrid `H_i` randomizes eligible challenge
   responses for epochs `1, …, i`. It retains honest keys in both key tables.
   Epoch/send accounting bounds recorded epochs by `q`, and a separate
   invariant excludes epoch zero. These facts identify `H_0` with the
   auxiliary real experiment and `H_q` with the auxiliary random experiment.
4. **Selected-epoch reduction.** The reduction selects `e` uniformly in
   `1, …, q`, embeds the KEM public key and split challenge ciphertext at
   epoch `e`, and samples other epochs honestly. Present-but-unavailable
   secret keys, offline states, coins, and honest keys are represented
   explicitly. Erasure remains distinguishable from unavailability.
   The supplied KEM challenge key is used only in challenge responses.
   A permitted exposure requiring unavailable material terminates with
   output `false`; rejected exposures continue normally. Exposure cancellation
   proves equal contributions from terminated paths. The per-query relation
   compares the simulator to an honest execution with fixed selected material.
   Preserved transcript, source, and recorded-key invariants lift this relation
   to every adaptive execution and identify its two challenge branches.
   Successive sampling stages then defer the online, offline, and key-generation
   components to their protocol calls.
5. **Combining bounds.** The signed adjacent-hybrid differences telescope.
   Uniform epoch selection gives their average as the reduction's signed
   KEM branch difference, producing the factor `q`. The two correctness
   endpoints contribute `2qε` to distinguishing advantage. Dividing by two
   converts to guessing advantage, yielding the factors `q/2` and `qε`.
   The zero-send case is proved separately; setting `ε = 0` removes the
   correctness term in `security_perfectKEM`.

## File structure

All paths below are relative to `OppUniKEM/Security/`.

| Files | Mathematical role |
| --- | --- |
| `Basic`, `Leakage` | Interface, send budget, and leakage marginal/exposure laws. |
| `Invariant`, `EpochBound` | Transcript preservation and epoch accounting. |
| `Tracked`, `Score`, `OneStep`, `FailureBound` | Failure monitor, potential, and `qε` bound. |
| `CounterBound` | Bounds successful sends by the adversary's send-query budget. |
| `Ideal`, `IdealReceive`, `IdealGame` | Auxiliary game and agreement before failure. |
| `Endpoints` | The two fixed-bit correctness-error endpoint bounds. |
| `IdealBounds`, `ZeroEpoch`, `IdealHybrids` | Epoch bounds and auxiliary hybrid endpoints. |
| `IdealStopping` | Exposure cancellation and persistent challenge protection. |
| `Reduction/Primitives` | KEM samplers with unavailable selected-epoch material. |
| `Reduction/Simulator` | Epoch selection, exposure termination, and IND-CPA adversary. |
| `Reduction/Relation` | Marks honest states for comparison with symbolic simulator states. |
| `Reduction/Branches` | Fixed KEM branches and uniform epoch averaging. |
| `Reduction/{Material,Pinned,Game}` | Selected samples and the honest intermediate game. |
| `Reduction/{SendShape,Send,Receive}` | Local output shapes and marking relations. |
| `Reduction/{OracleSend,OracleReceive,OracleLeakage}` | Send and receive game-state relations. |
| `Reduction/{Challenge,Corruption,Oracle}` | Exposure and challenge relations; all-query theorem. |
| `Reduction/ChallengeSampling` | The supplied challenge key is used at most once. |
| `Reduction/{Sources,SourcePreservation,Support}` | Source fields and honest send support. |
| `Reduction/Invariant` | Transcript and source preservation in the honest intermediate game. |
| `Reduction/Simulation` | Whole-execution equality between the reduction and stopped honest game. |
| `Reduction/{Keys,HybridGame}` | Recorded selected key and the two pinned challenge branches. |
| `Reduction/SamplingStages` | Games for successive online, offline, and key-generation deferral. |
| `Reduction/{OnlineUse,OnlineFirstUse,OnlineSampling}` | One-use facts for the online sample. |
| `Reduction/{OnlineFresh,OnlineOracle}` | Online deferral through the complete security game. |
| `Reduction/{SourceUse,SourceSuccess,SourceFirstUse}` | Source phases and leakage guards. |
| `Reduction/{OfflineFresh,OfflineOracle,OfflineIndependence}` | Offline query comparisons. |
| `Reduction/{KeygenOracle,KeygenIndependence}` | Key-generation query comparisons. |
| `Reduction/{OfflineSampling,KeygenSampling}` | Source deferral for adaptive adversaries. |
| `Reduction/{UnusedMaterial,DeferredMaterial}` | Elimination of stored selected-epoch material. |
| `Reduction/Adjacent` | Adjacent-hybrid correspondence, cancellation, and telescoping. |
| `Theorem` | Security inequality and perfect-correctness corollary for the explicit reduction. |
| `HybridBound` | Guessing advantage bounded by half the endpoint hybrid gap plus `qε`. |
| `ZeroSend` | Equality of fixed-bit experiments when no send query is made. |

Protocol-independent SCKA guard and bookkeeping lemmas are in
`SecureMessaging/SCKA/Security/`. Generic probability normalization,
state-dependent sampling, query-budget, stopping, and identical-until-bad
results are in the independent `ToVCVio` library.
-/
