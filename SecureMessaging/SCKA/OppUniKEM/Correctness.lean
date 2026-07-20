/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Correctness.Perfect
import SecureMessaging.SCKA.OppUniKEM.Correctness.KEM
import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction

/-!
# Opp-UniKEM-CKA — Correctness

This directory proves correctness of the opportunistic UniKEM sparse
continuous key-agreement construction in the full SCKA correctness experiment.
The experiment permits an adaptive environment to request sends and to deliver
any previously generated honest message in any order and any number of times.
Thus the result covers message delay, reordering, duplication, and replay; it
does not assume a reliable or in-order transport.

## Mathematical statement

Assume that the three erasure codes reconstruct their payload from every
threshold-size honest subset, that each threshold is positive, that
decapsulation is deterministic, and that the on/off encapsulation factors the
ordinary KEM encapsulation distribution.

* If the KEM is perfectly correct, then for every correctness adversary the
  protocol correctness experiment returns `true` with probability one.
* More generally, let `δ` bound the ordinary KEM correctness error.  If an
  adversary makes at most `q` total send queries, then

  `1 - Pr[protocol correctness succeeds] ≤ q · δ`.

The complement of success counts both an explicit `false` result and missing
probability mass.  In the present theorem the game is a `ProbComp`, hence it
is total and the missing mass is zero; the bound is equivalently a bound on
the probability of returning `false`.

Only sends are charged: either party may make the first random choice of a new
KEM epoch.  Random-index queries and all receive queries have zero cost.

## Proof architecture

The proof separates deterministic protocol reasoning from probabilistic KEM
reasoning.

1. **Honest reconstruction.**  A subset of an honestly encoded codeword is
   shown to decode exactly at the erasure-code threshold and then to recover
   the serialized payload.
2. **Transcript invariant.**  A mathematical transcript records the honest
   KEM samples of every epoch.  A reachability invariant relates it to local
   states, accumulated chunks, sent-message histories, key tables, and the two
   current epochs.  Each protocol operation preserves this relation for every
   supported outcome.
3. **Perfect correctness.**  Perfect KEM correctness makes every completed
   transcript epoch consistent.  The invariant then implies every assertion
   in the SCKA experiment, and preservation through the adversary's complete
   interaction gives probability-one correctness.
4. **Conditional KEM error.**  For imperfect correctness, the proof defines
   the remaining correctness error after fixing a key pair, an offline
   encapsulation, or both.  Tower identities identify the expectation of each
   conditional quantity with the ordinary average KEM error.  Both an
   explicit mismatch and missing mass are assigned error one.
5. **Potential argument.**  The execution is augmented with an absorbing bad
   event and the conditional error of its unresolved epoch.  Starting an epoch
   costs at most one KEM error in expectation; completing it realizes the
   existing conditional error; deterministic sends and arbitrary receives do
   not increase it.
6. **Adaptive reduction.**  Induction over the adversary's interaction tree
   bounds the final expected potential by `q · δ`.  A failed protocol
   assertion implies the bad event, so its probability is bounded by that
   same expectation.

## Files

* `Correctness.Perfect` develops honest reconstruction, the transcript
  invariant, oracle preservation, and perfect correctness.
* `Correctness.KEM` proves on/off factorization and the conditional-error tower
  identities.
* `Correctness.Reduction` lifts the local expected-error bounds through an
  adaptive adversary and proves the final quantitative theorem.

The principal public theorems are `oppUniKemCKA.correctness` and
`oppUniKemCKA.correctness_error_le_of_deltaCorrect`; the false-result-only
bound remains available as `oppUniKemCKA.correctness_failure_le_of_deltaCorrect`.
-/
