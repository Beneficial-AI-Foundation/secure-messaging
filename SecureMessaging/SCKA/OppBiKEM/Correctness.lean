/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Gavran, Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Correctness.Quantitative.Main

/-!
# Opp-BiKEM-CKA — Correctness

Opp-BiKEM-CKA runs one KEM instance per epoch, with the parties alternating roles: the
requester of epoch `e` (A for even `e`, B for odd `e`) transmits a fresh public key, the
responder answers with an encapsulation to it, and each payload travels as erasure-coded
chunks.

Let:

* `Π := scheme kem hDet ecEk ecCt leak` be the instantiated Opp-BiKEM-CKA scheme;
* `kem` be its KEM, with deterministic decapsulation `hDet`;
* `ecEk`, `ecCt` be erasure codes for public keys and ciphertexts;
* `leak` be the randomness exposed by leaking sends; the correctness game makes only plain
  sends, so `leak` plays no role in correctness;
* `G(Adv) := SCKAScheme.correctnessExp Π Adv` — the adversary `Adv` adaptively selects oracle
  queries, the game operations `SendA`, `SendB`, `RecvA`, `RecvB`, and `Unif`; a receive
  oracle may deliver any previously generated honest message (delay, reordering, duplication,
  replay); the game returns the conjunction of all protocol correctness assertions;
* `ε := kem.correctnessError`.

## Results and proofs

Assume that `kem` has deterministic decapsulation and that `ecEk` and `ecCt` are correct.
For every SCKA correctness adversary `Adv`, we have:

* `correctness_failure_le` — if `Adv` makes at most `q` send queries, then
  `Pr[G(Adv) = false] ≤ q · ε`;
* `correctness_true_ge` — under the same hypotheses, `Pr[G(Adv) = true] ≥ 1 - q · ε`;
* `correctness_of_perfectKEM` — a perfectly correct KEM gives `Pr[G(Adv) = true] = 1`
  without a query bound; `correctness_of_perfectKEM'` is the `ε = 0` instance of
  `correctness_true_ge`;
* `sends_never_rejected_of_perfectKEM`, `sends_never_rejected_of_noFailure` — `send` never
  takes its error exits (a missing own public key, a missing decoded peer key) on a reachable
  state: always for a perfectly correct KEM, and otherwise as long as no KEM instance has
  completed inconsistently. The correctness game does not observe these exits.

`SendQueryBound Adv q` states that `Adv` makes at most `q` queries to `SendA` and `SendB`
combined; `Unif`, `RecvA`, and `RecvB` queries are not counted.

The perfect-KEM theorem is proved in `Correctness.MainInvariant.Game` from the main invariant
of `Correctness.MainInvariant`. The quantitative bounds are proved in
`Correctness.Quantitative.Main`, using the generic tracked game of `SCKA.Correctness.Tracked`
and the conditional KEM error of `KEM.CorrectnessError`.
-/
