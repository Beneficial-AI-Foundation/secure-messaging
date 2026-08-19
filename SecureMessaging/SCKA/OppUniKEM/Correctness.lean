/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.OnOffKEM.CorrectnessError
import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction

/-!
# Correctness of Opp-UniKEM-CKA

Opp-UniKEM-CKA runs one KEM instance per epoch: party A transmits a fresh
public key, party B answers with a ciphertext sampled in an offline and an
online part, and each payload travels as erasure-coded chunks.

Let:

* `kem` be a KEM with deterministic decapsulation `hDet` and an on/off
  factorization `onoff` of encapsulation;
* `ecEk`, `ecCt0`, `ecCt1` be erasure codes for the public key and the two
  ciphertext components;
* `Π := scheme kem onoff hDet ecEk ecCt0 ecCt1 leak`;
* `G(Adv) := SCKAScheme.correctnessExp Π Adv` — the adversary `Adv`
  adaptively selects oracle queries, the game operations `SendA`, `SendB`,
  `RecvA`, `RecvB`, and `Unif`; a receive oracle may deliver any previously generated honest
  message (delay, reordering, duplication, replay); the game returns the
  conjunction of all protocol correctness assertions;
* `ε := kem.correctnessError`.

## Results and proofs

Assume the erasure codes `ecEk`, `ecCt0`, and `ecCt1` are correct.
For every SCKA correctness adversary `Adv`, we have:

* `correctness_failure_le` — if `Adv` makes at most `q` send queries, then
  `Pr[G(Adv) = false] ≤ q · ε`;
* `correctness_true_ge` — under the same hypotheses,
  `Pr[G(Adv) = true] ≥ 1 - q · ε`;
* `correctness` — as the zero-error corollary, a perfectly correct KEM gives
  `Pr[G(Adv) = true] = 1` without a query bound.

`SendQueryBound Adv q` states that `Adv` makes at most `q` queries to
`SendA` and `SendB` combined; `Unif`, `RecvA`, and `RecvB` queries are not
counted.

The proofs are in `Correctness.Reduction`, using the shared reachability
invariant in `Correctness.Invariant` and the conditional KEM errors in
`KEM.OnOffKEM.CorrectnessError`.
-/

open OracleSpec OracleComp ENNReal KEMScheme

namespace oppUniKemCKA

variable {K PK SK C Sym : Type}

/-- Assume:

* `kem` has deterministic decapsulation;
* `onoff` splits encapsulation into an offline and an online part;
* `ecEk`, `ecCt0`, and `ecCt1` are correct erasure codes with positive
  reconstruction thresholds;
* `adv` makes at most `q` `SendA` and `SendB` queries combined.

Then the Opp-UniKEM-CKA correctness game fails with probability at most
`q · kem.correctnessError`. -/
theorem correctness_failure_le [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEkCorrect : ecEk.ec.Correct)
    (hEkPos : 0 < ecEk.ec.nchunk)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0Correct : ecCt0.ec.Correct)
    (hCt0Pos : 0 < ecCt0.ec.nchunk)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1Correct : ecCt1.ec.Correct)
    (hCt1Pos : 0 < ecCt1.ec.nchunk)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (q : ℕ) (hq : SendQueryBound adv q) :
    Pr[= false |
      SCKAScheme.correctnessExp
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv] ≤
      (q : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp
    := by
  exact correctness_failure_le_reduction kem onoff hDet
    ecEk hEkCorrect hEkPos ecCt0 hCt0Correct hCt0Pos
    ecCt1 hCt1Correct hCt1Pos leak adv q hq

/-- Assume:

* `kem` has deterministic decapsulation;
* `onoff` splits encapsulation into an offline and an online part;
* `ecEk`, `ecCt0`, and `ecCt1` are correct erasure codes with positive
  reconstruction thresholds;
* `adv` makes at most `q` `SendA` and `SendB` queries combined.

Then the Opp-UniKEM-CKA correctness game succeeds with probability at least
`1 - q · kem.correctnessError`. -/
-- ANCHOR: correctnessTrueGe
theorem correctness_true_ge [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEkCorrect : ecEk.ec.Correct)
    (hEkPos : 0 < ecEk.ec.nchunk)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0Correct : ecCt0.ec.Correct)
    (hCt0Pos : 0 < ecCt0.ec.nchunk)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1Correct : ecCt1.ec.Correct)
    (hCt1Pos : 0 < ecCt1.ec.nchunk)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (q : ℕ) (hq : SendQueryBound adv q) :
    Pr[= true |
      SCKAScheme.correctnessExp
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv] ≥
      1 - (q : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp
-- ANCHOR_END: correctnessTrueGe
    := by
  exact correctness_true_ge_reduction kem onoff hDet
    ecEk hEkCorrect hEkPos ecCt0 hCt0Correct hCt0Pos
    ecCt1 hCt1Correct hCt1Pos leak adv q hq

/-- Assume:

* `kem` has deterministic decapsulation and is perfectly correct;
* `onoff` splits encapsulation into an offline and an online part;
* `ecEk`, `ecCt0`, and `ecCt1` are correct erasure codes with positive
  reconstruction thresholds.

Then the Opp-UniKEM-CKA correctness game succeeds with probability one for
every adversary, without a query bound. -/
-- ANCHOR: correctness
theorem correctness [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (hEkCorrect : ecEk.ec.Correct) (hCt0Correct : ecCt0.ec.Correct)
    (hCt1Correct : ecCt1.ec.Correct)
    (hEkPos : 0 < ecEk.ec.nchunk) (hCt0Pos : 0 < ecCt0.ec.nchunk)
    (hCt1Pos : 0 < ecCt1.ec.nchunk)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym)) :
    Pr[= true |
      SCKAScheme.correctnessExp
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv] = 1
-- ANCHOR_END: correctness
    := by
  exact correctness_of_perfectKEM kem onoff hDet ecEk ecCt0 ecCt1 leak hkem
    hEkCorrect hCt0Correct hCt1Correct hEkPos hCt0Pos hCt1Pos adv

end oppUniKemCKA
