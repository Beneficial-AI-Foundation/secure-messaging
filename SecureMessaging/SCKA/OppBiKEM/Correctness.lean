/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Correctness.Quantitative.Main
import SecureMessaging.SCKA.OppBiKEM.Correctness.PerfectKEM

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
* `correctness_of_perfectKEM'`, `correctness_of_perfectKEM` — a perfectly correct KEM gives
  `Pr[G(Adv) = true] = 1`: the first is the `ε = 0` instance of `correctness_true_ge`, the
  second drops the query bound;
* `sends_never_rejected_of_noFailure` (in `Quantitative.Main`) and
  `sends_never_rejected_of_perfectKEM` (in `PerfectKEM`) — `send` never takes its error exits
  (a missing own public key, a missing decoded peer key) on a reachable state: as long as no KEM
  instance has completed inconsistently, and always for a perfectly correct KEM. The
  correctness game does not observe these exits.

The first four are stated at the end of this file. `SendQueryBound Adv q` states that `Adv`
makes at most `q` queries to `SendA` and `SendB` combined; `Unif`, `RecvA`, and `RecvB`
queries are not counted.

There are two proofs. The quantitative proof, in `Correctness.Quantitative.Main`, shows that
the tracked run sets its failure flag with probability at most `q · ε` (`tracked_bad_le`);
`correctness_failure_le` follows, and `correctness_true_ge` and `correctness_of_perfectKEM'`
follow from it. The perfect-KEM proof, in `Correctness.PerfectKEM`, shows that the main
invariant holds at every reachable state (`simulateQ_gameInv`); `correctness_of_perfectKEM`
follows. Both rest on the main
invariant of `Correctness.MainInvariant`, which every oracle preserves as long as both parties
can decapsulate the ciphertexts they have yet to receive (`MainInvariant.Game`). They differ in
how they ensure this:

* the quantitative proof keeps the invariant only until the first KEM failure and bounds the
  probability of a KEM failure by `q · ε`, using the tracked game of
  `ToVCVio.OracleComp.SimSemantics.StateT.BadFlag` (specialised to SCKA in
  `SCKA.Correctness.Tracked`) and the conditional KEM error of `KEM.CorrectnessError`;
* the perfect-KEM proof uses that no instance of a perfectly correct KEM can fail, so the
  invariant holds at every reachable state and no query bound is needed.
-/

open OracleComp KEMScheme ENNReal

namespace oppBiKemCKA

variable {K PK SK C Sym : Type} [DecidableEq K] [DecidableEq Sym]

/-- Assume:

* `kem` has deterministic decapsulation;
* `ecEk` and `ecCt` are correct erasure codes;
* `adv` makes at most `q` `SendA` and `SendB` queries combined.

Then the Opp-BiKEM-CKA correctness game fails with probability at most
`q · kem.correctnessError`. -/
theorem correctness_failure_le
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct) (leak : kem.RandLeak)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (q : ℕ) (hq : SCKAScheme.SendQueryBound adv q) :
    Pr[= false | SCKAScheme.correctnessExp (scheme kem hDet ecEk ecCt leak) adv] ≤
      (q : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp :=
  SCKAScheme.correctness_failure_le_of_tracked_bad (scheme kem hDet ecEk ecCt leak)
    (kemFailure hDet) (GameInv kem ecEk ecCt) (fun _ hs => hs.1)
    (trackedBiKem_preservesInv kem hDet ecEk ecCt hEk hCt leak) adv _
    (trackedInv_init kem hDet ecEk ecCt) (correctnessExp_eq_map kem hDet ecEk ecCt leak adv) _
    (tracked_bad_le kem hDet ecEk ecCt hEk hCt leak adv q hq)

/-- Assume:

* `kem` has deterministic decapsulation;
* `ecEk` and `ecCt` are correct erasure codes;
* `adv` makes at most `q` `SendA` and `SendB` queries combined.

Then the Opp-BiKEM-CKA correctness game succeeds with probability at least
`1 - q · kem.correctnessError`. -/
-- ANCHOR: correctnessTrueGe
theorem correctness_true_ge
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct) (leak : kem.RandLeak)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (q : ℕ) (hq : SCKAScheme.SendQueryBound adv q) :
    Pr[= true | SCKAScheme.correctnessExp (scheme kem hDet ecEk ecCt leak) adv] ≥
      1 - (q : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp
-- ANCHOR_END: correctnessTrueGe
    := by
  have h := correctness_failure_le kem hDet ecEk ecCt hEk hCt leak adv q hq
  rw [probOutput_false_eq_sub, probFailure_eq_zero, tsub_zero, tsub_le_iff_right] at h
  rw [ge_iff_le, tsub_le_iff_right]
  rwa [add_comm]

/-- Assume:

* `kem` has deterministic decapsulation and is perfectly correct;
* `ecEk` and `ecCt` are correct erasure codes;
* `adv` makes at most `q` `SendA` and `SendB` queries combined.

Then the Opp-BiKEM-CKA correctness game succeeds with probability one. This is the `ε = 0`
instance of `correctness_true_ge`; `correctness_of_perfectKEM` proves the same without a query
bound. -/
theorem correctness_of_perfectKEM'
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct) (leak : kem.RandLeak)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (q : ℕ) (hq : SCKAScheme.SendQueryBound adv q) :
    Pr[= true | SCKAScheme.correctnessExp (scheme kem hDet ecEk ecCt leak) adv] = 1 := by
  have h := correctness_true_ge kem hDet ecEk ecCt hEk hCt leak adv q hq
  rw [(KEMScheme.correctnessError_eq_zero_iff_perfectlyCorrect kem ProbCompRuntime.probComp).mpr
    hkem, mul_zero, tsub_zero] at h
  exact le_antisymm probOutput_le_one h

/-- Assume:

* `kem` has deterministic decapsulation and is perfectly correct;
* `ecEk` and `ecCt` are correct erasure codes.

Then the Opp-BiKEM-CKA correctness game succeeds with probability one for every adversary,
without a query bound. -/
theorem correctness_of_perfectKEM
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (leak : kem.RandLeak)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym)) :
    Pr[= true | SCKAScheme.correctnessExp (scheme kem hDet ecEk ecCt leak) adv] = 1 := by
  have hdec := decapsCorrectOnSupport_of_perfectlyCorrect kem hDet hkem
  have hfalse :
      Pr[= false | SCKAScheme.correctnessExp (scheme kem hDet ecEk ecCt leak) adv] = 0 := by
    rw [correctnessExp_eq_map, ← probEvent_eq_eq_probOutput, probEvent_map]
    rw [probEvent_eq_zero_iff]
    intro z hz hcontra
    have hinv := simulateQ_gameInv kem hDet ecEk ecCt hEk hCt leak hdec adv
      (initialState .A) (initialState .B) (by simp [initA, init, initialState])
      (by simp [initB, init, initialState]) z hz
    have := hinv.1
    simp only [Function.comp] at hcontra
    rw [this] at hcontra
    cases hcontra
  rw [probOutput_false_eq_sub, probFailure_eq_zero, tsub_zero] at hfalse
  exact le_antisymm probOutput_le_one ((tsub_eq_zero_iff_le).mp hfalse)

end oppBiKemCKA
