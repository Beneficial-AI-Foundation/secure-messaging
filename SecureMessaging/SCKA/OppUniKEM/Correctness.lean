/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Correctness.Perfect
import SecureMessaging.SCKA.OppUniKEM.Correctness.KEM
import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction

/-!
# Correctness of Opp-UniKEM-CKA

Opp-UniKEM-CKA runs one KEM instance per epoch: party A transmits a fresh public
key and part B answers with a ciphertext, sampled in an offline and an online
part; each payload is sent through erasure-coded chunks.

Fix a KEM `kem` with deterministic decapsulation `hDet`, an on/off
factorization `onoff` of encapsulation, and erasure codes `ecEk`, `ecCt0`,
`ecCt1` for the public key and the two ciphertext components.

Let:

```text
Π    := scheme kem onoff hDet ecEk ecCt0 ecCt1 leak
G(Adv) := SCKAScheme.correctnessExp Π Adv
ε    := kem.correctnessError.
```

In the game `G(Adv)` the adversary adaptively schedules the oracles `SendA`, `SendB`,
`RecvA`, `RecvB`, and `Unif`; a receive oracle may deliver any previously
generated honest message, so the game includes delay, reordering,
duplication, and replay.  `G(Adv)` returns the conjunction of all protocol
correctness assertions.

## Main results

Assume the erasure codes `ecEk`, `ecCt0`, and `ecCt1` are correct.
For every correctness adversary `Adv`, we have:

* `correctness` — if the KEM is perfectly correct, then
  `Pr[G(Adv) = true] = 1`;
* `correctness_failure_le` — more generally, if `Adv` makes at most `q` send queries, then
  `Pr[G(Adv) = false] ≤ q · ε`;
* `correctness_true_ge` — under the same hypotheses,
  `Pr[G(Adv) = true] ≥ 1 - q · ε`.

`SendQueryBound Adv q` states that `Adv` makes at most `q` queries to
`SendA` and `SendB` combined; `Unif`, `RecvA`, and `RecvB` queries are not
counted.

## Proof outline

Each epoch makes at most three randomized choices: party A samples a KEM key
pair, party B samples the offline part of an encapsulation and later its online
part, which also yields the epoch's shared key:

```text
(pk, sk) ← kem.keygen,  (st, ct₀) ← onoff.encapsOff,  (ct₁, k) ← onoff.encapsOn st pk.
```

**Perfect correctness** (`Correctness.Perfect`):

1. We define a transcript `T` that maps each epoch from a game run to the samples it has drawn.

2. We define the predicate `WorldInv T s` stating that the game state `s` is consistent with `T`
  and `s.correct = true`.

3. We show `∃ T, WorldInv T s` holds initially and is preserved by every oracle
   call; the receive oracles are analysed for every recorded message, in
   any order and any multiplicity.

4. We prove that A's decapsulated key always equals B's
   recorded key.  By consistency with `T` both come from an honest key
   pair and encapsulation, so perfect KEM correctness applies.

5. We conclude `Pr[G(Adv) = true] = 1`.

**Quantitative bounds** (`Correctness.KEM`, `Correctness.Reduction`):

1. We define the probability that an epoch ends in a decapsulation failure
   (decapsulating `(ct₀, ct₁)` under `sk` does not return `k`):

   * `φ(pk, sk)` — the key pair is fixed; `(st, ct₀)` is sampled from
     `onoff.encapsOff` and `(ct₁, k)` from `onoff.encapsOn st pk`;
   * `ψ(st, ct₀)` — the offline sample is fixed; `(pk, sk)` is sampled
     from `kem.keygen` and `(ct₁, k)` from `onoff.encapsOn st pk`;
   * `χ(pk, sk, st, ct₀)` — both are fixed; `(ct₁, k)` is sampled from
     `onoff.encapsOn st pk`.

   We prove that all three quantities are `≤ 1`, and that the KEM correctness
   error `ε` is equal to the expectation of `φ(pk, sk)` over `(pk, sk) ← kem.keygen`,
   and also equal to the expectation of `ψ(st, ct₀)` over `(st, ct₀) ← onoff.encapsOff`.

    `ε = Pr[⊥ | kem.keygen]      + Σ' kp,  Pr[= kp | kem.keygen]       · φ(kp)
     ε = Pr[⊥ | onoff.encapsOff] + Σ' off, Pr[= off | onoff.encapsOff] · ψ(off)`

2. We extend the game state with a Boolean `b`, updated after every oracle
   call: it becomes `true`, and stays `true`, once a completed epoch has
   decapsulated inconsistently.  We define

   * `V(s)` — `φ`, `ψ`, or `χ` at the samples the epoch in progress has
     drawn, and `0` if it has drawn none or is complete;
   * `S(s, b) := if b then 1 else V(s)`.

3. We show that a send call increases the expectation of `S` by at most
   `ε`, and that no other call increases it.

4. We show, by induction over the adversary's query tree, that the
   expectation of `S` at the end of the game is at most `q · ε` for at
   most `q` sends.

5. We conclude `Pr[G(Adv) = false] ≤ q · ε`: a final state with
   `correct = false` has `b = true`, and so `S = 1` there.
-/

open OracleSpec OracleComp ENNReal KEMScheme

namespace oppUniKemCKA

variable {K PK SK C Sym : Type}

/-- Perfect correctness of Opp-UniKEM-CKA: given a perfectly correct KEM and
correct erasure codes, the unrestricted SCKA correctness game succeeds with
probability one, `Pr[G(Adv) = true] = 1`. -/
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

/-- Quantitative correctness:
`Pr[G(Adv) = false] ≤ q · kem.correctnessError` for adversaries making at
most `q` send queries.  Both send oracles count toward `q`; receive queries
are not counted. -/
-- ANCHOR: correctnessFailureLeKEM
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
-- ANCHOR_END: correctnessFailureLeKEM
    := by
  exact correctness_failure_le_reduction kem onoff hDet
    ecEk hEkCorrect hEkPos ecCt0 hCt0Correct hCt0Pos
    ecCt1 hCt1Correct hCt1Pos leak adv q hq

/-- `Pr[G(Adv) = true] ≥ 1 - q · kem.correctnessError` for at most `q` send
queries. -/
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

end oppUniKemCKA
