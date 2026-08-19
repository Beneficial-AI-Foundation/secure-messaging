/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction.Composition

/-!
# Opp-UniKEM-CKA — Reduction to KEM Correctness

Let:

* `Π := scheme kem onoff hDet ecEk ecCt0 ecCt1 leak` be the Opp-UniKEM-CKA SCKA scheme;
* `G(Adv) := SCKAScheme.correctnessExp Π Adv` be the outcome of its correctness experiment
  for an adversary `Adv`;
* `ε := kem.correctnessError` be the underlying KEM's correctness error;
* `E_X[f] := Pr[X = ⊥] + Σ x, Pr[X = x] · f x` be the expected payoff of
  `f` under a computation `X` (`expectedPayoff`).

  In our context, the payoff `f x` is a failure probability,
  so `E_X[f]` is the probability that `X` fails directly
  (charged `1`) or returns an `x` that fails later (probability `f x`).

## Main results

If the adversary `Adv` makes at most `q` send queries (`SendQueryBound Adv q`), then

* `correctness_failure_le_reduction`: `Pr[G(Adv) = false] ≤ q · ε`;
* `correctness_true_ge_reduction`: `Pr[G(Adv) = true] ≥ 1 - q · ε`.

The proof has four parts.

## Tracked game and tracked states invariant (`Reduction.Core`, `Reduction.Projection`)

The tracked execution augments each ordinary game state with a failure flag.
Its states are pairs `(s, b)`, where:
- `s` is a correctness-game state, and
- `b` is a Boolean flag recording whether a KEM failure has occurred so far.

The tracked execution uses:

* `bad s := currentKEMFailure kem onoff hDet s` — a Boolean predicate on
  correctness-game states. It is `true` iff both protocol parties are in the
  same epoch and the completed KEM material is inconsistent:

  ```text
  join := onoff.split.symm     (a KEM ciphertext from its two components)

  s.stA.dkA          = some sk
  s.stB.ct0          = some ct₀
  s.stB.ct1          = some ct₁
  s.keyB s.stB.t     = some k
  decaps sk (join (ct₀, ct₁)) ≠ some k
  ```

* `Ô := trackedCorrectnessImpl` — the tracked query handler (`QueryImpl`):
  given an oracle query and a tracked state, it runs the corresponding
  ordinary-game query and updates the failure flag `b` according to the bad
  predicate of the resulting state:

  ```text
  Run o s := ((SCKAScheme.sckaCorrectnessImpl Π) o).run s

  Ô o (s, b) := do
    (r, s') ← Run o s
    return (r, (s', b ∨ bad s'))
  ```

* `J := trackedInv` — the invariant of tracked states: either the flag
  `b` is set, or `s` is reachable and its current KEM material is consistent:

  ```text
  J (s, b) := b = true ∨ (reachableInv s ∧ bad s = false)
  ```

## Failure probabilities (`Reduction.Core`)

The conditional errors from `KEM.OnOffKEM.CorrectnessError` describe the
probability of failure over the samples that remain to be drawn in an
OnOffKEM experiment:

* `φ(pk, sk)` — the correctness error after fixing the key pair, averaged
  over the remaining offline and online samples;
* `ψ(st, ct₀)` — the correctness error after fixing the offline sample,
  averaged over the remaining key-pair and online samples;
* `χ(pk, sk, st, ct₀)` — the correctness error after fixing both first-stage
  samples, averaged over the remaining online sample.

For an ordinary game state `s` and a failure flag `b`, we define:

* `V(s) := currentFailurePotential kem onoff s`, the conditional probability
  that the epoch in progress completes inconsistently:

```text
V s := 0                     when no sample drawn, or epoch completed
       φ (pk, sk)            when only the key pair (stA.ekA, stA.dkA) drawn
       ψ (st, ct₀)           when only the offline sample (stB.stCt, stB.ct0) drawn
       χ (pk, sk, st, ct₀)   when both drawn

```

* `S(s, b) := trackedFailureScore kem onoff (s, b)`, equal to `1` when
  `b = true` and to `V(s)` otherwise.

```text
S (s, b) := if b then 1 else V s
```

## One step (`Reduction.Send`, `Reduction.Receive`, `Reduction.OneStep`)

We prove that each oracle query:
- preserves the tracked states invariant J(s, b), and
- increases the expected tracked failure score by at most `ε`.

More precisely, for every oracle `o` and every tracked state `(s, b)` satisfying `J (s, b)`,
we have:

```text
(r, (s', b')) ∈ supp (Ô o (s, b)) → J (s', b').             -- the invariant is preserved
E_{Ô o (s, b)}[S] ≤ S (s, b) + ε      if o ∈ {SendA, SendB} -- expected payoff increase is bounded
E_{Ô o (s, b)}[S] ≤ S (s, b)          otherwise.            -- expected score does not increase
```

## Composition
In `Reduction.Composition`, we aggregate the one-query facts over an adaptive
adversary, whose later queries may depend on earlier responses, by induction
over its oracle-computation tree.
-/

open OracleSpec OracleComp ENNReal KEMScheme

namespace oppUniKemCKA

universe u

variable {K PK SK C Sym : Type}

open SCKAScheme.sckaCorrectnessSpec
open oppUniKemCKA.Reduction.Internal

section Reduction

variable [DecidableEq Sym]

/-- Assume:

* `kem` has deterministic decapsulation and is perfectly correct;
* `onoff` splits encapsulation into an offline and an online part;
* `ecEk`, `ecCt0`, and `ecCt1` are correct erasure codes.

Then the Opp-UniKEM-CKA correctness game succeeds with probability one. -/
theorem correctness_of_perfectKEM [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (hkem : kem.PerfectlyCorrect ProbCompRuntime.probComp)
    (hEkCorrect : ecEk.ec.Correct) (hCt0Correct : ecCt0.ec.Correct)
    (hCt1Correct : ecCt1.ec.Correct)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym)) :
    Pr[= true |
      SCKAScheme.correctnessExp
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv] = 1
    := by
  have hEkPos := ecEk.ec.nchunk_pos
  have hCt0Pos := ecCt0.ec.nchunk_pos
  have hCt1Pos := ecCt1.ec.nchunk_pos
  let tracked := trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak
  let Inv := trackedInv kem onoff hDet ecEk ecCt0 ecCt1
  let score := trackedFailureScore (Sym := Sym) kem onoff
  let s₀ := initialGame (Sym := Sym) kem onoff
  have hpres : QueryImpl.PreservesInv tracked Inv :=
    trackedCorrectnessImpl_preserves kem onoff hDet ecEk hEkCorrect hEkPos
      ecCt0 hCt0Correct hCt0Pos ecCt1 hCt1Correct hCt1Pos leak
  have hinit : Inv (s₀, false) := by
    simpa [Inv, s₀] using
      tracked_initial_inv kem onoff hDet ecEk ecCt0 ecCt1 hEkPos hCt0Pos
  have hscore₀ : score (s₀, false) = 0 := by
    simp [score, trackedFailureScore, currentFailurePotential, s₀, initialGame,
      initialA, initialB, SCKAScheme.initGameState, optionPair]
  have hepsilon : factorCorrectnessError kem onoff = 0 := by
    rw [factorCorrectnessError_eq]
    exact (KEMScheme.correctnessError_eq_zero_iff_perfectlyCorrect
      kem ProbCompRuntime.probComp).2 hkem
  have hstep : ∀ t p, Inv p →
      expectedPayoff ((tracked t).run p) (fun z => score z.2) ≤ score p := by
    intro t p hp
    have h := tracked_score_step_le kem onoff hDet ecEk ecCt0 ecCt1 leak t p hp
    simpa [tracked, Inv, score, hepsilon] using h
  have hscore :
      expectedPayoff ((simulateQ tracked adv).run (s₀, false))
          (fun z => score z.2) ≤ 0 := by
    have h := expectedPayoff_simulateQ_run_le_of_nonincreasing
      tracked Inv score hpres hstep adv (s₀, false) hinit
    rw [hscore₀] at h
    exact h
  have hbad :
      Pr[ fun z => z.2.2 = true |
          (simulateQ
            (trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak) adv).run
              (initialGame (Sym := Sym) kem onoff, false)] ≤ 0 := by
    calc
      Pr[ fun z => z.2.2 = true |
          (simulateQ tracked adv).run (s₀, false)] ≤
          expectedPayoff ((simulateQ tracked adv).run (s₀, false))
            (fun z => score z.2) :=
        tracked_bad_probability_le_score kem onoff _
      _ ≤ 0 := hscore
  have hfalse_le :
      Pr[= false |
        SCKAScheme.correctnessExp
          (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv] ≤ 0 :=
    correctness_failure_le_of_tracked_bad kem onoff hDet
      ecEk hEkCorrect hEkPos ecCt0 hCt0Correct hCt0Pos
      ecCt1 hCt1Correct hCt1Pos leak adv 0 hbad
  have hfalse :
      Pr[= false |
        SCKAScheme.correctnessExp
          (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv] = 0 :=
    le_antisymm hfalse_le bot_le
  rw [probOutput_false_eq_sub, probFailure_eq_zero, tsub_zero] at hfalse
  exact le_antisymm probOutput_le_one ((tsub_eq_zero_iff_le).mp hfalse)

/-- Assume:

* `kem` has deterministic decapsulation;
* `onoff` splits encapsulation into an offline and an online part;
* `ecEk`, `ecCt0`, and `ecCt1` are correct erasure codes;
* `adv` makes at most `q` `SendA` and `SendB` queries combined.

Then the Opp-UniKEM-CKA correctness game fails with probability at most
`q · kem.correctnessError`. -/
theorem correctness_failure_le_reduction [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEkCorrect : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0Correct : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1Correct : ecCt1.ec.Correct)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (q : ℕ) (hq : SendQueryBound adv q) :
    Pr[= false |
      SCKAScheme.correctnessExp
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv] ≤
      (q : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp
    := by
  have hEkPos := ecEk.ec.nchunk_pos
  have hCt0Pos := ecCt0.ec.nchunk_pos
  have hCt1Pos := ecCt1.ec.nchunk_pos
  let tracked := trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak
  let Inv := trackedInv kem onoff hDet ecEk ecCt0 ecCt1
  let score := trackedFailureScore (Sym := Sym) kem onoff
  let s₀ := initialGame (Sym := Sym) kem onoff
  let epsilon := factorCorrectnessError kem onoff
  have hpres : QueryImpl.PreservesInv tracked Inv :=
    trackedCorrectnessImpl_preserves kem onoff hDet ecEk hEkCorrect hEkPos
      ecCt0 hCt0Correct hCt0Pos ecCt1 hCt1Correct hCt1Pos leak
  have hinit : Inv (s₀, false) := by
    simpa [Inv, s₀] using
      tracked_initial_inv kem onoff hDet ecEk ecCt0 ecCt1 hEkPos hCt0Pos
  have hscore₀ : score (s₀, false) = 0 := by
    simp [score, trackedFailureScore, currentFailurePotential, s₀, initialGame,
      initialA, initialB, SCKAScheme.initGameState, optionPair]
  have hscore :
      expectedPayoff ((simulateQ tracked adv).run (s₀, false))
          (fun z => score z.2) ≤
        (q : ℝ≥0∞) * epsilon := by
    have h := expectedPayoff_simulateQ_run_le
      (trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak)
      (trackedInv kem onoff hDet ecEk ecCt0 ecCt1)
      (trackedFailureScore kem onoff)
      (IsSendQuery (Sym := Sym)) epsilon hpres
      (tracked_score_step_le kem onoff hDet ecEk ecCt0 ecCt1 leak)
      adv q hq (s₀, false) hinit
    have hscore₀' : trackedFailureScore kem onoff (s₀, false) = 0 := by
      simpa [score] using hscore₀
    rw [hscore₀', zero_add] at h
    simpa [tracked, score] using h
  have hbad :
      Pr[ fun z => z.2.2 = true |
          (simulateQ
            (trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak) adv).run
              (initialGame (Sym := Sym) kem onoff, false)] ≤
        (q : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp := by
    calc
      Pr[ fun z => z.2.2 = true |
          (simulateQ tracked adv).run (s₀, false)] ≤
          expectedPayoff ((simulateQ tracked adv).run (s₀, false))
            (fun z => score z.2) :=
        tracked_bad_probability_le_score kem onoff _
      _ ≤ (q : ℝ≥0∞) * epsilon := hscore
      _ = (q : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp := by
        simp only [epsilon, factorCorrectnessError_eq]
  exact correctness_failure_le_of_tracked_bad kem onoff hDet
    ecEk hEkCorrect hEkPos ecCt0 hCt0Correct hCt0Pos
    ecCt1 hCt1Correct hCt1Pos leak adv
    ((q : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp) hbad

/-- Corollary: `Pr[G(Adv) = true] ≥ 1 - q * kem.correctnessError` for at most `q` send
queries. -/
theorem correctness_true_ge_reduction [DecidableEq K]
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEkCorrect : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0Correct : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1Correct : ecCt1.ec.Correct)
    (leak : KEMScheme.OnOffRandLeak kem onoff)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (q : ℕ) (hq : SendQueryBound adv q) :
    Pr[= true |
      SCKAScheme.correctnessExp
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv] ≥
      1 - (q : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp
    := by
  have h := correctness_failure_le_reduction kem onoff hDet
    ecEk hEkCorrect ecCt0 hCt0Correct ecCt1 hCt1Correct leak adv q hq
  rw [probOutput_false_eq_sub, probFailure_eq_zero, tsub_zero] at h
  rw [tsub_le_iff_right] at h
  rw [ge_iff_le, tsub_le_iff_right]
  rwa [add_comm]

end Reduction

end oppUniKemCKA
