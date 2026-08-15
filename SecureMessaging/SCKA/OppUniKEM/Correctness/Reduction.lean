/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction.Composition

/-!
# Opp-UniKEM-CKA — Reduction to KEM Correctness

Let:

* `Π := scheme kem onoff hDet ecEk ecCt0 ecCt1 leak` — the Opp-UniKEM-CKA
  protocol as an `SCKAScheme` (`OppUniKEM.Construction`), given correct
  erasure codes with positive reconstruction thresholds;
* `G(Adv) := SCKAScheme.correctnessExp Π Adv` - the outcome of the correctness experiment
  for an adversary `Adv`;
* `ε := kem.correctnessError`;
* `E_X[f] := Pr[X = ⊥] + Σ x, Pr[X = x] · f x` — the expected payoff of
  `f` under `X` (`expectedPayoff`).  Here every payoff `f x` is a failure
  probability, so `E_X[f]` is the probability that `X` fails directly
  (charged `1`) or returns an `x` that fails later (probability `f x`).

## Main results

If the adversary `Adv` makes at most `q` send queries (`SendQueryBound Adv q`), then

* `correctness_failure_le_reduction`: `Pr[G(Adv) = false] ≤ q · ε`;
* `correctness_true_ge_reduction`: `Pr[G(Adv) = true] ≥ 1 - q · ε`.

The proof is split in modules as follows.

## Tracked game and tracked states invariant (`Reduction.Core`, `Reduction.Projection`)

We define a *tracked game* whose states are pairs `(s, b)`, where:
- `s` is a correctness-game state, and
- `b` is a Boolean flag recording whether a KEM failure has occurred so far.

We also define:

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

* `Ô := trackedCorrectnessImpl` — the tracked game's oracle
  implementation. It answers any query as in the original game and updates
  the failure flag `b` according to the bad predicate of the next state:

  ```text
  Run o s := ((SCKAScheme.sckaCorrectnessImpl Π) o).run s

  Ô o (s, b) := do
    (r, s') ← Run o s
    return (r, (s', b ∨ bad s'))
  ```

* `J := trackedInv` — the invariant of tracked states: either the flag
  `b` is set, or `s` is reachable and no bad event happens:

  ```text
  J (s, b) := b = true ∨ (reachableInv s ∧ bad s = false)
  ```

## Failure probabilities (`Reduction.Core`)

The conditional errors from `KEM.OnOffKEM.CorrectnessError` describe the
probability of failure over the samples that remain to be drawn:

* `φ(pk, sk)` — after fixing the key pair, average over the offline and
  online samples;
* `ψ(st, ct₀)` — after fixing the offline sample, average over the key pair
  and online sample;
* `χ(pk, sk, st, ct₀)` — after fixing both first-stage samples, average over
  the online sample.

Each error also counts a computation that produces no output as failure.

We define:

* `V s` — the probability that the epoch in progress of the game state `s`
  completes inconsistently;

```text
V s := 0                     no sample drawn, or epoch completed
       φ (pk, sk)            only the key pair (stA.ekA, stA.dkA) drawn
       ψ (st, ct₀)           only the offline sample (stB.stCt, stB.ct0) drawn
       χ (pk, sk, st, ct₀)   both drawn

```

* `S (s, b)` — the failure-risk payoff tracked by the proof:
  an already-recorded failure (`b = true`) has risk payoff `1`;
  otherwise the payoff is the conditional failure probability `V s` of the epoch in progress.

```text
S (s, b) := if b then 1 else V s
```

## One step (`Reduction.Send`, `Reduction.Receive`, `Reduction.OneStep`)

We prove that each oracle query:
- preserves the tracked states invariant J(s, b), and
- increases the expected payoff of `S` by at most `ε`.

More precisely, for every oracle `o` and every tracked state `(s, b)` satisfying `J (s, b)`,
we have:

```text
(r, (s', b')) ∈ supp (Ô o (s, b)) → J (s', b').             -- the invariant is preserved
E_{Ô o (s, b)}[S] ≤ S (s, b) + ε      if o ∈ {SendA, SendB} -- bound the expected payoff increase
E_{Ô o (s, b)}[S] ≤ S (s, b)          otherwise.            -- expected risk payoff is same.
```

## Composition (`Reduction.Composition`, this module)

Starting from `S (s₀, false) = 0`, `expectedPayoff_simulateQ_run_le` composes
the one-step bound over at most `q` send queries.  The invariant `J` makes game
failure imply score `1`, and `tracked_run_project` transfers the bound to the
original game:

```text
Pr[G(Adv) = false] ≤ E[S final] ≤ q · ε
```

The success bound follows because `G(Adv)` is total.
-/

open OracleSpec OracleComp ENNReal KEMScheme

namespace oppUniKemCKA

universe u

variable {K PK SK C Sym : Type}

open SCKAScheme.sckaCorrectnessSpec
open oppUniKemCKA.Reduction.Internal

section Reduction

variable [DecidableEq Sym]

/-- Reduction of Opp-UniKEM-CKA correctness to KEM correctness: an adversary
making at most `q` send queries makes the correctness experiment fail with
probability at most `q * kem.correctnessError`.  Both send oracles count
toward `q`, since either party may draw the first sample of a fresh epoch;
receive queries are not counted. -/
theorem correctness_failure_le_reduction [DecidableEq K]
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
  let tracked := trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak
  let Inv := trackedInv kem onoff hDet ecEk ecCt0 ecCt1
  let score := trackedFailureScore (Sym := Sym) kem onoff
  let s₀ := initialGame (Sym := Sym) kem onoff
  let epsilon := factorCorrectnessError kem onoff
  have hpres : QueryImpl.PreservesInv tracked Inv :=
    trackedCorrectnessImpl_preserves kem onoff hDet ecEk hEkCorrect hEkPos
      ecCt0 hCt0Correct hCt0Pos ecCt1 hCt1Correct hCt1Pos leak
  have hinit : Inv (s₀, false) := by
    right
    refine ⟨?_, ?_⟩
    · simpa [s₀, initialGame, initialA, initialB] using
        reachableInv_init kem onoff ecEk ecCt0 ecCt1 hEkPos hCt0Pos
    · simp [currentKEMFailure, s₀, initialGame, initialA, initialB,
        SCKAScheme.initGameState]
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
  have hmono :
      Pr[fun z => z.2.1.correct = false |
          (simulateQ tracked adv).run (s₀, false)] ≤
        Pr[fun z => z.2.2 = true |
          (simulateQ tracked adv).run (s₀, false)] := by
    refine probEvent_mono ?_
    intro z hz hincorrect
    have hzInv : Inv z.2 :=
      OracleComp.simulateQ_run_preservesInv tracked Inv hpres adv
        (s₀, false) hinit z hz
    rcases hzInv with hbad | ⟨hreach, _hcurrent⟩
    · exact hbad
    · rcases hreach with ⟨_T, hConsistent⟩
      simp [hConsistent.correct] at hincorrect
  calc
    Pr[= false |
        SCKAScheme.correctnessExp
          (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv] =
        Pr[fun z => z.2.1.correct = false |
          (simulateQ tracked adv).run (s₀, false)] := by
      rw [correctnessExp_eq_final_map]
      rw [← probEvent_eq_eq_probOutput, probEvent_map]
      have hproject := tracked_run_project kem onoff hDet ecEk ecCt0 ecCt1
        leak adv (s₀, false)
      rw [← hproject, probEvent_map]
      congr 1
    _ ≤ Pr[fun z => z.2.2 = true |
          (simulateQ tracked adv).run (s₀, false)] := hmono
    _ ≤ expectedPayoff ((simulateQ tracked adv).run (s₀, false))
          (fun z => score z.2) :=
      tracked_bad_probability_le_score kem onoff _
    _ ≤ (q : ℝ≥0∞) * epsilon := hscore
    _ = (q : ℝ≥0∞) * kem.correctnessError ProbCompRuntime.probComp := by
      simp only [epsilon, factorCorrectnessError_eq]

/-- `Pr[G(Adv) = true] ≥ 1 - q * kem.correctnessError` for at most `q` send
queries. -/
theorem correctness_true_ge_reduction [DecidableEq K]
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
    := by
  have h := correctness_failure_le_reduction kem onoff hDet
    ecEk hEkCorrect hEkPos ecCt0 hCt0Correct hCt0Pos
    ecCt1 hCt1Correct hCt1Pos leak adv q hq
  rw [probOutput_false_eq_sub, probFailure_eq_zero, tsub_zero] at h
  rw [tsub_le_iff_right] at h
  rw [ge_iff_le, tsub_le_iff_right]
  rwa [add_comm]

end Reduction

end oppUniKemCKA
