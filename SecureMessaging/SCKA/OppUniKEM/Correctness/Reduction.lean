/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction.Composition

/-!
# Opp-UniKEM-CKA — Reduction to KEM Correctness

Main results, for `Π := scheme kem onoff hDet ecEk ecCt0 ecCt1 leak`,
`G(Adv) := SCKAScheme.correctnessExp Π Adv`, `ε := kem.correctnessError`,
and
correct erasure codes with positive reconstruction thresholds:

* `correctness_failure_le_reduction` — for at most `q` send queries
  (`SendQueryBound Adv q`), `Pr[G(Adv) = false] ≤ q · ε`;
* `correctness_true_ge_reduction` — equivalently,
  `Pr[G(Adv) = true] ≥ 1 - q · ε`;
* `correctness_failure_le_of_sendBFailureBound` — the analogous bound from
  stepwise premises (`SendBFailureBound`, `NonSendBPreservesCurrent`,
  `SendBQueryBound`).

Abbreviate `join := onoff.split⁻¹` and
`Run o s := ((SCKAScheme.sckaCorrectnessImpl Π) o).run s`.  In the proof,
`ε` is computed as `factorCorrectnessError kem onoff hDet`, which equals
`kem.correctnessError` (`factorCorrectnessError_eq`).

## Tracked game

* `bad s` (`currentKEMFailure`) — `true` iff `s.stA.t = s.stB.t` and the
  current epoch has completed inconsistently:
  `s.stA.dkA = some sk`, `s.stB.ct0 = some ct₀`, `s.stB.ct1 = some ct₁`,
  `s.keyB s.stB.t = some k`, and
  `hDet.decapsDet sk (join (ct₀, ct₁)) ≠ some k`.
* `Ô` (`trackedCorrectnessImpl`) — the game extended with a Boolean that
  stays `true` once set:
  `Ô o (s, b) := do (r, s') ← Run o s; return (r, (s', b ∨ bad s'))`.
* `J` (`trackedInv`) —
  `J (s, b) := b = true ∨ (reachableInv s ∧ bad s = false)`.

## Failure probabilities

With the conditional errors `χ`, `φ`, `ψ` of `Correctness.KEM`, associate to
a tracked state the probability that it has already failed, or that its
epoch in progress completes inconsistently:

```text
V s := 0                     no sample drawn, or epoch completed
       φ (pk, sk)            only the key pair (stA.ekA, stA.dkA) drawn
       ψ (st, ct₀)           only the offline sample (stB.stCt, stB.ct0) drawn
       χ (pk, sk, st, ct₀)   both drawn

S (s, b) := if b then 1 else V s
E_X[f]   := Pr[X = ⊥] + Σ x, Pr[X = x] · f x
```

(`currentFailurePotential`, `trackedFailureScore`, `expectedPayoff`).  The
epoch in progress reads A's key pair, and B's offline sample when
`s.stA.t = s.stB.t`; when `s.stA.t = s.stB.t + 1`, B's material belongs to
the completed previous epoch and is ignored.

## One step

For every oracle `o` and every `(s, b)` with `J (s, b)`:

```text
(r, (s', b')) ∈ supp (Ô o (s, b)) → J (s', b')
E_{Ô o (s, b)}[S] ≤ S (s, b) + ε      if o ∈ {SendA, SendB}
E_{Ô o (s, b)}[S] ≤ S (s, b)          otherwise.
```

Drawing the epoch's first sample turns `V = 0` into expectation at most `ε`
(the averaging identities of `Correctness.KEM`); drawing the other
first-stage sample has expectation exactly `V`; drawing the online sample
completes the epoch, setting `b' = bad s'` with expectation `χ = V` and
`V s' = 0`.  Receive oracles move no KEM material; their cases are proved
for every message index.

## Composition

1. `tracked_score_adversary_le` — induction over the adversary's query
   tree: `J (s, b)` and at most `q` sends give
   `E[S final] ≤ S (s, b) + q · ε`; initially `S (s₀, false) = 0`.
2. `tracked_run_project` — dropping the Boolean projects the tracked run
   onto the real game; by `J`, `correct = false` forces `b = true`, i.e.
   `S = 1`.  Hence `Pr[G(Adv) = false] ≤ q · ε`, and
   `Pr[G(Adv) = true] ≥ 1 - q · ε` follows since `G(Adv)` is total.

## Stepwise interface

`correctness_failure_le_of_sendBFailureBound` replaces the conditional
errors by two premises:
`SendBFailureBound δ` — from a state with consistent current KEM material,
one `SendB` call sets `bad` with probability at most `δ` — and
`NonSendBPreservesCurrent` — no other oracle can set `bad`.  It bounds
`Pr[G(Adv) = false] ≤ q · δ` for at most `q` `SendB` queries
(`SendBQueryBound Adv q`).
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
  let score := trackedFailureScore (Sym := Sym) kem onoff hDet
  let s₀ := initialGame (Sym := Sym) kem onoff
  let epsilon := factorCorrectnessError kem onoff hDet
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
    have h := tracked_score_adversary_le kem onoff hDet ecEk ecCt0 ecCt1 leak
      adv q hq epsilon hpres
      (tracked_score_step_le kem onoff hDet ecEk ecCt0 ecCt1 leak)
      (s₀, false) hinit
    have hscore₀' : trackedFailureScore kem onoff hDet (s₀, false) = 0 := by
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
    · rcases hreach with ⟨_world, hWorld⟩
      simp [hWorld.correct] at hincorrect
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
      tracked_bad_probability_le_score kem onoff hDet _
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
