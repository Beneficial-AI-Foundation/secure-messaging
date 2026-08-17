/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction

/-!
# Opp-UniKEM-CKA — Perfect Correctness

We prove perfect correctness of Opp-UniKEM — `correctness_of_perfectKEM`:
for a perfectly correct KEM and correct erasure codes with positive reconstruction thresholds,
`Pr[G(Adv) = true] = 1`, where `G(Adv) := SCKAScheme.correctnessExp Π Adv`
and `Π := scheme kem onoff hDet ecEk ecCt0 ecCt1 leak`.

The transcript relation and oracle-preservation proofs are in
`Perfect.Invariant`, `Perfect.SendA`, `Perfect.SendB`, `Perfect.RecvA`, and
`Perfect.RecvB`.  They are shared with the quantitative reduction.

The reduction tracks a failure score `S`.  Perfect KEM correctness implies
`factorCorrectnessError kem onoff = 0`, so its one-step theorem says that no
oracle increases the expected score.  The generic theorem
`expectedPayoff_simulateQ_run_le_of_nonincreasing` composes this fact through
an arbitrary adaptive adversary, without a query bound.  Since the initial
score is zero,

```text
Pr[G(Adv) = false] ≤ E[S final] = 0.
```

Totality of the correctness game then gives `Pr[G(Adv) = true] = 1`.
-/

open OracleSpec OracleComp ENNReal KEMScheme

namespace oppUniKemCKA

variable {K PK SK C Sym : Type}

open SCKAScheme.sckaCorrectnessSpec
open Reduction.Internal

/-- Perfect correctness of Opp-UniKEM-CKA in the full SCKA correctness game.

The adversary may delay, reorder, duplicate, and replay honest protocol
messages.  Perfect KEM correctness, deterministic decapsulation, and the
three erasure-code correctness assumptions suffice to make every game
assertion hold on every supported execution. -/
theorem correctness_of_perfectKEM [DecidableEq Sym] [DecidableEq K]
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
    := by
  let tracked := trackedCorrectnessImpl kem onoff hDet ecEk ecCt0 ecCt1 leak
  let Inv := trackedInv kem onoff hDet ecEk ecCt0 ecCt1
  let score := trackedFailureScore (Sym := Sym) kem onoff
  let s₀ := initialGame (Sym := Sym) kem onoff
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
  have hfalse_le :
      Pr[= false |
        SCKAScheme.correctnessExp
          (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv] ≤ 0 := by
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
      _ ≤ 0 := hscore
  have hfalse :
      Pr[= false |
        SCKAScheme.correctnessExp
          (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) adv] = 0 :=
    le_antisymm hfalse_le bot_le
  rw [probOutput_false_eq_sub, probFailure_eq_zero, tsub_zero] at hfalse
  exact le_antisymm probOutput_le_one ((tsub_eq_zero_iff_le).mp hfalse)

end oppUniKemCKA
