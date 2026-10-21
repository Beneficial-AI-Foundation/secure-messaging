/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Defs
import ToVCVio.OracleComp.SimSemantics.StateT.BadFlag

/-!
# The tracked game for SCKA correctness

To bound the failure probability of an SCKA correctness experiment by a primitive's error, the
game is run with an extra Boolean flag that is set as soon as the state becomes *bad* and never
cleared. The construction itself is generic and lives in
`ToVCVio.OracleComp.SimSemantics.StateT.BadFlag` (`trackedImpl`, `trackedInv`). This file
specialises it to the SCKA correctness game, with `SendQueryBound` from `SCKA.Defs` counting
send queries:

* `tracked_bad_le_of_score_step` turns per-query expected-score bounds (an allowance of `ε` per
  send query, none otherwise) into `Pr[flag] ≤ q · ε`;
* `correctness_failure_le_of_tracked_bad` turns a bound on the flag into a bound on
  `Pr[correctnessExp = false]`, given that the invariant forces the game's `correct` bit.

The scheme-specific inputs are the bad predicate, the invariant, the score, and the per-query
bounds.

This complements the potential method of `SCKA.Correctness` (`correctness_error_le_of_potential`),
which needs an invariant preserved by every query of the ordinary game. With the flag, the
invariant only has to hold until the first bad state, so nothing has to be proved about the
states that follow a primitive failure.
-/

open OracleSpec ENNReal

namespace SCKAScheme

open OracleComp sckaCorrectnessSpec

variable {IK StA StB I Rho Rand : Type}

/-- Let `adv` be a correctness adversary making at most `q` queries to
`SendA` and `SendB` combined. Assume:

* `trackedInv Inv bad` holds at `(s₀, false)` and is preserved by every query;
* `score (s₀, false) = 0`;
* `score (s, true) ≥ 1` for every game state `s`;
* from every invariant tracked state, sends increase the expected score
  by at most `ε`, and other queries do not increase it.

Then the probability that `bad` holds after at least one query during
`adv`'s execution is at most `q · ε`. -/
theorem tracked_bad_le_of_score_step [DecidableEq I]
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (bad : GameState StA StB I Rho → Bool) (Inv : GameState StA StB I Rho → Prop)
    (score : GameState StA StB I Rho × Bool → ℝ≥0∞) (ε : ℝ≥0∞)
    (hscore1 : ∀ p, p.2 = true → 1 ≤ score p)
    (hpres : QueryImpl.PreservesInv (trackedImpl (sckaCorrectnessImpl scka) bad)
      (trackedInv Inv bad))
    (hstep : ∀ t p, trackedInv Inv bad p →
      expectedPayoff (((trackedImpl (sckaCorrectnessImpl scka) bad) t).run p)
          (fun z => score z.2) ≤
        score p + if isSendQuery (Rho := Rho) t then ε else 0)
    (adv : SCKACorrectnessAdversary Rho) (q : ℕ) (hq : SendQueryBound adv q)
    (s₀ : GameState StA StB I Rho) (hinit : trackedInv Inv bad (s₀, false))
    (hscore₀ : score (s₀, false) = 0) :
    Pr{let z ← (simulateQ (trackedImpl (sckaCorrectnessImpl scka) bad) adv).run (s₀, false)}[z.2.2 = true] ≤
      (q : ℝ≥0∞) * ε :=
  (OracleComp.tracked_bad_le_of_score_step (sckaCorrectnessImpl scka) bad Inv score
    (fun t => isSendQuery (Rho := Rho) t = true) ε hscore1 hpres hstep adv q hq s₀
    hinit).trans_eq (by rw [hscore₀, zero_add])

/-- Let `adv` be a correctness adversary and `s₀` a game state. Assume:

* `trackedInv Inv bad` holds at `(s₀, false)` and is preserved by every query;
* `Inv s` implies `s.correct = true` for every game state `s`;
* `correctnessExp scka adv` is the final `correct` bit of `adv`'s execution from `s₀`;
* the probability that `bad` holds after at least one query during `adv`'s execution from
  `s₀` is at most `δ`.

Then `Pr[correctnessExp scka adv = false] ≤ δ`. -/
theorem correctness_failure_le_of_tracked_bad [DecidableEq I]
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (bad : GameState StA StB I Rho → Bool) (Inv : GameState StA StB I Rho → Prop)
    (hcorrect : ∀ s, Inv s → s.correct = true)
    (hpres : QueryImpl.PreservesInv (trackedImpl (sckaCorrectnessImpl scka) bad)
      (trackedInv Inv bad))
    (adv : SCKACorrectnessAdversary Rho) (s₀ : GameState StA StB I Rho)
    (hinit : trackedInv Inv bad (s₀, false))
    (hexp : correctnessExp scka adv =
      (fun z => z.2.correct) <$> (simulateQ (sckaCorrectnessImpl scka) adv).run s₀)
    (δ : ℝ≥0∞)
    (hbad : Pr{let z ← (simulateQ (trackedImpl (sckaCorrectnessImpl scka) bad) adv).run (s₀, false)}[z.2.2 = true] ≤ δ) :
    Pr{let x ← correctnessExp scka adv}[x = false] ≤ δ := by
  rw [hexp, ← probEvent_eq_eq_probOutput, prEvent_map]
  exact (probEvent_not_good_le_tracked_bad (sckaCorrectnessImpl scka) bad Inv
    (fun s => s.correct) hcorrect hpres adv s₀ hinit).trans hbad

end SCKAScheme
