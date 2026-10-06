/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Gavran, Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Defs
import ToVCVio.OracleComp.ExpectedPayoff
import ToVCVio.OracleComp.SimSemantics.StateT.ExpectedPayoffBound
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# The tracked game, generically

To bound the failure probability of an SCKA correctness experiment by a primitive's error, the
game is run with an extra Boolean flag that is set as soon as the state becomes *bad* and
never cleared. This file provides that construction for any stateful oracle implementation:

* `trackedImpl impl bad` runs `impl` and updates the flag;
* `trackedInv Inv bad` is the tracked invariant: the flag is set, or `Inv` holds and the state
  is not bad;
* `tracked_run_project`: forgetting the flag recovers the ordinary run;
* `trackedImpl_preserves`: one-step preservation of `Inv` under "not bad" lifts to the tracked
  game;
* `tracked_bad_probability_le_score`: the probability that the flag ends up set is at most the
  expected value of any score that is at least `1` on flagged states.

For the SCKA correctness game specifically, `SendQueryBound` counts send queries and
`tracked_bad_le_of_score_step` turns per-query expected-score bounds (an allowance of `ε` per
send query, none otherwise) into `Pr[flag] ≤ q · ε`, and `correctness_failure_le_of_tracked_bad`
turns a bound on the flag into a bound on `Pr[correctnessExp = false]`, given that the invariant
forces the game's `correct` bit. The scheme-specific inputs are the bad predicate, the invariant,
the score, and the per-query bounds.
-/

open OracleSpec ENNReal

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {σ : Type}

/-- Run an oracle and set the flag if the resulting state is bad. The flag is never cleared. -/
def trackedImpl (impl : QueryImpl spec (StateT σ ProbComp)) (bad : σ → Bool) :
    QueryImpl spec (StateT (σ × Bool) ProbComp) :=
  fun t p => do
    let z ← (impl t).run p.1
    pure (z.1, (z.2, p.2 || bad z.2))

/-- The tracked invariant: the flag is set, or the invariant holds and the state is not bad. -/
def trackedInv (Inv : σ → Prop) (bad : σ → Bool) (p : σ × Bool) : Prop :=
  p.2 = true ∨ (Inv p.1 ∧ bad p.1 = false)

/-- Forgetting the flag after one tracked query gives the ordinary query. -/
theorem trackedImpl_project (impl : QueryImpl spec (StateT σ ProbComp)) (bad : σ → Bool)
    (t : ι) (p : σ × Bool) :
    Prod.map id Prod.fst <$> ((trackedImpl impl bad) t).run p = (impl t).run p.1 := by
  unfold trackedImpl
  change Prod.map id Prod.fst <$> (do
      let z ← (impl t).run p.1
      pure (z.1, (z.2, p.2 || bad z.2))) = _
  rw [map_eq_bind_pure_comp, bind_assoc]
  simp

/-- Forgetting the flag after a whole tracked run gives the ordinary run. -/
theorem tracked_run_project (impl : QueryImpl spec (StateT σ ProbComp)) (bad : σ → Bool)
    {α : Type} (oa : OracleComp spec α) (p : σ × Bool) :
    Prod.map id Prod.fst <$> (simulateQ (trackedImpl impl bad) oa).run p =
      (simulateQ impl oa).run p.1 :=
  map_run_simulateQ_eq_of_query_map_eq (trackedImpl impl bad) impl Prod.fst
    (trackedImpl_project impl bad) oa p

/-- One-step preservation of `Inv` from states that are not bad lifts to the tracked
invariant. -/
theorem trackedImpl_preserves (impl : QueryImpl spec (StateT σ ProbComp)) (bad : σ → Bool)
    (Inv : σ → Prop)
    (hstep : ∀ t s, Inv s → bad s = false → ∀ z ∈ support ((impl t).run s), Inv z.2) :
    QueryImpl.PreservesInv (trackedImpl impl bad) (trackedInv Inv bad) := by
  intro t p hp z hz
  unfold trackedImpl at hz
  change z ∈ support (do
    let y ← (impl t).run p.1
    pure (y.1, (y.2, p.2 || bad y.2))) at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  simp only [mem_support_pure_iff] at hz
  subst z
  rcases hp with hflag | ⟨hinv, hgood⟩
  · left
    simp [hflag]
  by_cases hbad : bad y.2 = true
  · left
    simp [hbad]
  · right
    exact ⟨hstep t p.1 hinv hgood y hy, by simpa using hbad⟩

/-- The probability that the flag is set is at most the expected score, for any score that is
at least `1` on flagged states. Computation failure is charged `1` by `expectedPayoff`. -/
theorem tracked_bad_probability_le_score {α : Type} (score : σ × Bool → ℝ≥0∞)
    (hscore : ∀ p : σ × Bool, p.2 = true → 1 ≤ score p) (oa : ProbComp (α × (σ × Bool))) :
    Pr[ fun z => z.2.2 = true | oa] ≤ expectedPayoff oa (fun z => score z.2) := by
  classical
  unfold expectedPayoff
  calc
    Pr[ fun z => z.2.2 = true | oa] ≤ ∑' z, Pr[= z | oa] * score z.2 := by
      apply probEvent_le_tsum_probOutput_mul_cost
      intro z hz
      exact hscore z.2 hz
    _ ≤ Pr[⊥ | oa] + ∑' z, Pr[= z | oa] * score z.2 := le_add_left le_rfl

end OracleComp

namespace SCKAScheme

open OracleComp sckaCorrectnessSpec

variable {IK StA StB I Rho Rand : Type}

/-- Whether a correctness-game query is `SendA` or `SendB`. -/
def isSendQuery (t : (sckaCorrectnessSpec Rho).Domain) : Bool :=
  match t with
  | OSendA | OSendB => true
  | _ => false

/-- The proposition that a correctness-game query is a send query. -/
def IsSendQuery (t : (sckaCorrectnessSpec Rho).Domain) : Prop :=
  isSendQuery t = true

/-- Decides whether a correctness-game query is a send query. -/
instance : DecidablePred (IsSendQuery (Rho := Rho)) :=
  fun t => inferInstanceAs (Decidable (isSendQuery t = true))

/-- The adversary makes at most `q` send queries, both parties counted. -/
def SendQueryBound (adv : SCKACorrectnessAdversary Rho) (q : ℕ) : Prop :=
  adv.IsQueryBoundP (IsSendQuery (Rho := Rho)) q

/-- Per-query expected-score bounds, with an allowance of `ε` on send queries only, give a bound
`q · ε` on the probability that the flag is set after an adversary making at most `q` send
queries, starting from a state of score `0`. -/
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
        score p + if IsSendQuery t then ε else 0)
    (adv : SCKACorrectnessAdversary Rho) (q : ℕ) (hq : SendQueryBound adv q)
    (s₀ : GameState StA StB I Rho) (hinit : trackedInv Inv bad (s₀, false))
    (hscore₀ : score (s₀, false) = 0) :
    Pr[ fun z => z.2.2 = true |
        (simulateQ (trackedImpl (sckaCorrectnessImpl scka) bad) adv).run (s₀, false)] ≤
      (q : ℝ≥0∞) * ε := by
  calc
    Pr[ fun z => z.2.2 = true |
        (simulateQ (trackedImpl (sckaCorrectnessImpl scka) bad) adv).run (s₀, false)] ≤
        expectedPayoff
          ((simulateQ (trackedImpl (sckaCorrectnessImpl scka) bad) adv).run (s₀, false))
          (fun z => score z.2) :=
      tracked_bad_probability_le_score score hscore1 _
    _ ≤ score (s₀, false) + (q : ℝ≥0∞) * ε :=
      expectedPayoff_simulateQ_run_le (trackedImpl (sckaCorrectnessImpl scka) bad)
        (trackedInv Inv bad) score (IsSendQuery (Rho := Rho)) ε hpres hstep adv q hq
        (s₀, false) hinit
    _ = (q : ℝ≥0∞) * ε := by rw [hscore₀, zero_add]

/-- A bound on the probability that the final flag is set bounds the failure probability of the
correctness experiment, given that the experiment is the final `correct` bit of the ordinary
run from `s₀` and that the invariant forces `correct = true`. -/
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
    (hbad : Pr[ fun z => z.2.2 = true |
      (simulateQ (trackedImpl (sckaCorrectnessImpl scka) bad) adv).run (s₀, false)] ≤ δ) :
    Pr[= false | correctnessExp scka adv] ≤ δ := by
  set tracked := trackedImpl (sckaCorrectnessImpl scka) bad with htracked
  have hmono :
      Pr[ fun z => z.2.1.correct = false | (simulateQ tracked adv).run (s₀, false)] ≤
        Pr[ fun z => z.2.2 = true | (simulateQ tracked adv).run (s₀, false)] := by
    refine probEvent_mono ?_
    intro z hz hincorrect
    have hzInv : trackedInv Inv bad z.2 :=
      simulateQ_run_preservesInv tracked (trackedInv Inv bad) hpres adv (s₀, false) hinit z hz
    rcases hzInv with hflag | ⟨hinv, -⟩
    · exact hflag
    · simp [hcorrect _ hinv] at hincorrect
  calc
    Pr[= false | correctnessExp scka adv] =
        Pr[ fun z => z.2.1.correct = false | (simulateQ tracked adv).run (s₀, false)] := by
      rw [hexp, ← probEvent_eq_eq_probOutput, probEvent_map]
      have hproject := tracked_run_project (sckaCorrectnessImpl scka) bad adv (s₀, false)
      rw [← hproject, probEvent_map]
      congr 1
    _ ≤ Pr[ fun z => z.2.2 = true | (simulateQ tracked adv).run (s₀, false)] := hmono
    _ ≤ δ := hbad

end SCKAScheme
