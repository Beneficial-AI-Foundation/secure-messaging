/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.OracleComp.SimSemantics.StateT.ExpectedPayoffBound
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Stateful simulation with a sticky bad flag

**Setting.** Let

- `impl : QueryImpl spec (StateT σ ProbComp)` be a stateful oracle implementation;
- `bad : σ → Bool` mark the states after which nothing needs to be proved;
- `Inv : σ → Prop` be an invariant that only has to hold until the first bad state.

`trackedImpl impl bad` runs `impl` on pairs `(s, b) : σ × Bool` and sets the flag `b` as soon as
the resulting state is bad; the flag is never cleared. `trackedInv Inv bad (s, b)` holds when the
flag is set, or `Inv s` holds and `s` is not bad.

**Results.**

- `tracked_run_project`: forgetting the flag after a tracked run gives the run of `impl`;
- `trackedImpl_preserves`: if every query preserves `Inv` from states that are not bad, the
  tracked implementation preserves `trackedInv Inv bad`;
- `tracked_bad_probability_le_score`: the probability that the flag is set is at most the
  expected value of any score that is at least `1` on flagged states;
- `tracked_bad_le_of_score_step`: if a query raises the expected score by at most `ε` when it
  satisfies `p` and not at all otherwise, then after a computation making at most `q` queries
  satisfying `p` the flag is set with probability at most `score (s₀, false) + q · ε`;
- `probEvent_not_good_le_tracked_bad`: if `Inv` forces `good s = true`, then the run of `impl`
  ends in a state with `good s = false` with probability at most that of the flag being set.

With the flag, `Inv` only has to be preserved from states that are not bad, so nothing has to be
proved about the states that follow the first bad one.
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
    Pr{let z ← oa}[z.2.2 = true] ≤ expectedPayoff oa (fun z => score z.2) :=
  probEvent_le_expectedPayoff oa _ _ fun z hz => hscore z.2 hz

/-- Per-query expected-score bounds, with an allowance of `ε` on queries satisfying `p` only,
give a bound `score (s₀, false) + q · ε` on the probability that the flag is set after a
computation making at most `q` queries satisfying `p`. -/
theorem tracked_bad_le_of_score_step (impl : QueryImpl spec (StateT σ ProbComp))
    (bad : σ → Bool) (Inv : σ → Prop) (score : σ × Bool → ℝ≥0∞)
    (p : ι → Prop) [DecidablePred p] (ε : ℝ≥0∞)
    (hscore1 : ∀ x : σ × Bool, x.2 = true → 1 ≤ score x)
    (hpres : QueryImpl.PreservesInv (trackedImpl impl bad) (trackedInv Inv bad))
    (hstep : ∀ t x, trackedInv Inv bad x →
      expectedPayoff (((trackedImpl impl bad) t).run x) (fun z => score z.2) ≤
        score x + if p t then ε else 0)
    {α : Type} (oa : OracleComp spec α) (q : ℕ) (hq : oa.IsQueryBoundP p q)
    (s₀ : σ) (hinit : trackedInv Inv bad (s₀, false)) :
    Pr{let z ← (simulateQ (trackedImpl impl bad) oa).run (s₀, false)}[z.2.2 = true] ≤
      score (s₀, false) + (q : ℝ≥0∞) * ε :=
  (tracked_bad_probability_le_score score hscore1 _).trans
    (expectedPayoff_simulateQ_run_le (trackedImpl impl bad) (trackedInv Inv bad) score p ε
      hpres hstep oa q hq (s₀, false) hinit)

/-- If `Inv` forces `good s = true`, the run of `impl` from `s₀` ends in a state with
`good s = false` with probability at most that of the flag being set at the end of the tracked
run from `(s₀, false)`. -/
theorem probEvent_not_good_le_tracked_bad (impl : QueryImpl spec (StateT σ ProbComp))
    (bad : σ → Bool) (Inv : σ → Prop) (good : σ → Bool) (hgood : ∀ s, Inv s → good s = true)
    (hpres : QueryImpl.PreservesInv (trackedImpl impl bad) (trackedInv Inv bad))
    {α : Type} (oa : OracleComp spec α) (s₀ : σ) (hinit : trackedInv Inv bad (s₀, false)) :
    Pr{let z ← (simulateQ impl oa).run s₀}[good z.2 = false] ≤
      Pr{let z ← (simulateQ (trackedImpl impl bad) oa).run (s₀, false)}[z.2.2 = true] := by
  rw [← tracked_run_project impl bad oa (s₀, false), prEvent_map]
  refine prEvent_mono_of_support _ _ _ ?_
  intro z hz hnotgood
  rcases simulateQ_run_preservesInv (trackedImpl impl bad) (trackedInv Inv bad) hpres oa
      (s₀, false) hinit z hz with hflag | ⟨hinv, -⟩
  · exact hflag
  · simp [hgood _ hinv] at hnotgood

end OracleComp
