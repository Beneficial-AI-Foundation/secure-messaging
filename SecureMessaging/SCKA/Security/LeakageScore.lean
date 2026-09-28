/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Security.Leakage
import ToVCVio.OracleComp.ExpectedPayoff

/-!
# Expected scores for leaking sends

**Parameters.** Fix a scheme, party `X ∈ {A, B}`, send-exposure rule
`L : StX → StX → Rand → Finset ℕ`, game state `s`, epoch set `E`,
score `Φ : GameState → ℝ≥0∞`, and bound `c : ℝ≥0∞`.

**Assumptions.**

* For every local state, forgetting send coins gives the ordinary send.
* For every supported successful leaking-send output with next local state
  `u` and coins `r`, `L(s.stX, u, r) = E`.
* For every game state `u` and set `F`, `Φ({u with exposed := F}) = Φ(u)`.
* `Φ(s) ≤ c`, and the ordinary game send satisfies `𝔼[Φ(s')] ≤ c`.

**Conclusion.** `𝔼[Φ(s')] ≤ c`, where `(response, s')` is sampled by running
party X's guarded leaking-send oracle from `s`.

**Proof.** If `E ∩ s.challenged = ∅`, the guard accepts every successful
sample, and the marginal equality transfers the expected score. Otherwise,
every successful sample is rejected and the game retains score `Φ(s)`.
Unsuccessful protocol outputs also retain `s`.
-/

open OracleSpec OracleComp ENNReal

namespace SCKAScheme

variable {IK StA StB I Rho Rand : Type} [DecidableEq I]

/-- Fix a state `s`, exposure set `E`, score `Φ`, and bound `c`. Assume:

* forgetting coins recovers A's ordinary send at every local state;
* every supported successful leaking send from `s` exposes `E`;
* `Φ({u with exposed := F}) = Φ(u)` for every state `u` and set `F`;
* `Φ(s) ≤ c`, and A's ordinary game send from `s` has expected score at most `c`.

Then A's guarded leaking game send from `s` has expected score at most `c`. -/
theorem oracleSendArleak_expectedPayoff_le
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StA → StA → Rand → Finset ℕ)
    (hm : ∀ st, (do
      let out ← scka.sendArleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        scka.sendA st)
    (s : GameState StA StB I Rho) (E : Finset ℕ)
    (hE : ∀ key msg epoch state coins,
      some (key, msg, epoch, state, coins) ∈ support (scka.sendArleak s.stA) →
      leak s.stA state coins = E)
    (score : GameState StA StB I Rho → ℝ≥0∞)
    (hbook : ∀ state exposed, score { state with exposed := exposed } = score state)
    (c : ℝ≥0∞) (hs : score s ≤ c)
    (hplain : expectedPayoff ((oracleSendA scka ()).run s) (fun z => score z.2) ≤ c) :
    expectedPayoff ((oracleSendArleak leak scka ()).run s) (fun z => score z.2) ≤ c := by
  by_cases hguard : E ∩ s.challenged ≠ ∅
  · apply expectedPayoff_le_const_of_support _ _ _ probFailure_eq_zero
    intro z hz
    simp only [oracleSendArleak, StateT.run_bind, StateT.run_get, pure_bind,
      StateT.run_monadLift, monadLift_self, bind_assoc] at hz
    rw [mem_support_bind_iff] at hz
    obtain ⟨out, hout, hz⟩ := hz
    cases out with
    | none => simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
    | some out =>
      rcases out with ⟨key, msg, epoch, state, coins⟩
      dsimp only at hz
      rw [hE key msg epoch state coins hout] at hz
      split at hz
      · simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
      · contradiction
  · suffices heq : expectedPayoff ((oracleSendArleak leak scka ()).run s)
        (fun z => score z.2) =
        expectedPayoff ((oracleSendA scka ()).run s) (fun z => score z.2) by
      exact heq ▸ hplain
    simp only [oracleSendArleak, oracleSendA, StateT.run_bind, StateT.run_get,
      pure_bind, StateT.run_monadLift, monadLift_self, bind_assoc]
    rw [← hm s.stA]
    simp only [bind_assoc, pure_bind, expectedPayoff_bind]
    congr 1
    apply tsum_congr
    intro out
    by_cases hout : out ∈ support (scka.sendArleak s.stA)
    · cases out with
      | none => simp [expectedPayoff_pure]
      | some out =>
        rcases out with ⟨key, msg, epoch, state, coins⟩
        simp only [hE key msg epoch state coins hout, hguard, ↓reduceIte]
        cases key <;> simp only [Option.map_some, StateT.run_bind, StateT.run_set,
          pure_bind, StateT.run_pure, expectedPayoff_pure]
        all_goals
          congr 1
          conv_rhs => rw [← hbook _ (s.exposed ∪ E)]
    · have hz : Pr[= out | scka.sendArleak s.stA] = 0 := by
        exact probOutput_eq_zero_of_not_mem_support hout
      simp only [hz, zero_mul]

/-- Fix a state `s`, exposure set `E`, score `Φ`, and bound `c`. Assume:

* forgetting coins recovers B's ordinary send at every local state;
* every supported successful leaking send from `s` exposes `E`;
* `Φ({u with exposed := F}) = Φ(u)` for every state `u` and set `F`;
* `Φ(s) ≤ c`, and B's ordinary game send from `s` has expected score at most `c`.

Then B's guarded leaking game send from `s` has expected score at most `c`. -/
theorem oracleSendBrleak_expectedPayoff_le
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StB → StB → Rand → Finset ℕ)
    (hm : ∀ st, (do
      let out ← scka.sendBrleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        scka.sendB st)
    (s : GameState StA StB I Rho) (E : Finset ℕ)
    (hE : ∀ key msg epoch state coins,
      some (key, msg, epoch, state, coins) ∈ support (scka.sendBrleak s.stB) →
      leak s.stB state coins = E)
    (score : GameState StA StB I Rho → ℝ≥0∞)
    (hbook : ∀ state exposed, score { state with exposed := exposed } = score state)
    (c : ℝ≥0∞) (hs : score s ≤ c)
    (hplain : expectedPayoff ((oracleSendB scka ()).run s) (fun z => score z.2) ≤ c) :
    expectedPayoff ((oracleSendBrleak leak scka ()).run s) (fun z => score z.2) ≤ c := by
  by_cases hguard : E ∩ s.challenged ≠ ∅
  · apply expectedPayoff_le_const_of_support _ _ _ probFailure_eq_zero
    intro z hz
    simp only [oracleSendBrleak, StateT.run_bind, StateT.run_get, pure_bind,
      StateT.run_monadLift, monadLift_self, bind_assoc] at hz
    rw [mem_support_bind_iff] at hz
    obtain ⟨out, hout, hz⟩ := hz
    cases out with
    | none => simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
    | some out =>
      rcases out with ⟨key, msg, epoch, state, coins⟩
      dsimp only at hz
      rw [hE key msg epoch state coins hout] at hz
      split at hz
      · simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
      · contradiction
  · suffices heq : expectedPayoff ((oracleSendBrleak leak scka ()).run s)
        (fun z => score z.2) =
        expectedPayoff ((oracleSendB scka ()).run s) (fun z => score z.2) by
      exact heq ▸ hplain
    simp only [oracleSendBrleak, oracleSendB, StateT.run_bind, StateT.run_get,
      pure_bind, StateT.run_monadLift, monadLift_self, bind_assoc]
    rw [← hm s.stB]
    simp only [bind_assoc, pure_bind, expectedPayoff_bind]
    congr 1
    apply tsum_congr
    intro out
    by_cases hout : out ∈ support (scka.sendBrleak s.stB)
    · cases out with
      | none => simp [expectedPayoff_pure]
      | some out =>
        rcases out with ⟨key, msg, epoch, state, coins⟩
        simp only [hE key msg epoch state coins hout, hguard, ↓reduceIte]
        cases key <;> simp only [Option.map_some, StateT.run_bind, StateT.run_set,
          pure_bind, StateT.run_pure, expectedPayoff_pure]
        all_goals
          congr 1
          conv_rhs => rw [← hbook _ (s.exposed ∪ E)]
    · have hz : Pr[= out | scka.sendBrleak s.stB] = 0 := by
        exact probOutput_eq_zero_of_not_mem_support hout
      simp only [hz, zero_mul]

end SCKAScheme
