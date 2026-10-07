/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Security.Oracles
import ToVCVio.OracleComp.SimSemantics.StateT.Stop
import ToVCVio.OracleComp.ExpectedPayoff

/-!
# Expected scores of guarded leaking sends

Let `scka : SCKAScheme ProbComp IK StA StB I Rho Rand` be a scheme and
`s : GameState StA StB I Rho` be a game state. For either party `X`, a leaking send is
*forgetful* if dropping its returned coins recovers the ordinary-send computation:
`(do let out ← scka.sendXrleak st; pure (out.map forgetCoins)) = scka.sendX st`
for every local state `st`.

For a forgetful leaking send whose supported successful outputs from `s` all expose the same
set `E`, every score `score : GameState StA StB I Rho → ℝ≥0∞` independent of `exposed`
satisfies: if `score s ≤ c` and the ordinary query's expected score is at most `c`, then the
guarded leaking query's expected score is at most `c`. The guard either rejects, retaining
`s`, or accepts and updates only `exposed`, which the score ignores.
-/

open OracleSpec OracleComp ENNReal

namespace SCKAScheme

variable {IK StA StB I Rho Rand τ : Type} [DecidableEq I]

/-- Let `score : GameState StA StB I Rho → ℝ≥0∞` be independent of `exposed`. Assume:

- forgetting A's send coins recovers its ordinary send;
- every supported successful leaking send from `s` exposes the same set `E`;
- `score s ≤ c` and the ordinary game send's expected score is at most `c`.

Then the guarded leaking game send's expected score is at most `c`. -/
theorem oracleSendArleak_expectedPayoff_le
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StA → Rand → Finset ℕ)
    (hm : ∀ st, (do
      let out ← scka.sendArleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        scka.sendA st)
    (s : GameState StA StB I Rho) (E : Finset ℕ)
    (hE : ∀ key msg epoch state coins,
      some (key, msg, epoch, state, coins) ∈ support (scka.sendArleak s.stA) →
      leak s.stA coins = E)
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

/-- Let `score : GameState StA StB I Rho → ℝ≥0∞` be independent of `exposed`. Assume:

- forgetting B's send coins recovers its ordinary send;
- every supported successful leaking send from `s` exposes the same set `E`;
- `score s ≤ c` and the ordinary game send's expected score is at most `c`.

Then the guarded leaking game send's expected score is at most `c`. -/
theorem oracleSendBrleak_expectedPayoff_le
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StB → Rand → Finset ℕ)
    (hm : ∀ st, (do
      let out ← scka.sendBrleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        scka.sendB st)
    (s : GameState StA StB I Rho) (E : Finset ℕ)
    (hE : ∀ key msg epoch state coins,
      some (key, msg, epoch, state, coins) ∈ support (scka.sendBrleak s.stB) →
      leak s.stB coins = E)
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
