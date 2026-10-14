/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Defs
import ToVCVio.OracleComp.SimSemantics.StateT.Stop
import ToVCVio.OracleComp.ExpectedPayoff

/-!
# SCKA security oracles

The results apply to an arbitrary SCKA scheme over `ProbComp` and state exposure functions
satisfying the hypotheses below. An SCKA game state has the following structure:

```text
s = (stA, stB, keyA, keyB, msgA, msgB, nA, nB, tcurA, tcurB,
     exposed, challenged, correct).
```

The finite sets `exposed, challenged ⊆ ℕ` record epochs exposed by corruption or randomness leakage,
and epochs whose challenges were successfully answered, respectively.
For a predicate `Inv` on game states, preservation means `Inv(s) → Inv(s')` for every
possible oracle transition `s → s'`.

For leaking send operations, we always assume that discarding
the returned coins recovers the ordinary-send computation.

- **State updates.** Challenge and corruption queries can change only `challenged` and
  `exposed` part of the game state, respectively; rejected queries leave the game state unchanged.
- **Invariant preservation.** If `Inv` remains true when `challenged` is replaced by any
  finite set, then challenge queries preserve `Inv`.
  The same holds for corruption queries and `exposed`. For leaking sends, assume `Inv` holds
  before the query and in every possible ordinary-send successor, and remains true under
  arbitrary changes to `exposed`. Then it holds in every possible leaking-send successor.
- **Expected-score bounds.** Suppose every successful leaking send from a state `s` exposes
  the same set of epochs. For a score independent of `exposed`, a bound `c` on both the initial
  score and its expectation after an ordinary send also bounds its expectation after a leaking
  send.
- **Full oracle family.** `securityImplOf` combines correctness and challenge oracles with
  leaking-send and corruption oracles. Invariant preservation by each component implies
  preservation by the full family. Replacing the correctness and challenge components by equal
  query computations preserves the full family's query computations.
-/

open OracleSpec OracleComp ENNReal

namespace SCKAScheme

variable {IK StA StB I Rho Rand : Type}

/-! ## Individual security oracles -/

/-! ### Challenge -/

section Challenge

variable [SampleableType I]

/-- Challenging an exposed or previously challenged epoch returns `none`
and preserves the state, in both fixed-bit experiments. -/
theorem oracleChall_rejected (b : Bool) (s : GameState StA StB I Rho) (t : ℕ)
    (h : t ∈ s.exposed ∨ t ∈ s.challenged) :
    (oracleChall b StA StB I Rho t).run s = pure (none, s) := by
  simp [oracleChall, h]

/-- A challenge whose two key-table entries are `none` returns `none` and retains the
state, regardless of `exposed`, `challenged`, and the challenge bit `b`. -/
theorem oracleChall_unavailable (b : Bool) (s : GameState StA StB I Rho) (t : ℕ)
    (hA : s.keyA t = none) (hB : s.keyB t = none) :
    (oracleChall b StA StB I Rho t).run s = pure (none, s) := by
  by_cases h : t ∈ s.exposed ∨ t ∈ s.challenged
  · exact oracleChall_rejected b s t h
  · simp [oracleChall, h, hA, hB]

/-- Every possible result of a challenge at epoch `t` is `(none, s)` if `t` is exposed,
previously challenged, or has no recorded key. Otherwise, `t` is eligible and the successor
state differs from `s` only by inserting `t` into `challenged`. -/
theorem oracleChall_support (b : Bool) (s : GameState StA StB I Rho) (t : ℕ)
    (z : Option I × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleChall b StA StB I Rho t).run s)) :
    (z = (none, s) ∧
        ((t ∈ s.exposed ∨ t ∈ s.challenged) ∨ (s.keyA t = none ∧ s.keyB t = none))) ∨
      (¬(t ∈ s.exposed ∨ t ∈ s.challenged) ∧ ((s.keyA t).isSome ∨ (s.keyB t).isSome) ∧
        z.2 = { s with challenged := insert t s.challenged }) := by
  by_cases h : t ∈ s.exposed ∨ t ∈ s.challenged
  · rw [oracleChall_rejected b s t h] at hz
    exact Or.inl ⟨(mem_support_pure_iff _ _).mp hz, Or.inl h⟩
  by_cases hkey : (s.keyA t).isSome ∨ (s.keyB t).isSome
  · refine Or.inr ⟨h, hkey, ?_⟩
    cases hA : s.keyA t <;> cases hB : s.keyB t <;> cases b <;>
      simp only [oracleChall, Bool.false_eq_true, ↓reduceIte, bind_pure_comp,
        pure_bind, StateT.run_bind, StateT.run_get, h, hA, hB, StateT.run_pure,
        StateT.run_map, StateT.run_set, StateT.run_monadLift, monadLift_self,
        map_pure, Functor.map_map, support_pure, Set.mem_singleton_iff,
        support_map, support_uniformSample, Set.image_univ, Set.mem_range] at hz
    all_goals
      first
      | (obtain rfl := hz; rfl)
      | (obtain ⟨k, rfl⟩ := hz; rfl)
      | simp [hA, hB] at hkey
  · have hA : s.keyA t = none := by cases hA : s.keyA t <;> simp_all
    have hB : s.keyB t = none := by cases hB : s.keyB t <;> simp_all
    rw [oracleChall_unavailable b s t hA hB] at hz
    exact Or.inl ⟨(mem_support_pure_iff _ _).mp hz, Or.inr ⟨hA, hB⟩⟩

end Challenge

/-- A challenge oracle `chall` records challenges if every supported successor of a query `t`
from `s` equals `s` or, when `t ∉ s.exposed`, differs only by inserting `t` into `challenged`. -/
def RecordsChallenges
    (chall : QueryImpl (ℕ →ₒ Option I) (StateT (GameState StA StB I Rho) ProbComp)) : Prop :=
  ∀ (t : ℕ) s z, z ∈ support ((chall t).run s) →
    z.2 = s ∨ (t ∉ s.exposed ∧ z.2 = { s with challenged := insert t s.challenged })

namespace RecordsChallenges

variable {chall : QueryImpl (ℕ →ₒ Option I) (StateT (GameState StA StB I Rho) ProbComp)}

/-- A challenge oracle satisfying `RecordsChallenges` preserves every invariant preserved
by arbitrary changes to `challenged`. -/
theorem preservesInv (h : RecordsChallenges chall) (Inv : GameState StA StB I Rho → Prop)
    (hbook : ∀ s challenged, Inv s → Inv { s with challenged := challenged }) :
    QueryImpl.PreservesInv chall Inv := by
  intro t s hs z hz
  rcases h t s z hz with h | ⟨_, h⟩
  · rw [h]; exact hs
  · rw [h]; exact hbook s _ hs

end RecordsChallenges

/-- For either bit `b`, the challenge oracle `oracleChall b` satisfies `RecordsChallenges`. -/
theorem oracleChall_recordsChallenges [SampleableType I] (b : Bool) :
    RecordsChallenges (oracleChall b StA StB I Rho) := by
  intro t s z hz
  rcases oracleChall_support b s t z hz with ⟨h, _⟩ | ⟨helig, _, h⟩
  · exact Or.inl (by rw [h])
  · exact Or.inr ⟨fun ht => helig (Or.inl ht), h⟩

/-! ### Corruption -/

/-- The corruption of A is a deterministic update: rejection returns `(none, s)`;
acceptance returns A's state and adds its vulnerable set to `exposed`. -/
theorem oracleCorruptA_run (vuln : StA → Finset ℕ) (s : GameState StA StB I Rho) :
    (oracleCorruptA vuln StB I Rho ()).run s =
      if vuln s.stA ∩ s.challenged ≠ ∅ then pure (none, s)
      else pure (some s.stA, { s with exposed := s.exposed ∪ vuln s.stA }) := by
  by_cases h : vuln s.stA ∩ s.challenged ≠ ∅
  · simp [oracleCorruptA, h]
  · simp [oracleCorruptA, not_not.mp h]

/-- Support of the corruption of A: rejection with the state unchanged, or acceptance when the
vulnerable set is disjoint from `challenged`. -/
theorem oracleCorruptA_support (vuln : StA → Finset ℕ) (s : GameState StA StB I Rho)
    (z : Option StA × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleCorruptA vuln StB I Rho ()).run s)) :
    z = (none, s) ∨
      (vuln s.stA ∩ s.challenged = ∅ ∧
        z = (some s.stA, { s with exposed := s.exposed ∪ vuln s.stA })) := by
  rw [oracleCorruptA_run] at hz
  split_ifs at hz with h
  · exact Or.inl ((mem_support_pure_iff _ _).mp hz)
  · exact Or.inr ⟨not_not.mp h, (mem_support_pure_iff _ _).mp hz⟩

/-- Corruption of A preserves every invariant preserved by arbitrary changes to `exposed`. -/
theorem oracleCorruptA_preservesInv (vuln : StA → Finset ℕ)
    (Inv : GameState StA StB I Rho → Prop)
    (hbook : ∀ s exposed, Inv s → Inv { s with exposed := exposed }) :
    QueryImpl.PreservesInv (oracleCorruptA vuln StB I Rho) Inv := by
  intro _ s hs z hz
  rcases oracleCorruptA_support vuln s z hz with h | ⟨_, h⟩
  · rw [h]; exact hs
  · rw [h]; exact hbook _ _ hs

/-- The corruption of B is a deterministic update: rejection returns `(none, s)`;
acceptance returns B's state and adds its vulnerable set to `exposed`. -/
theorem oracleCorruptB_run (vuln : StB → Finset ℕ) (s : GameState StA StB I Rho) :
    (oracleCorruptB vuln StA I Rho ()).run s =
      if vuln s.stB ∩ s.challenged ≠ ∅ then pure (none, s)
      else pure (some s.stB, { s with exposed := s.exposed ∪ vuln s.stB }) := by
  by_cases h : vuln s.stB ∩ s.challenged ≠ ∅
  · simp [oracleCorruptB, h]
  · simp [oracleCorruptB, not_not.mp h]

/-- Support of the corruption of B: rejection with the state unchanged, or acceptance when the
vulnerable set is disjoint from `challenged`. -/
theorem oracleCorruptB_support (vuln : StB → Finset ℕ) (s : GameState StA StB I Rho)
    (z : Option StB × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleCorruptB vuln StA I Rho ()).run s)) :
    z = (none, s) ∨
      (vuln s.stB ∩ s.challenged = ∅ ∧
        z = (some s.stB, { s with exposed := s.exposed ∪ vuln s.stB })) := by
  rw [oracleCorruptB_run] at hz
  split_ifs at hz with h
  · exact Or.inl ((mem_support_pure_iff _ _).mp hz)
  · exact Or.inr ⟨not_not.mp h, (mem_support_pure_iff _ _).mp hz⟩

/-- Corruption of B preserves every invariant preserved by arbitrary changes to `exposed`. -/
theorem oracleCorruptB_preservesInv (vuln : StB → Finset ℕ)
    (Inv : GameState StA StB I Rho → Prop)
    (hbook : ∀ s exposed, Inv s → Inv { s with exposed := exposed }) :
    QueryImpl.PreservesInv (oracleCorruptB vuln StA I Rho) Inv := by
  intro _ s hs z hz
  rcases oracleCorruptB_support vuln s z hz with h | ⟨_, h⟩
  · rw [h]; exact hs
  · rw [h]; exact hbook _ _ hs

/-! ### Leaking sends -/

section LeakingSend

variable [DecidableEq I]

/-- Suppose discarding A's returned coins recovers its ordinary send for every local state.
Let `Inv` hold at `s` and be preserved by arbitrary changes to `exposed`. If every ordinary-send
successor from `s` satisfies `Inv`, then every leaking-send successor from `s` does too. -/
theorem oracleSendArleak_preservesInv_at
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StA → Rand → Finset ℕ)
    (hm : ∀ st, (do
      let out ← scka.sendArleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        scka.sendA st)
    (Inv : GameState StA StB I Rho → Prop)
    (hbook : ∀ s exposed, Inv s → Inv { s with exposed := exposed })
    (s : GameState StA StB I Rho) (hs : Inv s)
    (hplain : ∀ z ∈ support ((oracleSendA scka ()).run s), Inv z.2)
    (z : Option (ℕ × Option ℕ × Rho × Rand) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleSendArleak leak scka ()).run s)) : Inv z.2 := by
  simp only [oracleSendArleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc] at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨out, hout, hz⟩ := hz
  cases out with
  | none =>
      simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
  | some out =>
      rcases out with ⟨key, msg, epoch, state, coins⟩
      have hout' : some (key, msg, epoch, state) ∈ support (scka.sendA s.stA) := by
        rw [← hm]
        exact (mem_support_bind_iff _ _ _).mpr ⟨_, hout, by simp⟩
      dsimp only at hz
      split at hz
      · simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
      · cases key <;>
          simp only [StateT.run_bind, StateT.run_set, pure_bind,
            StateT.run_pure, mem_support_pure_iff] at hz
        all_goals
          suffices h : Inv { z.2 with exposed := s.exposed } by
            simpa using hbook _ z.2.exposed h
          refine hplain
            (z.1.map (fun (t, ti, msg, _) => (t, ti, msg)),
              { z.2 with exposed := s.exposed }) ?_
          obtain rfl := hz
          simp only [oracleSendA, StateT.run_bind, StateT.run_get, pure_bind,
            StateT.run_monadLift, monadLift_self, bind_assoc]
          apply (mem_support_bind_iff _ _ _).mpr
          exact ⟨_, hout', by simp⟩

/-- The version of `oracleSendArleak_preservesInv_at` for B. -/
theorem oracleSendBrleak_preservesInv_at
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StB → Rand → Finset ℕ)
    (hm : ∀ st, (do
      let out ← scka.sendBrleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        scka.sendB st)
    (Inv : GameState StA StB I Rho → Prop)
    (hbook : ∀ s exposed, Inv s → Inv { s with exposed := exposed })
    (s : GameState StA StB I Rho) (hs : Inv s)
    (hplain : ∀ z ∈ support ((oracleSendB scka ()).run s), Inv z.2)
    (z : Option (ℕ × Option ℕ × Rho × Rand) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleSendBrleak leak scka ()).run s)) : Inv z.2 := by
  simp only [oracleSendBrleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc] at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨out, hout, hz⟩ := hz
  cases out with
  | none =>
      simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
  | some out =>
      rcases out with ⟨key, msg, epoch, state, coins⟩
      have hout' : some (key, msg, epoch, state) ∈ support (scka.sendB s.stB) := by
        rw [← hm]
        exact (mem_support_bind_iff _ _ _).mpr ⟨_, hout, by simp⟩
      dsimp only at hz
      split at hz
      · simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
      · cases key <;>
          simp only [StateT.run_bind, StateT.run_set, pure_bind,
            StateT.run_pure, mem_support_pure_iff] at hz
        all_goals
          suffices h : Inv { z.2 with exposed := s.exposed } by
            simpa using hbook _ z.2.exposed h
          refine hplain
            (z.1.map (fun (t, ti, msg, _) => (t, ti, msg)),
              { z.2 with exposed := s.exposed }) ?_
          obtain rfl := hz
          simp only [oracleSendB, StateT.run_bind, StateT.run_get, pure_bind,
            StateT.run_monadLift, monadLift_self, bind_assoc]
          apply (mem_support_bind_iff _ _ _).mpr
          exact ⟨_, hout', by simp⟩

end LeakingSend

/-! ## Expected scores of leaking sends -/

section ExpectedScores

variable [DecidableEq I]

/-- Suppose discarding A's send coins recovers its ordinary send, and every supported
successful leaking-send output from `s` exposes the same set `E`. Every score unchanged by
updates to `exposed` then has expected value at most `c` after the leaking-send query, provided
`score s ≤ c` and its expected value after the ordinary-send query is at most `c`. -/
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

/-- The expected-score bound of `oracleSendArleak_expectedPayoff_le` for B. -/
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

end ExpectedScores

/-! ## Full security oracle family -/

section SecurityFamily

variable [DecidableEq I]

/-- Assemble the security oracles for a proof game. `base` supplies uniform sampling,
ordinary sends, and receives; `chall` supplies challenges. Leaking sends and corruptions
use the given scheme and exposure functions. -/
def securityImplOf
    (base : QueryImpl (sckaCorrectnessSpec Rho) (StateT (GameState StA StB I Rho) ProbComp))
    (chall : QueryImpl (ℕ →ₒ Option I) (StateT (GameState StA StB I Rho) ProbComp))
    (vulnA : VulnerableEpochs StA Rand) (vulnB : VulnerableEpochs StB Rand)
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) :
    QueryImpl (sckaSecuritySpec StA StB I Rho Rand)
      (StateT (GameState StA StB I Rho) ProbComp) :=
  base
    + oracleSendArleak vulnA.rleak scka + oracleSendBrleak vulnB.rleak scka
    + chall
    + oracleCorruptA vulnA.corrupt StB I Rho + oracleCorruptB vulnB.corrupt StA I Rho

variable (base : QueryImpl (sckaCorrectnessSpec Rho) (StateT (GameState StA StB I Rho) ProbComp))
variable (chall : QueryImpl (ℕ →ₒ Option I) (StateT (GameState StA StB I Rho) ProbComp))
variable (vulnA : VulnerableEpochs StA Rand) (vulnB : VulnerableEpochs StB Rand)
variable (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)

/-- If each component query from `s` produces only states satisfying `Inv`, then every
assembled security query from `s` does too. -/
theorem securityImplOf_preserves_at (Inv : GameState StA StB I Rho → Prop)
    (s : GameState StA StB I Rho)
    (hbase : ∀ t z, z ∈ support ((base t).run s) → Inv z.2)
    (hA : ∀ z ∈ support ((oracleSendArleak vulnA.rleak scka ()).run s), Inv z.2)
    (hB : ∀ z ∈ support ((oracleSendBrleak vulnB.rleak scka ()).run s), Inv z.2)
    (hC : ∀ (t : ℕ) z, z ∈ support ((chall t).run s) → Inv z.2)
    (hcA : ∀ z ∈ support ((oracleCorruptA vulnA.corrupt StB I Rho ()).run s), Inv z.2)
    (hcB : ∀ z ∈ support ((oracleCorruptB vulnB.corrupt StA I Rho ()).run s), Inv z.2)
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain)
    (z : (sckaSecuritySpec StA StB I Rho Rand).Range t × GameState StA StB I Rho)
    (hz : z ∈ support ((securityImplOf base chall vulnA vulnB scka t).run s)) :
    Inv z.2 := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · exact hbase t z hz
  · cases u; exact hA z hz
  · cases u; exact hB z hz
  · exact hC t z hz
  · cases u; exact hcA z hz
  · cases u; exact hcB z hz

/-- Suppose discarding send coins recovers ordinary sends and `chall` satisfies
`RecordsChallenges`. Let `Inv` hold at `s` and be preserved by arbitrary changes to `exposed`
and `challenged`. If `base` and both ordinary-send oracles produce only states satisfying
`Inv` from `s`, then every assembled security query from `s` does too. -/
theorem securityImplOf_preserves_at_of_book (Inv : GameState StA StB I Rho → Prop)
    (hbook : ∀ s exposed challenged, Inv s →
      Inv { s with exposed := exposed, challenged := challenged })
    (hmA : ∀ st, (do
      let out ← scka.sendArleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        scka.sendA st)
    (hmB : ∀ st, (do
      let out ← scka.sendBrleak st
      pure (out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))) =
        scka.sendB st)
    (hchall : RecordsChallenges chall)
    (s : GameState StA StB I Rho) (hs : Inv s)
    (hbase : ∀ t z, z ∈ support ((base t).run s) → Inv z.2)
    (hsendA : ∀ z ∈ support ((oracleSendA scka ()).run s), Inv z.2)
    (hsendB : ∀ z ∈ support ((oracleSendB scka ()).run s), Inv z.2)
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain)
    (z : (sckaSecuritySpec StA StB I Rho Rand).Range t × GameState StA StB I Rho)
    (hz : z ∈ support ((securityImplOf base chall vulnA vulnB scka t).run s)) :
    Inv z.2 := by
  have hexp : ∀ s exposed, Inv s → Inv { s with exposed := exposed } :=
    fun s exposed h => by simpa using hbook s exposed s.challenged h
  have hch : ∀ s challenged, Inv s → Inv { s with challenged := challenged } :=
    fun s challenged h => by simpa using hbook s s.exposed challenged h
  refine securityImplOf_preserves_at base chall vulnA vulnB scka Inv s hbase
    (fun z hz => oracleSendArleak_preservesInv_at scka vulnA.rleak hmA Inv hexp s hs hsendA z hz)
    (fun z hz => oracleSendBrleak_preservesInv_at scka vulnB.rleak hmB Inv hexp s hs hsendB z hz)
    (fun t z hz => hchall.preservesInv Inv hch t s hs z hz)
    (fun z hz => oracleCorruptA_preservesInv vulnA.corrupt Inv hexp () s hs z hz)
    (fun z hz => oracleCorruptB_preservesInv vulnB.corrupt Inv hexp () s hs z hz) t z hz

/-- If `base` and `base'` have equal query computations from `s`, and so do `chall` and
`chall'`, the two assembled security implementations have equal query computations from `s`. -/
theorem securityImplOf_run_eq
    (base' : QueryImpl (sckaCorrectnessSpec Rho) (StateT (GameState StA StB I Rho) ProbComp))
    (chall' : QueryImpl (ℕ →ₒ Option I) (StateT (GameState StA StB I Rho) ProbComp))
    (s : GameState StA StB I Rho)
    (hbase : ∀ t, (base t).run s = (base' t).run s)
    (hchall : ∀ t : ℕ, (chall t).run s = (chall' t).run s)
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain) :
    (securityImplOf base chall vulnA vulnB scka t).run s =
      (securityImplOf base' chall' vulnA vulnB scka t).run s := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · exact hbase t
  · rfl
  · rfl
  · exact hchall t
  · rfl
  · rfl

end SecurityFamily

end SCKAScheme
