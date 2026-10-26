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

Generic results for SCKA schemes over `ProbComp`. Recall the game state:

```text
s = (stA, stB, keyA, keyB, msgA, msgB, nA, nB, tcurA, tcurB,
     exposed, challenged, correct).
```

Here `exposed` records epochs exposed by corruption or randomness leakage, and `challenged`
records epochs whose challenges were successfully answered.

We prove:

- **State updates:** characterizations of challenge and corruption query outcomes, and the
  epoch-dependent challenge oracle `oracleChallOn`, whose query at epoch `t` is the fixed-bit
  challenge with bit `random t`.
- **Invariants:** conditions for security queries to preserve a predicate on game states.
- **Expected scores:** conditions for ordinary-send bounds to hold also for leaking sends.
- **Full oracle family:** `securityImplOf` combines correctness, challenge, leaking-send,
  and corruption oracles. We derive invariant preservation and equality of query computations
  from the corresponding component properties.
-/

open OracleSpec OracleComp ENNReal

namespace SCKAScheme

variable {IK StA StB I Rho Rand : Type}

/-! ## Individual security oracles -/

/-! ### Challenge -/

section Challenge

variable [SampleableType I]

/-- Challenging an exposed or previously challenged epoch returns `none`
and preserves the state. -/
theorem oracleChall_rejected (b : Bool) (s : GameState StA StB I Rho) (t : ℕ)
    (h : t ∈ s.exposed ∨ t ∈ s.challenged) :
    (oracleChall b StA StB I Rho t).run s = pure (none, s) := by
  simp [oracleChall, h]

/-- If the game's epoch-key tables for A and B, `s.keyA` and `s.keyB`, both contain `none`
at epoch `t`, challenging `t` returns `none` and leaves `s` unchanged, regardless of
`exposed` and `challenged`. -/
theorem oracleChall_unavailable (b : Bool) (s : GameState StA StB I Rho) (t : ℕ)
    (hA : s.keyA t = none) (hB : s.keyB t = none) :
    (oracleChall b StA StB I Rho t).run s = pure (none, s) := by
  by_cases h : t ∈ s.exposed ∨ t ∈ s.challenged
  · exact oracleChall_rejected b s t h
  · simp [oracleChall, h, hA, hB]

/-- Every possible result `z = (answer, s')` of a challenge at epoch `t` from state `s` satisfies
one of two cases:

- **Rejected or unavailable:** `t` is exposed or already challenged, or neither of the game's
  tables `s.keyA`, `s.keyB` records a key at `t`. Then `answer = none` and `s' = s`.
- **Eligible:** `t` is neither exposed nor already challenged, and at least one table records
  a key at `t`. Then `s' = { s with challenged := insert t s.challenged }`. -/
theorem oracleChall_support (b : Bool) (s : GameState StA StB I Rho) (t : ℕ)
    (z : Option I × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleChall b StA StB I Rho t).run s)) :
    (z = (none, s) ∧
      ((t ∈ s.exposed ∨ t ∈ s.challenged) ∨
        (s.keyA t = none ∧ s.keyB t = none))) ∨
    (¬(t ∈ s.exposed ∨ t ∈ s.challenged) ∧
      ((s.keyA t).isSome ∨ (s.keyB t).isSome) ∧
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

/-- Two challenge bits give the same query computation at epoch `t` from `s` whenever they
agree if `t` is eligible in `s`: not exposed, not already challenged, and keyed in one of the
game's tables. On an ineligible epoch both bits return `none` and leave `s` unchanged. -/
theorem oracleChall_run_eq_of_eligible_imp (b b' : Bool) (s : GameState StA StB I Rho) (t : ℕ)
    (h : ¬(t ∈ s.exposed ∨ t ∈ s.challenged) →
      ((s.keyA t).isSome = true ∨ (s.keyB t).isSome = true) → b = b') :
    (oracleChall b StA StB I Rho t).run s = (oracleChall b' StA StB I Rho t).run s := by
  by_cases hrej : t ∈ s.exposed ∨ t ∈ s.challenged
  · rw [oracleChall_rejected b s t hrej, oracleChall_rejected b' s t hrej]
  by_cases hkey : (s.keyA t).isSome = true ∨ (s.keyB t).isSome = true
  · rw [h hrej hkey]
  · have hA : s.keyA t = none := by cases hA : s.keyA t <;> simp_all
    have hB : s.keyB t = none := by cases hB : s.keyB t <;> simp_all
    rw [oracleChall_unavailable b s t hA hB, oracleChall_unavailable b' s t hA hB]

end Challenge

/-- The challenge oracle `oracleChall` preserves every predicate `Inv` on game states that is
insensitive to `challenged`: `Inv s → Inv { s with challenged := C }` for every `C`. -/
theorem oracleChall_preservesInv [SampleableType I] (b : Bool)
    (Inv : GameState StA StB I Rho → Prop)
    (hbook : ∀ s challenged, Inv s → Inv { s with challenged := challenged }) :
    QueryImpl.PreservesInv (oracleChall b StA StB I Rho) Inv := by
  intro t s hs z hz
  rcases oracleChall_support b s t z hz with ⟨h, _⟩ | ⟨_, _, h⟩
  · rw [h]; exact hs
  · rw [h]; exact hbook s _ hs

/-! ### Epoch-dependent challenge -/

section ChallengeOn

variable [SampleableType I]

/-- The challenge oracle whose eligible answers are random exactly at the epochs selected by
`random`: the query at epoch `t` is `oracleChall (random t)` at `t`, with the same guards and
bookkeeping. -/
def oracleChallOn (random : ℕ → Bool) (StA StB I Rho : Type) [SampleableType I] :
    QueryImpl (ℕ →ₒ Option I) (StateT (GameState StA StB I Rho) ProbComp) :=
  fun t => oracleChall (random t) StA StB I Rho t

@[simp]
lemma oracleChallOn_apply (random : ℕ → Bool) (t : ℕ) :
    oracleChallOn random StA StB I Rho t = oracleChall (random t) StA StB I Rho t := rfl

/-- A constant selection is the fixed-bit challenge oracle. -/
lemma oracleChallOn_const (b : Bool) :
    oracleChallOn (fun _ => b) StA StB I Rho = oracleChall b StA StB I Rho := rfl

/-- `oracleChallOn` preserves every predicate on game states that is insensitive to
`challenged`. -/
theorem oracleChallOn_preservesInv (random : ℕ → Bool)
    (Inv : GameState StA StB I Rho → Prop)
    (hbook : ∀ s challenged, Inv s → Inv { s with challenged := challenged }) :
    QueryImpl.PreservesInv (oracleChallOn random StA StB I Rho) Inv :=
  fun t => oracleChall_preservesInv (random t) Inv hbook t

end ChallengeOn

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

/-- Corrupting A either:

- returns `none` and leaves the game state unchanged; or
- returns `s.stA` and adds `vuln s.stA` to `exposed`, with none of these epochs challenged. -/
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

/-- Corrupting B either:

- returns `none` and leaves the game state unchanged; or
- returns `s.stB` and adds `vuln s.stB` to `exposed`, with none of these epochs challenged. -/
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

/-- Bookkeeping of A's leaking-send query from `s`: the challenged set is unchanged, and the
exposed set grows by a set disjoint from the challenged set (empty on rejection). -/
theorem oracleSendArleak_bookkeeping
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StA → Rand → Finset ℕ)
    (s : GameState StA StB I Rho)
    (z : Option (ℕ × Option ℕ × Rho × Rand) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleSendArleak leak scka ()).run s)) :
    z.2.challenged = s.challenged ∧
      ∃ E : Finset ℕ, E ∩ s.challenged = ∅ ∧ z.2.exposed = s.exposed ∪ E := by
  simp only [oracleSendArleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc] at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨out, -, hz⟩ := hz
  cases out with
  | none =>
      obtain rfl : z = (none, s) := by simpa using (mem_support_pure_iff _ _).mp hz
      exact ⟨rfl, ∅, by simp, by simp⟩
  | some out =>
      rcases out with ⟨key, msg, epoch, state, coins⟩
      dsimp only at hz
      split at hz
      · obtain rfl : z = (none, s) := by simpa using (mem_support_pure_iff _ _).mp hz
        exact ⟨rfl, ∅, by simp, by simp⟩
      · rename_i hvuln
        cases key <;>
          simp only [StateT.run_bind, StateT.run_set, pure_bind,
            StateT.run_pure, mem_support_pure_iff] at hz
        all_goals
          obtain rfl := hz
          exact ⟨rfl, leak s.stA coins, not_not.mp hvuln, rfl⟩

/-- The version of `oracleSendArleak_bookkeeping` for B. -/
theorem oracleSendBrleak_bookkeeping
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StB → Rand → Finset ℕ)
    (s : GameState StA StB I Rho)
    (z : Option (ℕ × Option ℕ × Rho × Rand) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleSendBrleak leak scka ()).run s)) :
    z.2.challenged = s.challenged ∧
      ∃ E : Finset ℕ, E ∩ s.challenged = ∅ ∧ z.2.exposed = s.exposed ∪ E := by
  simp only [oracleSendBrleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc] at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨out, -, hz⟩ := hz
  cases out with
  | none =>
      obtain rfl : z = (none, s) := by simpa using (mem_support_pure_iff _ _).mp hz
      exact ⟨rfl, ∅, by simp, by simp⟩
  | some out =>
      rcases out with ⟨key, msg, epoch, state, coins⟩
      dsimp only at hz
      split at hz
      · obtain rfl : z = (none, s) := by simpa using (mem_support_pure_iff _ _).mp hz
        exact ⟨rfl, ∅, by simp, by simp⟩
      · rename_i hvuln
        cases key <;>
          simp only [StateT.run_bind, StateT.run_set, pure_bind,
            StateT.run_pure, mem_support_pure_iff] at hz
        all_goals
          obtain rfl := hz
          exact ⟨rfl, leak s.stB coins, not_not.mp hvuln, rfl⟩
end LeakingSend

/-! ## Expected scores of leaking sends -/

section ExpectedScores

variable [DecidableEq I]

/-- Let `s` be a game state, `score` a function from game states to `ℝ≥0∞`, and `c : ℝ≥0∞`.
Assume:

- for every local state, discarding A's returned send coins recovers its ordinary send;
- every successful execution of A's leaking send from `s.stA` gives the same exposure set `E`;
- changing `exposed` does not change `score`;
- `score s ≤ c`;
- the expected score after A's ordinary-send query from `s` is at most `c`.

Then the expected score after A's leaking-send query from `s` is also at most `c`. -/
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

omit [DecidableEq I] in
/-- A challenge query does not raise any score that is insensitive to `challenged`. -/
theorem oracleChall_expectedPayoff_le [SampleableType I] (b : Bool) (t : ℕ)
    (s : GameState StA StB I Rho) (score : GameState StA StB I Rho → ℝ≥0∞)
    (hbook : ∀ state challenged, score { state with challenged := challenged } = score state) :
    expectedPayoff ((oracleChall b StA StB I Rho t).run s) (fun z => score z.2) ≤ score s := by
  refine expectedPayoff_le_const_of_support _ _ _ probFailure_eq_zero ?_
  intro z hz
  rcases oracleChall_support b s t z hz with ⟨h, -⟩ | ⟨-, -, h⟩
  · simp [h]
  · simp [h, hbook]

omit [DecidableEq I] in
/-- Corrupting A does not raise any score that is insensitive to `exposed`. -/
theorem oracleCorruptA_expectedPayoff_le (vuln : StA → Finset ℕ)
    (s : GameState StA StB I Rho) (score : GameState StA StB I Rho → ℝ≥0∞)
    (hbook : ∀ state exposed, score { state with exposed := exposed } = score state) :
    expectedPayoff ((oracleCorruptA vuln StB I Rho ()).run s) (fun z => score z.2) ≤
      score s := by
  refine expectedPayoff_le_const_of_support _ _ _ probFailure_eq_zero ?_
  intro z hz
  rcases oracleCorruptA_support vuln s z hz with h | ⟨-, h⟩
  · simp [h]
  · simp [h, hbook]

omit [DecidableEq I] in
/-- Corrupting B does not raise any score that is insensitive to `exposed`. -/
theorem oracleCorruptB_expectedPayoff_le (vuln : StB → Finset ℕ)
    (s : GameState StA StB I Rho) (score : GameState StA StB I Rho → ℝ≥0∞)
    (hbook : ∀ state exposed, score { state with exposed := exposed } = score state) :
    expectedPayoff ((oracleCorruptB vuln StA I Rho ()).run s) (fun z => score z.2) ≤
      score s := by
  refine expectedPayoff_le_const_of_support _ _ _ probFailure_eq_zero ?_
  intro z hz
  rcases oracleCorruptB_support vuln s z hz with h | ⟨-, h⟩
  · simp [h]
  · simp [h, hbook]

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

/-- `sckaSecurityImpl b` is `securityImplOf` over the correctness oracles and the fixed-bit
challenge oracle. -/
theorem sckaSecurityImpl_eq_securityImplOf [SampleableType I] (b : Bool)
    (vulnA : VulnerableEpochs StA Rand) (vulnB : VulnerableEpochs StB Rand)
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) :
    sckaSecurityImpl b vulnA vulnB scka =
      securityImplOf (sckaCorrectnessImpl scka) (oracleChall b StA StB I Rho) vulnA vulnB scka :=
  rfl

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
    -- `hz` says that `z = (answer, nextState)` can result from query `t` in state `s`.
    (hz : z ∈ support ((securityImplOf base chall vulnA vulnB scka t).run s)) :
    Inv z.2 := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · exact hbase t z hz
  · cases u; exact hA z hz
  · cases u; exact hB z hz
  · exact hC t z hz
  · cases u; exact hcA z hz
  · cases u; exact hcB z hz

/-- Let `Inv` be a predicate on game states and `s` a game state. Assume:

- `Inv s`;
- replacing `exposed` and `challenged` by any finite sets preserves `Inv`;
- for each party and local state, discarding the returned send coins recovers the ordinary send;
- every query of `base` or `chall`, and both ordinary-send queries, produces only states
  satisfying `Inv` when run from `s`.

Then every query of the full oracle family `securityImplOf` from `s` produces only states
satisfying `Inv`. -/
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
    (s : GameState StA StB I Rho) (hs : Inv s)
    (hbase : ∀ t z, z ∈ support ((base t).run s) → Inv z.2)
    (hchall : ∀ (t : ℕ) z, z ∈ support ((chall t).run s) → Inv z.2)
    (hsendA : ∀ z ∈ support ((oracleSendA scka ()).run s), Inv z.2)
    (hsendB : ∀ z ∈ support ((oracleSendB scka ()).run s), Inv z.2)
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain)
    (z : (sckaSecuritySpec StA StB I Rho Rand).Range t × GameState StA StB I Rho)
    (hz : z ∈ support ((securityImplOf base chall vulnA vulnB scka t).run s)) :
    Inv z.2 := by
  have hexp : ∀ s exposed, Inv s → Inv { s with exposed := exposed } :=
    fun s exposed h => by simpa using hbook s exposed s.challenged h
  refine securityImplOf_preserves_at base chall vulnA vulnB scka Inv s hbase
    (fun z hz => oracleSendArleak_preservesInv_at scka vulnA.rleak hmA Inv hexp s hs hsendA z hz)
    (fun z hz => oracleSendBrleak_preservesInv_at scka vulnB.rleak hmB Inv hexp s hs hsendB z hz)
    hchall
    (fun z hz => oracleCorruptA_preservesInv vulnA.corrupt Inv hexp () s hs z hz)
    (fun z hz => oracleCorruptB_preservesInv vulnB.corrupt Inv hexp () s hs z hz) t z hz

/-- The special case of `securityImplOf_preserves_at_of_book` for `sckaSecurityImpl`. Its
ordinary sends are correctness queries, so the two send hypotheses are instances of `hbase`. -/
theorem sckaSecurityImpl_preserves_at_of_book [SampleableType I] (b : Bool)
    (Inv : GameState StA StB I Rho → Prop)
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
    (s : GameState StA StB I Rho) (hs : Inv s)
    (hbase : ∀ t z, z ∈ support ((sckaCorrectnessImpl scka t).run s) → Inv z.2)
    (hchall : ∀ (t : ℕ) z, z ∈ support ((oracleChall b StA StB I Rho t).run s) → Inv z.2)
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain)
    (z : (sckaSecuritySpec StA StB I Rho Rand).Range t × GameState StA StB I Rho)
    (hz : z ∈ support ((sckaSecurityImpl b vulnA vulnB scka t).run s)) :
    Inv z.2 :=
  securityImplOf_preserves_at_of_book (sckaCorrectnessImpl scka) (oracleChall b StA StB I Rho)
    vulnA vulnB scka Inv hbook hmA hmB s hs hbase hchall
    (hbase sckaCorrectnessSpec.OSendA) (hbase sckaCorrectnessSpec.OSendB) t z hz

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


/-- Bookkeeping of one assembled security query from `s`. Assume that base queries from `s` keep
both `exposed` and `challenged`, and that challenge queries from `s` keep `exposed` and do not
shrink `challenged`. Then the query shrinks neither set, and every newly exposed epoch was not
challenged in `s`. -/
theorem securityImplOf_bookkeeping (s : GameState StA StB I Rho)
    (hbase : ∀ t z, z ∈ support ((base t).run s) →
      z.2.exposed = s.exposed ∧ z.2.challenged = s.challenged)
    (hchall : ∀ (t : ℕ) z, z ∈ support ((chall t).run s) →
      z.2.exposed = s.exposed ∧ s.challenged ⊆ z.2.challenged)
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain)
    (z : (sckaSecuritySpec StA StB I Rho Rand).Range t × GameState StA StB I Rho)
    (hz : z ∈ support ((securityImplOf base chall vulnA vulnB scka t).run s)) :
    s.exposed ⊆ z.2.exposed ∧ s.challenged ⊆ z.2.challenged ∧
      ∀ e ∈ z.2.exposed, e ∉ s.exposed → e ∉ s.challenged := by
  have hgrow : ∀ (E : Finset ℕ) (u : GameState StA StB I Rho), E ∩ s.challenged = ∅ →
      u.challenged = s.challenged → u.exposed = s.exposed ∪ E →
      s.exposed ⊆ u.exposed ∧ s.challenged ⊆ u.challenged ∧
        ∀ e ∈ u.exposed, e ∉ s.exposed → e ∉ s.challenged := by
    intro E u hE hc he
    refine ⟨by rw [he]; exact Finset.subset_union_left, by rw [hc], fun e he' hnot hchal => ?_⟩
    rw [he, Finset.mem_union] at he'
    have hmem : e ∈ E ∩ s.challenged := Finset.mem_inter.2 ⟨he'.resolve_left hnot, hchal⟩
    rw [hE] at hmem
    exact Finset.notMem_empty e hmem
  rcases t with (((((t | u) | u) | t) | u) | u)
  · obtain ⟨he, hc⟩ := hbase t z hz
    exact hgrow ∅ z.2 (by simp) hc (by rw [he, Finset.union_empty])
  · cases u
    obtain ⟨hc, E, hE, he⟩ := oracleSendArleak_bookkeeping scka vulnA.rleak s z hz
    exact hgrow E z.2 hE hc he
  · cases u
    obtain ⟨hc, E, hE, he⟩ := oracleSendBrleak_bookkeeping scka vulnB.rleak s z hz
    exact hgrow E z.2 hE hc he
  · obtain ⟨he, hc⟩ := hchall t z hz
    exact ⟨by rw [he], hc, fun e he' hnot => by rw [he] at he'; exact absurd he' hnot⟩
  · cases u
    rcases oracleCorruptA_support vulnA.corrupt s z hz with h | ⟨hE, h⟩
    · rw [h]; exact hgrow ∅ s (by simp) rfl (by simp)
    · rw [h]; exact hgrow _ _ hE rfl rfl
  · cases u
    rcases oracleCorruptB_support vulnB.corrupt s z hz with h | ⟨hE, h⟩
    · rw [h]; exact hgrow ∅ s (by simp) rfl (by simp)
    · rw [h]; exact hgrow _ _ hE rfl rfl

end SecurityFamily

end SCKAScheme
