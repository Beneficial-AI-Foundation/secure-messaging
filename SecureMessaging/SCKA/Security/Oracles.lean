/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Defs

/-!
# Supports and invariants of the security oracles

Let `scka : SCKAScheme ProbComp IK StA StB I Rho Rand` be a scheme and
`s : GameState StA StB I Rho` be a game state. These lemmas describe the responses and state
updates of challenge, corruption, and leaking-send queries from `s`. Rejected queries retain
`s`; accepted challenges insert their epoch into `challenged`, and accepted corruptions and
leaking sends add their vulnerable epochs to `exposed`.

A challenge oracle `chall` satisfies `RecordsChallenges` when each supported successor of a
query `t` from a state `s` is `s`, or differs only by inserting `t` into `s.challenged` with
`t ∉ s.exposed`. The oracle `oracleChall b` satisfies this for either challenge bit `b`.

If discarding returned coins recovers an ordinary-send computation, invariants of that send
also hold for its leaking-send oracle, provided arbitrary changes to `exposed` preserve them.
-/

open OracleSpec OracleComp

namespace SCKAScheme

variable {IK StA StB I Rho Rand : Type}

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

end SCKAScheme
