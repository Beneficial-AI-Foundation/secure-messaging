/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Defs
import ToVCVio.OracleComp.SimSemantics.StateT.Stop
import ToVCVio.ProgramLogic.Unary.WP

/-!
# SCKA security oracles

Generic results on the security oracles of an SCKA scheme over `ProbComp`. A game state is

```text
s = (stA, stB, keyA, keyB, msgA, msgB, nA, nB, tcurA, tcurB,
     exposed, challenged, correct),
```

where `exposed` holds the epochs exposed by corruption or leakage and `challenged` the answered
challenges.

- **Individual oracles:** possible results of challenge, corruption, and leaking-send queries;
  challenge oracles that record challenges (`RecordsChallenges`).
- **Expected scores:** ordinary-send bounds extend to leaking sends.
- **Send distributions:** rejection and stopping of leaking sends with a fixed exposure set;
  equal local-send distributions give equal query distributions.
- **Full family** `securityImplOf base chall vulnA vulnB scka`: invariants, bookkeeping (no
  exposed or challenged epoch is removed; only sends increase `nA`, by at most one), and query
  equalities follow from those of the components.
-/

open OracleSpec OracleComp ENNReal
open OracleComp.ProgramLogic

namespace SCKAScheme

variable {IK StA StB I Rho Rand : Type}

/-! ## Individual security oracles -/

/-! ### Challenge -/

section Challenge

variable [SampleableType I]

/-- Challenge oracle answering query `t` as `oracleChall (mode t)`: an eligible challenge
gets an independent uniform key if `mode t` and the recorded key otherwise. -/
def challOf (mode : ℕ → Bool) :
    QueryImpl (ℕ →ₒ Option I) (StateT (GameState StA StB I Rho) ProbComp) :=
  fun t => oracleChall (mode t) StA StB I Rho t

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

/-- If `t` is exposed, challenged, or has no recorded key in `s`, every bit gives the same
challenge computation on `t` from `s`. -/
theorem oracleChall_run_eq_of_rejected (b b' : Bool) (s : GameState StA StB I Rho) (t : ℕ)
    (h : (t ∈ s.exposed ∨ t ∈ s.challenged) ∨ (s.keyA t = none ∧ s.keyB t = none)) :
    (oracleChall b StA StB I Rho t).run s = (oracleChall b' StA StB I Rho t).run s := by
  rcases h with h | ⟨hA, hB⟩
  · rw [oracleChall_rejected b s t h, oracleChall_rejected b' s t h]
  · rw [oracleChall_unavailable b s t hA hB, oracleChall_unavailable b' s t hA hB]

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

/-- An eligible challenge `t` puts `t` into `challenged` in every possible successor. -/
theorem oracleChall_adds_challenged (b : Bool) (s : GameState StA StB I Rho) (t : ℕ)
    (helig : ¬(t ∈ s.exposed ∨ t ∈ s.challenged))
    (hkey : (s.keyA t).isSome ∨ (s.keyB t).isSome)
    (z : Option I × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleChall b StA StB I Rho t).run s)) :
    t ∈ z.2.challenged := by
  rcases oracleChall_support b s t z hz with ⟨_, hrej | ⟨hA, hB⟩⟩ | ⟨_, _, h⟩
  · exact absurd hrej helig
  · simp [hA, hB] at hkey
  · rw [h]; exact Finset.mem_insert_self _ _

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

/-- Bookkeeping condition on a challenge oracle `chall`: every possible successor of a challenge
at epoch `t` from `s` is `s` itself, or, when `t ∉ s.exposed`, `s` with `t` added to
`challenged`. In particular, `chall` changes neither the party states nor the recorded keys. -/
def RecordsChallenges
    (chall : QueryImpl (ℕ →ₒ Option I) (StateT (GameState StA StB I Rho) ProbComp)) : Prop :=
  ∀ (t : ℕ) s z, z ∈ support ((chall t).run s) →
    z.2 = s ∨ (t ∉ s.exposed ∧ z.2 = { s with challenged := insert t s.challenged })

namespace RecordsChallenges

variable {chall : QueryImpl (ℕ →ₒ Option I) (StateT (GameState StA StB I Rho) ProbComp)}

/-- Preserves every `Inv` that is stable under changes to `challenged`. -/
theorem preservesInv (h : RecordsChallenges chall) (Inv : GameState StA StB I Rho → Prop)
    (hbook : ∀ s challenged, Inv s → Inv { s with challenged := challenged }) :
    QueryImpl.PreservesInv chall Inv := by
  intro t s hs z hz
  rcases h t s z hz with h | ⟨_, h⟩
  · rw [h]; exact hs
  · rw [h]; exact hbook s _ hs

/-- Preserves `Disjoint exposed challenged`. -/
theorem preserves_disjoint (h : RecordsChallenges chall) :
    QueryImpl.PreservesInv chall (fun s => Disjoint s.exposed s.challenged) := by
  intro t s hs z hz
  rcases h t s z hz with h | ⟨ht, h⟩
  · rw [h]; exact hs
  · rw [h]
    exact Finset.disjoint_insert_right.mpr ⟨ht, hs⟩

/-- Removes no challenged epoch. -/
theorem challenged_subset (h : RecordsChallenges chall) (t : ℕ) (s : GameState StA StB I Rho)
    (z : Option I × GameState StA StB I Rho) (hz : z ∈ support ((chall t).run s)) :
    s.challenged ⊆ z.2.challenged := by
  rcases h t s z hz with h | ⟨_, h⟩
  · rw [h]
  · rw [h]; exact Finset.subset_insert _ _

/-- Changes neither `exposed` nor `nA`. -/
theorem exposed_nA_eq (h : RecordsChallenges chall) (t : ℕ) (s : GameState StA StB I Rho)
    (z : Option I × GameState StA StB I Rho) (hz : z ∈ support ((chall t).run s)) :
    z.2.exposed = s.exposed ∧ z.2.nA = s.nA := by
  rcases h t s z hz with h | ⟨_, h⟩ <;> rw [h] <;> exact ⟨rfl, rfl⟩

end RecordsChallenges

/-- For every challenge mode, `challOf mode` records challenges. -/
theorem challOf_recordsChallenges [SampleableType I] (mode : ℕ → Bool) :
    RecordsChallenges (challOf (StA := StA) (StB := StB) (I := I) (Rho := Rho) mode) := by
  intro t s z hz
  rcases oracleChall_support (mode t) s t z hz with ⟨h, _⟩ | ⟨helig, _, h⟩
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

/-- The corruption of A preserves `Disjoint exposed challenged`. -/
theorem oracleCorruptA_preserves_disjoint (vuln : StA → Finset ℕ) :
    QueryImpl.PreservesInv (oracleCorruptA vuln StB I Rho)
      (fun s => Disjoint s.exposed s.challenged) := by
  intro _ s hs z hz
  rcases oracleCorruptA_support vuln s z hz with h | ⟨hv, h⟩
  · rw [h]; exact hs
  · rw [h]
    exact Finset.disjoint_union_left.mpr ⟨hs, Finset.disjoint_iff_inter_eq_empty.mpr hv⟩

/-- The corruption of A never removes an exposed epoch. -/
theorem oracleCorruptA_exposed_subset (vuln : StA → Finset ℕ) (u : Unit)
    (s : GameState StA StB I Rho) (z : Option StA × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleCorruptA vuln StB I Rho u).run s)) :
    s.exposed ⊆ z.2.exposed := by
  cases u
  rcases oracleCorruptA_support vuln s z hz with h | ⟨_, h⟩
  · rw [h]
  · rw [h]; exact Finset.subset_union_left

/-- The corruption of A changes neither the challenged set nor A's send counter. -/
theorem oracleCorruptA_challenged_nA_eq (vuln : StA → Finset ℕ) (u : Unit)
    (s : GameState StA StB I Rho) (z : Option StA × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleCorruptA vuln StB I Rho u).run s)) :
    z.2.challenged = s.challenged ∧ z.2.nA = s.nA := by
  cases u
  rcases oracleCorruptA_support vuln s z hz with h | ⟨_, h⟩ <;> rw [h] <;> exact ⟨rfl, rfl⟩

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

/-- B version of `oracleCorruptA_preserves_disjoint`. -/
theorem oracleCorruptB_preserves_disjoint (vuln : StB → Finset ℕ) :
    QueryImpl.PreservesInv (oracleCorruptB vuln StA I Rho)
      (fun s => Disjoint s.exposed s.challenged) := by
  intro _ s hs z hz
  rcases oracleCorruptB_support vuln s z hz with h | ⟨hv, h⟩
  · rw [h]; exact hs
  · rw [h]
    exact Finset.disjoint_union_left.mpr ⟨hs, Finset.disjoint_iff_inter_eq_empty.mpr hv⟩

/-- B version of `oracleCorruptA_exposed_subset`. -/
theorem oracleCorruptB_exposed_subset (vuln : StB → Finset ℕ) (u : Unit)
    (s : GameState StA StB I Rho) (z : Option StB × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleCorruptB vuln StA I Rho u).run s)) :
    s.exposed ⊆ z.2.exposed := by
  cases u
  rcases oracleCorruptB_support vuln s z hz with h | ⟨_, h⟩
  · rw [h]
  · rw [h]; exact Finset.subset_union_left

/-- B version of `oracleCorruptA_challenged_nA_eq`. -/
theorem oracleCorruptB_challenged_nA_eq (vuln : StB → Finset ℕ) (u : Unit)
    (s : GameState StA StB I Rho) (z : Option StB × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleCorruptB vuln StA I Rho u).run s)) :
    z.2.challenged = s.challenged ∧ z.2.nA = s.nA := by
  cases u
  rcases oracleCorruptB_support vuln s z hz with h | ⟨_, h⟩ <;> rw [h] <;> exact ⟨rfl, rfl⟩

/-! ### Leaking sends -/

section LeakingSend

variable [DecidableEq I]

/-- Every possible result of A's leaking send from `s` is `(none, s)`, or has a successor with
`exposed = s.exposed ∪ E` (`E ∩ s.challenged = ∅`), the same `challenged`, and `nA = s.nA + 1`. -/
theorem oracleSendArleak_support
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StA → Rand → Finset ℕ) (s : GameState StA StB I Rho)
    (z : Option (ℕ × Option ℕ × Rho × Rand) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleSendArleak leak scka ()).run s)) :
    z = (none, s) ∨
      ∃ E : Finset ℕ, E ∩ s.challenged = ∅ ∧ z.2.exposed = s.exposed ∪ E ∧
        z.2.challenged = s.challenged ∧ z.2.nA = s.nA + 1 := by
  simp only [oracleSendArleak, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
    monadLift_self, bind_assoc, pure_bind, mem_support_bind_iff] at hz
  obtain ⟨out, _, hz⟩ := hz
  cases out with
  | none => exact Or.inl (by simpa using (mem_support_pure_iff _ _).mp hz)
  | some out =>
    rcases out with ⟨key, msg, epoch, state, coins⟩
    dsimp only at hz
    split at hz
    · exact Or.inl (by simpa using (mem_support_pure_iff _ _).mp hz)
    · rename_i hguard
      refine Or.inr ⟨leak s.stA coins, not_not.mp hguard, ?_⟩
      cases key <;>
        simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
          mem_support_pure_iff] at hz
      all_goals obtain rfl := hz; exact ⟨rfl, rfl, rfl⟩

/-- A's leaking send preserves `Disjoint exposed challenged`. -/
theorem oracleSendArleak_preserves_disjoint
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StA → Rand → Finset ℕ) :
    QueryImpl.PreservesInv (oracleSendArleak leak scka)
      (fun s => Disjoint s.exposed s.challenged) := by
  intro u s hs z hz
  cases u
  rcases oracleSendArleak_support scka leak s z hz with h | ⟨E, hE, hex, hch, _⟩
  · rw [h]; exact hs
  · show Disjoint z.2.exposed z.2.challenged
    rw [hex, hch]
    exact Finset.disjoint_union_left.mpr ⟨hs, Finset.disjoint_iff_inter_eq_empty.mpr hE⟩

/-- A's leaking send never changes the challenged set. -/
theorem oracleSendArleak_challenged_eq
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StA → Rand → Finset ℕ)
    (u : Unit) (s : GameState StA StB I Rho)
    (z : Option (ℕ × Option ℕ × Rho × Rand) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleSendArleak leak scka u).run s)) :
    z.2.challenged = s.challenged := by
  cases u
  rcases oracleSendArleak_support scka leak s z hz with h | ⟨_, _, _, hch, _⟩
  · rw [h]
  · exact hch

/-- A's leaking send never removes an exposed epoch. -/
theorem oracleSendArleak_exposed_subset
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StA → Rand → Finset ℕ)
    (u : Unit) (s : GameState StA StB I Rho)
    (z : Option (ℕ × Option ℕ × Rho × Rand) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleSendArleak leak scka u).run s)) :
    s.exposed ⊆ z.2.exposed := by
  cases u
  rcases oracleSendArleak_support scka leak s z hz with h | ⟨E, _, hex, _, _⟩
  · rw [h]
  · rw [hex]; exact Finset.subset_union_left

/-- A's leaking send increases `nA` by at most one. -/
theorem oracleSendArleak_nA_le
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StA → Rand → Finset ℕ)
    (u : Unit) (s : GameState StA StB I Rho)
    (z : Option (ℕ × Option ℕ × Rho × Rand) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleSendArleak leak scka u).run s)) :
    z.2.nA ≤ s.nA + 1 := by
  cases u
  rcases oracleSendArleak_support scka leak s z hz with h | ⟨_, _, _, _, hn⟩
  · rw [h]; exact Nat.le_succ _
  · exact hn.le

/-- B version of `oracleSendArleak_support`, with `nA` unchanged. -/
theorem oracleSendBrleak_support
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StB → Rand → Finset ℕ) (s : GameState StA StB I Rho)
    (z : Option (ℕ × Option ℕ × Rho × Rand) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleSendBrleak leak scka ()).run s)) :
    z = (none, s) ∨
      ∃ E : Finset ℕ, E ∩ s.challenged = ∅ ∧ z.2.exposed = s.exposed ∪ E ∧
        z.2.challenged = s.challenged ∧ z.2.nA = s.nA := by
  simp only [oracleSendBrleak, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
    monadLift_self, bind_assoc, pure_bind, mem_support_bind_iff] at hz
  obtain ⟨out, _, hz⟩ := hz
  cases out with
  | none => exact Or.inl (by simpa using (mem_support_pure_iff _ _).mp hz)
  | some out =>
    rcases out with ⟨key, msg, epoch, state, coins⟩
    dsimp only at hz
    split at hz
    · exact Or.inl (by simpa using (mem_support_pure_iff _ _).mp hz)
    · rename_i hguard
      refine Or.inr ⟨leak s.stB coins, not_not.mp hguard, ?_⟩
      cases key <;>
        simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
          mem_support_pure_iff] at hz
      all_goals obtain rfl := hz; exact ⟨rfl, rfl, rfl⟩

/-- B version of `oracleSendArleak_preserves_disjoint`. -/
theorem oracleSendBrleak_preserves_disjoint
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StB → Rand → Finset ℕ) :
    QueryImpl.PreservesInv (oracleSendBrleak leak scka)
      (fun s => Disjoint s.exposed s.challenged) := by
  intro u s hs z hz
  cases u
  rcases oracleSendBrleak_support scka leak s z hz with h | ⟨E, hE, hex, hch, _⟩
  · rw [h]; exact hs
  · show Disjoint z.2.exposed z.2.challenged
    rw [hex, hch]
    exact Finset.disjoint_union_left.mpr ⟨hs, Finset.disjoint_iff_inter_eq_empty.mpr hE⟩

/-- B version of `oracleSendArleak_challenged_eq`. -/
theorem oracleSendBrleak_challenged_eq
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StB → Rand → Finset ℕ)
    (u : Unit) (s : GameState StA StB I Rho)
    (z : Option (ℕ × Option ℕ × Rho × Rand) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleSendBrleak leak scka u).run s)) :
    z.2.challenged = s.challenged := by
  cases u
  rcases oracleSendBrleak_support scka leak s z hz with h | ⟨_, _, _, hch, _⟩
  · rw [h]
  · exact hch

/-- B version of `oracleSendArleak_exposed_subset`. -/
theorem oracleSendBrleak_exposed_subset
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StB → Rand → Finset ℕ)
    (u : Unit) (s : GameState StA StB I Rho)
    (z : Option (ℕ × Option ℕ × Rho × Rand) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleSendBrleak leak scka u).run s)) :
    s.exposed ⊆ z.2.exposed := by
  cases u
  rcases oracleSendBrleak_support scka leak s z hz with h | ⟨E, _, hex, _, _⟩
  · rw [h]
  · rw [hex]; exact Finset.subset_union_left

/-- B's leaking send preserves A's send counter. -/
theorem oracleSendBrleak_nA_eq
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StB → Rand → Finset ℕ)
    (u : Unit) (s : GameState StA StB I Rho)
    (z : Option (ℕ × Option ℕ × Rho × Rand) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleSendBrleak leak scka u).run s)) :
    z.2.nA = s.nA := by
  cases u
  rcases oracleSendBrleak_support scka leak s z hz with h | ⟨_, _, _, _, hn⟩
  · rw [h]
  · exact hn

/-- Assume that discarding the coins returned by A's leaking send recovers its ordinary send for
every local state, and that `Inv` holds at `s` and does not depend on `exposed`. If every
ordinary-send successor from `s` satisfies `Inv`, then so does every leaking-send successor. -/
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

/-- Let `s` be a game state, `score` a function from game states to `ℝ≥0∞`, and `c : ℝ≥0∞`.
Assume:

- for every local state, discarding A's returned send coins recovers its ordinary send;
- every successful execution of A's leaking send from `s.stA` gives the same exposure set `E`;
- changing `exposed` does not change `score`;
- `score s ≤ c`;
- the expected score after A's ordinary-send query from `s` is at most `c`.

Then the expected score after A's leaking-send query from `s` is also at most `c`. -/
theorem oracleSendArleak_wp_le
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
    (hplain : wp ((oracleSendA scka ()).run s) (fun z => score z.2) ≤ c) :
    wp ((oracleSendArleak leak scka ()).run s) (fun z => score z.2) ≤ c := by
  by_cases hguard : E ∩ s.challenged ≠ ∅
  · apply wp_le_const_of_support _
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
  · suffices heq : wp ((oracleSendArleak leak scka ()).run s)
        (fun z => score z.2) =
        wp ((oracleSendA scka ()).run s) (fun z => score z.2) by
      exact heq ▸ hplain
    simp only [oracleSendArleak, oracleSendA, StateT.run_bind, StateT.run_get,
      pure_bind, StateT.run_monadLift, monadLift_self, bind_assoc]
    rw [← hm s.stA]
    simp only [bind_assoc, pure_bind, wp_bind_eq_tsum]
    apply tsum_congr
    intro out
    by_cases hout : out ∈ support (scka.sendArleak s.stA)
    · cases out with
      | none => simp only [StateT.run_pure, ExactWPMonad.wp_pure, Option.map_none]
      | some out =>
        rcases out with ⟨key, msg, epoch, state, coins⟩
        simp only [hE key msg epoch state coins hout, hguard, ↓reduceIte]
        cases key <;> simp only [Option.map_some, StateT.run_bind, StateT.run_set,
          pure_bind, StateT.run_pure, wp_pure]
        all_goals
          congr 1
          conv_rhs => rw [← hbook _ (s.exposed ∪ E)]
    · have hz : Pr{let x ← scka.sendArleak s.stA}[x = out] = 0 := by
        exact (prEvent_eq_zero_of_not_mem_support _) hout
      simp only [hz, zero_mul]

/-- The expected-score bound of `oracleSendArleak_wp_le` for B. -/
theorem oracleSendBrleak_wp_le
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
    (hplain : wp ((oracleSendB scka ()).run s) (fun z => score z.2) ≤ c) :
    wp ((oracleSendBrleak leak scka ()).run s) (fun z => score z.2) ≤ c := by
  by_cases hguard : E ∩ s.challenged ≠ ∅
  · apply wp_le_const_of_support _
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
  · suffices heq : wp ((oracleSendBrleak leak scka ()).run s)
        (fun z => score z.2) =
        wp ((oracleSendB scka ()).run s) (fun z => score z.2) by
      exact heq ▸ hplain
    simp only [oracleSendBrleak, oracleSendB, StateT.run_bind, StateT.run_get,
      pure_bind, StateT.run_monadLift, monadLift_self, bind_assoc]
    rw [← hm s.stB]
    simp only [bind_assoc, pure_bind, wp_bind_eq_tsum]
    apply tsum_congr
    intro out
    by_cases hout : out ∈ support (scka.sendBrleak s.stB)
    · cases out with
      | none => simp only [StateT.run_pure, ExactWPMonad.wp_pure, Option.map_none]
      | some out =>
        rcases out with ⟨key, msg, epoch, state, coins⟩
        simp only [hE key msg epoch state coins hout, hguard, ↓reduceIte]
        cases key <;> simp only [Option.map_some, StateT.run_bind, StateT.run_set,
          pure_bind, StateT.run_pure, wp_pure]
        all_goals
          congr 1
          conv_rhs => rw [← hbook _ (s.exposed ∪ E)]
    · have hz : Pr{let x ← scka.sendBrleak s.stB}[x = out] = 0 := by
        exact (prEvent_eq_zero_of_not_mem_support _) hout
      simp only [hz, zero_mul]

end ExpectedScores

/-! ## Send distributions under exposure guards -/

section SendDistributions

variable [DecidableEq I] {τ : Type}

/-- If `E ∩ s.challenged ≠ ∅` and `leak s.stA r = E` for the coins `r` of every possible
successful local leaking A-send, A's leaking-send query from `s` is `(none, s)` with probability
one. -/
theorem oracleSendArleak_rejected_evalDistEq
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StA → Rand → Finset ℕ)
    (s : GameState StA StB I Rho) (E : Finset ℕ)
    (hE : ∀ key msg epoch next coins,
      some (key, msg, epoch, next, coins) ∈ support (scka.sendArleak s.stA) →
      leak s.stA coins = E)
    (hguard : E ∩ s.challenged ≠ ∅) :
    (oracleSendArleak leak scka ()).run s =ᵈ (pure (none, s) : ProbComp _) := by
  simp only [oracleSendArleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc]
  refine ToVCVio.evalDistEq_bind_of_const' _ fun out hout => ?_
  cases out with
  | none => rfl
  | some out =>
    rcases out with ⟨key, msg, epoch, next, coins⟩
    dsimp only
    rw [hE key msg epoch next coins hout, ite_eq_left hguard]
    rfl

/-- If every local leaking A-send from `s.stA` succeeds with coins `r` such that
`leak s.stA r = E`, `E ∩ s.challenged = ∅`, and `e ∈ E`, then the query from `s`, stopped at
`e ∈ exposed`, answers `none` on every possible result. -/
theorem oracleSendArleak_stop_of_exposure
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StA → Rand → Finset ℕ)
    (s : GameState StA StB I Rho) (E : Finset ℕ) (e : ℕ)
    (hsuccess : none ∉ support (scka.sendArleak s.stA))
    (hE : ∀ key msg epoch next coins,
      some (key, msg, epoch, next, coins) ∈ support (scka.sendArleak s.stA) →
      leak s.stA coins = E)
    (hguard : E ∩ s.challenged = ∅) (he : e ∈ E)
    (z : Option (Option (ℕ × Option ℕ × Rho × Rand)) × GameState StA StB I Rho)
    (hz : z ∈ support (((stopOnState (oracleSendArleak leak scka)
      (fun s => decide (e ∈ s.exposed)) ()).run).run s)) :
    z.1 = none := by
  change z ∈ support (do
    let out ← (oracleSendArleak leak scka ()).run s
    pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2)) at hz
  simp only [oracleSendArleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc, mem_support_bind_iff] at hz
  obtain ⟨out, hout, hz⟩ := hz
  cases out with
  | none => exact False.elim (hsuccess hout)
  | some out =>
    rcases out with ⟨key, msg, epoch, next, coins⟩
    simp only [hE key msg epoch next coins hout, hguard, ne_eq, not_true_eq_false,
      ↓reduceIte] at hz
    cases key <;>
      simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
        mem_support_pure_iff, exists_eq_left, Finset.mem_union, he, or_true,
        decide_true, ↓reduceIte] at hz
    all_goals obtain rfl := hz; rfl

/-- B version of `oracleSendArleak_rejected_evalDistEq`. -/
theorem oracleSendBrleak_rejected_evalDistEq
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StB → Rand → Finset ℕ)
    (s : GameState StA StB I Rho) (E : Finset ℕ)
    (hE : ∀ key msg epoch next coins,
      some (key, msg, epoch, next, coins) ∈ support (scka.sendBrleak s.stB) →
      leak s.stB coins = E)
    (hguard : E ∩ s.challenged ≠ ∅) :
    (oracleSendBrleak leak scka ()).run s =ᵈ (pure (none, s) : ProbComp _) := by
  simp only [oracleSendBrleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc]
  refine ToVCVio.evalDistEq_bind_of_const' _ fun out hout => ?_
  cases out with
  | none => rfl
  | some out =>
    rcases out with ⟨key, msg, epoch, next, coins⟩
    dsimp only
    rw [hE key msg epoch next coins hout, ite_eq_left hguard]
    rfl

/-- B version of `oracleSendArleak_stop_of_exposure`. -/
theorem oracleSendBrleak_stop_of_exposure
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StB → Rand → Finset ℕ)
    (s : GameState StA StB I Rho) (E : Finset ℕ) (e : ℕ)
    (hsuccess : none ∉ support (scka.sendBrleak s.stB))
    (hE : ∀ key msg epoch next coins,
      some (key, msg, epoch, next, coins) ∈ support (scka.sendBrleak s.stB) →
      leak s.stB coins = E)
    (hguard : E ∩ s.challenged = ∅) (he : e ∈ E)
    (z : Option (Option (ℕ × Option ℕ × Rho × Rand)) × GameState StA StB I Rho)
    (hz : z ∈ support (((stopOnState (oracleSendBrleak leak scka)
      (fun s => decide (e ∈ s.exposed)) ()).run).run s)) :
    z.1 = none := by
  change z ∈ support (do
    let out ← (oracleSendBrleak leak scka ()).run s
    pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2)) at hz
  simp only [oracleSendBrleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc, mem_support_bind_iff] at hz
  obtain ⟨out, hout, hz⟩ := hz
  cases out with
  | none => exact False.elim (hsuccess hout)
  | some out =>
    rcases out with ⟨key, msg, epoch, next, coins⟩
    simp only [hE key msg epoch next coins hout, hguard, ne_eq, not_true_eq_false,
      ↓reduceIte] at hz
    cases key <;>
      simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
        mem_support_pure_iff, exists_eq_left, Finset.mem_union, he, or_true,
        decide_true, ↓reduceIte] at hz
    all_goals obtain rfl := hz; rfl

/-- If `(a ← sample; (family a).sendA s.stA) =ᵈ target.sendA s.stA`, the A-send queries
from `s` satisfy the same equality of joint response/state distributions. -/
theorem oracleSendA_sample_eq
    (sample : ProbComp τ) (family : τ → SCKAScheme ProbComp IK StA StB I Rho Rand)
    (target : SCKAScheme ProbComp IK StA StB I Rho Rand) (s : GameState StA StB I Rho)
    (h : (do let a ← sample; (family a).sendA s.stA) =ᵈ target.sendA s.stA) :
    (do let a ← sample; (oracleSendA (family a) ()).run s) =ᵈ
      (oracleSendA target ()).run s := by
  simp only [oracleSendA, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc]
  rw [← bind_assoc]
  exact h.bind_left _

/-- B version of `oracleSendA_sample_eq`. -/
theorem oracleSendB_sample_eq
    (sample : ProbComp τ) (family : τ → SCKAScheme ProbComp IK StA StB I Rho Rand)
    (target : SCKAScheme ProbComp IK StA StB I Rho Rand) (s : GameState StA StB I Rho)
    (h : (do let a ← sample; (family a).sendB s.stB) =ᵈ target.sendB s.stB) :
    (do let a ← sample; (oracleSendB (family a) ()).run s) =ᵈ
      (oracleSendB target ()).run s := by
  simp only [oracleSendB, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc]
  rw [← bind_assoc]
  exact h.bind_left _

/-- Leaking-send version of `oracleSendA_sample_eq`, for a common exposure function `leak`. -/
theorem oracleSendArleak_sample_eq
    (sample : ProbComp τ) (family : τ → SCKAScheme ProbComp IK StA StB I Rho Rand)
    (target : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StA → Rand → Finset ℕ) (s : GameState StA StB I Rho)
    (h : (do let a ← sample; (family a).sendArleak s.stA) =ᵈ
      target.sendArleak s.stA) :
    (do let a ← sample; (oracleSendArleak leak (family a) ()).run s) =ᵈ
      (oracleSendArleak leak target ()).run s := by
  simp only [oracleSendArleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc]
  rw [← bind_assoc]
  exact h.bind_left _

/-- B version of `oracleSendArleak_sample_eq`. -/
theorem oracleSendBrleak_sample_eq
    (sample : ProbComp τ) (family : τ → SCKAScheme ProbComp IK StA StB I Rho Rand)
    (target : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StB → Rand → Finset ℕ) (s : GameState StA StB I Rho)
    (h : (do let a ← sample; (family a).sendBrleak s.stB) =ᵈ
      target.sendBrleak s.stB) :
    (do let a ← sample; (oracleSendBrleak leak (family a) ()).run s) =ᵈ
      (oracleSendBrleak leak target ()).run s := by
  simp only [oracleSendBrleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc]
  rw [← bind_assoc]
  exact h.bind_left _

/-- Equal local A-sends from `s.stA` give equal A-send queries from `s`. -/
theorem oracleSendA_run_congr
    (scka scka' : SCKAScheme ProbComp IK StA StB I Rho Rand) (s : GameState StA StB I Rho)
    (h : scka.sendA s.stA = scka'.sendA s.stA) :
    (oracleSendA scka ()).run s = (oracleSendA scka' ()).run s := by
  simp only [oracleSendA, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_monadLift,
    monadLift_self, bind_assoc]
  rw [h]

/-- B version of `oracleSendA_run_congr`. -/
theorem oracleSendB_run_congr
    (scka scka' : SCKAScheme ProbComp IK StA StB I Rho Rand) (s : GameState StA StB I Rho)
    (h : scka.sendB s.stB = scka'.sendB s.stB) :
    (oracleSendB scka ()).run s = (oracleSendB scka' ()).run s := by
  simp only [oracleSendB, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_monadLift,
    monadLift_self, bind_assoc]
  rw [h]

/-- Leaking-send version of `oracleSendA_run_congr`, for a common exposure function `leak`. -/
theorem oracleSendArleak_run_congr
    (leak : StA → Rand → Finset ℕ)
    (scka scka' : SCKAScheme ProbComp IK StA StB I Rho Rand) (s : GameState StA StB I Rho)
    (h : scka.sendArleak s.stA = scka'.sendArleak s.stA) :
    (oracleSendArleak leak scka ()).run s = (oracleSendArleak leak scka' ()).run s := by
  simp only [oracleSendArleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc]
  rw [h]

/-- B version of `oracleSendArleak_run_congr`. -/
theorem oracleSendBrleak_run_congr
    (leak : StB → Rand → Finset ℕ)
    (scka scka' : SCKAScheme ProbComp IK StA StB I Rho Rand) (s : GameState StA StB I Rho)
    (h : scka.sendBrleak s.stB = scka'.sendBrleak s.stB) :
    (oracleSendBrleak leak scka ()).run s = (oracleSendBrleak leak scka' ()).run s := by
  simp only [oracleSendBrleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc]
  rw [h]

/-- If two schemes' A-receives agree on `s.stA`, their A-receive queries from `s` agree. -/
theorem oracleRecvA_run_congr
    (scka scka' : SCKAScheme ProbComp IK StA StB I Rho Rand) (s : GameState StA StB I Rho)
    (h : ∀ ρ, scka.recvA s.stA ρ = scka'.recvA s.stA ρ) (n : ℕ) :
    (oracleRecvA scka n).run s = (oracleRecvA scka' n).run s := by
  simp only [oracleRecvA, StateT.run_bind, StateT.run_get, pure_bind]
  cases hm : s.msgB n with
  | none => rfl
  | some entry =>
    rcases entry with ⟨ρ, tsnd⟩
    simp only
    rw [h ρ]

/-- B version of `oracleRecvA_run_congr`. -/
theorem oracleRecvB_run_congr
    (scka scka' : SCKAScheme ProbComp IK StA StB I Rho Rand) (s : GameState StA StB I Rho)
    (h : ∀ ρ, scka.recvB s.stB ρ = scka'.recvB s.stB ρ) (n : ℕ) :
    (oracleRecvB scka n).run s = (oracleRecvB scka' n).run s := by
  simp only [oracleRecvB, StateT.run_bind, StateT.run_get, pure_bind]
  cases hm : s.msgA n with
  | none => rfl
  | some entry =>
    rcases entry with ⟨ρ, tsnd⟩
    simp only
    rw [h ρ]

end SendDistributions

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

/-- If every component preserves `Inv`, so does `securityImplOf base chall vulnA vulnB scka`. -/
theorem securityImplOf_preservesInv (Inv : GameState StA StB I Rho → Prop)
    (hbase : QueryImpl.PreservesInv base Inv)
    (hA : QueryImpl.PreservesInv (oracleSendArleak vulnA.rleak scka) Inv)
    (hB : QueryImpl.PreservesInv (oracleSendBrleak vulnB.rleak scka) Inv)
    (hC : QueryImpl.PreservesInv chall Inv)
    (hcA : QueryImpl.PreservesInv (oracleCorruptA vulnA.corrupt StB I Rho) Inv)
    (hcB : QueryImpl.PreservesInv (oracleCorruptB vulnB.corrupt StA I Rho) Inv) :
    QueryImpl.PreservesInv (securityImplOf base chall vulnA vulnB scka) Inv :=
  fun t s hs z hz => securityImplOf_preserves_at base chall vulnA vulnB scka Inv s
    (fun t => hbase t s hs) (hA () s hs) (hB () s hs) (fun t => hC t s hs)
    (hcA () s hs) (hcB () s hs) t z hz

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

/-- If dropping the coins of each leaking send gives the ordinary send and `chall` records
challenges, the family preserves every `Inv` preserved by `base`, both ordinary sends, and
arbitrary changes to `exposed` and `challenged`. -/
theorem securityImplOf_preservesInv_of_book (Inv : GameState StA StB I Rho → Prop)
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
    (hbase : QueryImpl.PreservesInv base Inv)
    (hsendA : QueryImpl.PreservesInv (oracleSendA scka) Inv)
    (hsendB : QueryImpl.PreservesInv (oracleSendB scka) Inv) :
    QueryImpl.PreservesInv (securityImplOf base chall vulnA vulnB scka) Inv :=
  fun t s hs z hz => securityImplOf_preserves_at_of_book base chall vulnA vulnB scka Inv
    hbook hmA hmB s hs (fun t => hbase t s hs)
    (fun t => hchall.preservesInv Inv (fun s C h => by simpa using hbook s s.exposed C h) t s hs)
    (hsendA () s hs) (hsendB () s hs) t z hz

/-- If `base` keeps `exposed` and `chall` records challenges, every possible successor `s'` of
a family query from `s` has `s.exposed ⊆ s'.exposed`. -/
theorem securityImplOf_exposed_subset
    (hbase : ∀ t s z, z ∈ support ((base t).run s) → z.2.exposed = s.exposed)
    (hchall : RecordsChallenges chall)
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain) (s : GameState StA StB I Rho)
    (z : (sckaSecuritySpec StA StB I Rho Rand).Range t × GameState StA StB I Rho)
    (hz : z ∈ support ((securityImplOf base chall vulnA vulnB scka t).run s)) :
    s.exposed ⊆ z.2.exposed := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rw [hbase t s z hz]
  · exact oracleSendArleak_exposed_subset scka vulnA.rleak u s z hz
  · exact oracleSendBrleak_exposed_subset scka vulnB.rleak u s z hz
  · rw [(hchall.exposed_nA_eq t s z hz).1]
  · exact oracleCorruptA_exposed_subset vulnA.corrupt u s z hz
  · exact oracleCorruptB_exposed_subset vulnB.corrupt u s z hz

/-- `challenged` version of `securityImplOf_exposed_subset`. -/
theorem securityImplOf_challenged_subset
    (hbase : ∀ t s z, z ∈ support ((base t).run s) → z.2.challenged = s.challenged)
    (hchall : RecordsChallenges chall)
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain) (s : GameState StA StB I Rho)
    (z : (sckaSecuritySpec StA StB I Rho Rand).Range t × GameState StA StB I Rho)
    (hz : z ∈ support ((securityImplOf base chall vulnA vulnB scka t).run s)) :
    s.challenged ⊆ z.2.challenged := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rw [hbase t s z hz]
  · rw [oracleSendArleak_challenged_eq scka vulnA.rleak u s z hz]
  · rw [oracleSendBrleak_challenged_eq scka vulnB.rleak u s z hz]
  · exact hchall.challenged_subset t s z hz
  · rw [(oracleCorruptA_challenged_nA_eq vulnA.corrupt u s z hz).1]
  · rw [(oracleCorruptB_challenged_nA_eq vulnB.corrupt u s z hz).1]

/-- If `base` keeps both bookkeeping sets and `chall` records challenges, the assembled
oracles preserve `Disjoint exposed challenged`. -/
theorem securityImplOf_preserves_disjoint
    (hbase : ∀ t s z, z ∈ support ((base t).run s) →
      z.2.exposed = s.exposed ∧ z.2.challenged = s.challenged)
    (hchall : RecordsChallenges chall) :
    QueryImpl.PreservesInv (securityImplOf base chall vulnA vulnB scka)
      (fun s => Disjoint s.exposed s.challenged) := by
  refine securityImplOf_preservesInv base chall vulnA vulnB scka _ ?_
    (oracleSendArleak_preserves_disjoint scka vulnA.rleak)
    (oracleSendBrleak_preserves_disjoint scka vulnB.rleak)
    hchall.preserves_disjoint
    (oracleCorruptA_preserves_disjoint vulnA.corrupt)
    (oracleCorruptB_preserves_disjoint vulnB.corrupt)
  intro t s hs z hz
  obtain ⟨he, hc⟩ := hbase t s z hz
  show Disjoint z.2.exposed z.2.challenged
  rw [he, hc]; exact hs

/-- If `base` increases `nA` by at most one on sends and not otherwise, and `chall` records
challenges, every possible successor `s'` of a family query `t` from `s` has
`s'.nA ≤ s.nA + (if t is a send then 1 else 0)`. -/
theorem securityImplOf_nA_step
    (hbase : ∀ t s z, z ∈ support ((base t).run s) →
      z.2.nA ≤ s.nA + if isSendQuery t then 1 else 0)
    (hchall : RecordsChallenges chall)
    (t : (sckaSecuritySpec StA StB I Rho Rand).Domain) (s : GameState StA StB I Rho)
    (z : (sckaSecuritySpec StA StB I Rho Rand).Range t × GameState StA StB I Rho)
    (hz : z ∈ support ((securityImplOf base chall vulnA vulnB scka t).run s)) :
    z.2.nA ≤ s.nA + if sckaSecuritySpec.isSendQuery t then 1 else 0 := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rw [sckaSecuritySpec.isSendQuery_OCorrectness]
    exact hbase t s z hz
  · cases u
    simpa [sckaSecuritySpec.isSendQuery] using oracleSendArleak_nA_le scka vulnA.rleak () s z hz
  · cases u
    simpa [sckaSecuritySpec.isSendQuery] using
      (oracleSendBrleak_nA_eq scka vulnB.rleak () s z hz).le.trans (Nat.le_succ _)
  · simpa [sckaSecuritySpec.isSendQuery] using (hchall.exposed_nA_eq t s z hz).2.le
  · cases u
    simpa [sckaSecuritySpec.isSendQuery] using
      (oracleCorruptA_challenged_nA_eq vulnA.corrupt () s z hz).2.le
  · cases u
    simpa [sckaSecuritySpec.isSendQuery] using
      (oracleCorruptB_challenged_nA_eq vulnB.corrupt () s z hz).2.le

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
