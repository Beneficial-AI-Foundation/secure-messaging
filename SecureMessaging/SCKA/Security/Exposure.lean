/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Defs

/-!
# Challenge and corruption guards

**Rejection.** For every state `s`, epoch `t`, and bit `b`, the challenge
oracle returns `(none, s)` if `t ∈ s.exposed ∪ s.challenged`, or if both
key tables have entry `none` at `t`. Eligible challenges use `b` to select
a recorded key or a uniform key.

**Preservation.** Every challenge and corruption query preserves
`Disjoint exposed challenged`. More generally, challenges preserve any
invariant stable under updates to `challenged`; corruptions preserve any
invariant stable under updates to `exposed`.

**Proof.** Inspect each guard and supported response. Accepted queries update
the relevant set; rejected queries retain the state. These facts extend
protocol-state invariants to the security interface and supply the challenge
rejection used by `HybridExposure`.
-/

open OracleSpec OracleComp

namespace SCKAScheme

variable {StA StB I Rho : Type} [SampleableType I]

/-- Challenging an exposed or previously challenged epoch returns `none`
and preserves the state, in both fixed-bit experiments. -/
theorem oracleChall_rejected (b : Bool) (s : GameState StA StB I Rho) (t : ℕ)
    (h : t ∈ s.exposed ∨ t ∈ s.challenged) :
    (oracleChall b StA StB I Rho t).run s = pure (none, s) := by
  simp [oracleChall, h]

/-- A challenge whose two key-table entries are `none` returns `none` and retains the
state, regardless of the exposure sets and hidden bit. -/
theorem oracleChall_unavailable (b : Bool) (s : GameState StA StB I Rho) (t : ℕ)
    (hA : s.keyA t = none) (hB : s.keyB t = none) :
    (oracleChall b StA StB I Rho t).run s = pure (none, s) := by
  by_cases h : t ∈ s.exposed ∨ t ∈ s.challenged
  · exact oracleChall_rejected b s t h
  · simp [oracleChall, h, hA, hB]

/-- Once an epoch is exposed, both fixed-bit challenge oracles have the
same answer and state transition at that epoch. -/
theorem oracleChall_eq_of_exposed (s : GameState StA StB I Rho) (t : ℕ)
    (h : t ∈ s.exposed) :
    (oracleChall true StA StB I Rho t).run s =
      (oracleChall false StA StB I Rho t).run s := by
  rw [oracleChall_rejected true s t (Or.inl h),
    oracleChall_rejected false s t (Or.inl h)]

/-- A challenge preserves disjointness of exposed and challenged epochs.
This holds even when the query is repeated, unavailable, or already exposed. -/
theorem oracleChall_preserves_disjoint (b : Bool) :
    QueryImpl.PreservesInv (oracleChall b StA StB I Rho)
      (fun s => Disjoint s.exposed s.challenged) := by
  intro t s hs z hz
  by_cases h : t ∈ s.exposed ∨ t ∈ s.challenged
  · rw [oracleChall_rejected b s t h] at hz
    simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
  · have hins : Disjoint s.exposed (insert t s.challenged) := by
      simp only [Finset.disjoint_insert_right]
      exact ⟨fun ht => h (Or.inl ht), hs⟩
    cases hA : s.keyA t <;> cases hB : s.keyB t <;> cases b <;>
      simp only [oracleChall, Bool.false_eq_true, ↓reduceIte, bind_pure_comp,
        pure_bind, StateT.run_bind, StateT.run_get, h, hA, hB, StateT.run_pure,
        StateT.run_map, StateT.run_set, StateT.run_monadLift, monadLift_self,
        map_pure, Functor.map_map, support_pure, Set.mem_singleton_iff,
        support_map, support_uniformSample, Set.image_univ, Set.mem_range] at hz
    all_goals
      first
      | obtain rfl := hz
      | obtain ⟨k, rfl⟩ := hz
    all_goals assumption

omit [SampleableType I] in
/-- Corrupting A preserves disjointness: a conflicting corruption is
rejected; an accepted corruption adds only unchallenged vulnerable epochs. -/
theorem oracleCorruptA_preserves_disjoint (vuln : StA → Finset ℕ) :
    QueryImpl.PreservesInv (oracleCorruptA vuln StB I Rho)
      (fun s => Disjoint s.exposed s.challenged) := by
  intro _ s hs z hz
  by_cases h : vuln s.stA ∩ s.challenged ≠ ∅
  · have hz' : z = (none, s) := by simpa [oracleCorruptA, h] using hz
    obtain rfl := hz'
    exact hs
  · have heq := not_not.mp h
    have hz' : z = (some s.stA, { s with exposed := s.exposed ∪ vuln s.stA }) := by
      simpa [oracleCorruptA, heq] using hz
    obtain rfl := hz'
    exact Finset.disjoint_union_left.mpr
      ⟨hs, Finset.disjoint_iff_inter_eq_empty.mpr (not_not.mp h)⟩

omit [SampleableType I] in
/-- Corrupting B preserves disjointness by the same exposure guard as A. -/
theorem oracleCorruptB_preserves_disjoint (vuln : StB → Finset ℕ) :
    QueryImpl.PreservesInv (oracleCorruptB vuln StA I Rho)
      (fun s => Disjoint s.exposed s.challenged) := by
  intro _ s hs z hz
  by_cases h : vuln s.stB ∩ s.challenged ≠ ∅
  · have hz' : z = (none, s) := by simpa [oracleCorruptB, h] using hz
    obtain rfl := hz'
    exact hs
  · have heq := not_not.mp h
    have hz' : z = (some s.stB, { s with exposed := s.exposed ∪ vuln s.stB }) := by
      simpa [oracleCorruptB, heq] using hz
    obtain rfl := hz'
    exact Finset.disjoint_union_left.mpr
      ⟨hs, Finset.disjoint_iff_inter_eq_empty.mpr (not_not.mp h)⟩

/-- Challenge queries preserve every invariant insensitive to the
`challenged` bookkeeping set, including rejected and unavailable queries. -/
theorem oracleChall_preservesInv (b : Bool)
    (Inv : GameState StA StB I Rho → Prop)
    (hbook : ∀ s challenged, Inv s → Inv { s with challenged := challenged }) :
    QueryImpl.PreservesInv (oracleChall b StA StB I Rho) Inv := by
  intro t s hs z hz
  by_cases h : t ∈ s.exposed ∨ t ∈ s.challenged
  · rw [oracleChall_rejected b s t h] at hz
    simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
  · have hins := hbook s (insert t s.challenged) hs
    cases hA : s.keyA t <;> cases hB : s.keyB t <;> cases b <;>
      simp only [oracleChall, Bool.false_eq_true, ↓reduceIte, bind_pure_comp,
        pure_bind, StateT.run_bind, StateT.run_get, h, hA, hB, StateT.run_pure,
        StateT.run_map, StateT.run_set, StateT.run_monadLift, monadLift_self,
        map_pure, Functor.map_map, support_pure, Set.mem_singleton_iff,
        support_map, support_uniformSample, Set.image_univ, Set.mem_range] at hz
    all_goals
      first
      | obtain rfl := hz
      | obtain ⟨k, rfl⟩ := hz
    all_goals assumption

omit [SampleableType I] in
/-- A corruption of A preserves every invariant insensitive to the
`exposed` bookkeeping set, whether the corruption is accepted or rejected. -/
theorem oracleCorruptA_preservesInv (vuln : StA → Finset ℕ)
    (Inv : GameState StA StB I Rho → Prop)
    (hbook : ∀ s exposed, Inv s → Inv { s with exposed := exposed }) :
    QueryImpl.PreservesInv (oracleCorruptA vuln StB I Rho) Inv := by
  intro _ s hs z hz
  by_cases h : vuln s.stA ∩ s.challenged ≠ ∅
  · have hz' : z = (none, s) := by simpa [oracleCorruptA, h] using hz
    obtain rfl := hz'
    exact hs
  · have heq := not_not.mp h
    have hz' : z = (some s.stA, { s with exposed := s.exposed ∪ vuln s.stA }) := by
      simpa [oracleCorruptA, heq] using hz
    obtain rfl := hz'
    exact hbook _ _ hs

omit [SampleableType I] in
/-- A corruption of B preserves every invariant insensitive to the
`exposed` bookkeeping set, whether the corruption is accepted or rejected. -/
theorem oracleCorruptB_preservesInv (vuln : StB → Finset ℕ)
    (Inv : GameState StA StB I Rho → Prop)
    (hbook : ∀ s exposed, Inv s → Inv { s with exposed := exposed }) :
    QueryImpl.PreservesInv (oracleCorruptB vuln StA I Rho) Inv := by
  intro _ s hs z hz
  by_cases h : vuln s.stB ∩ s.challenged ≠ ∅
  · have hz' : z = (none, s) := by simpa [oracleCorruptB, h] using hz
    obtain rfl := hz'
    exact hs
  · have heq := not_not.mp h
    have hz' : z = (some s.stB, { s with exposed := s.exposed ∪ vuln s.stB }) := by
      simpa [oracleCorruptB, heq] using hz
    obtain rfl := hz'
    exact hbook _ _ hs

end SCKAScheme
