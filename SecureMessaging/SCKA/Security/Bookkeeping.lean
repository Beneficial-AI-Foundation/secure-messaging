/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Security.Exposure

/-!
# Exposure and challenge bookkeeping

**Invariant.** For a game state `s`, require
`Disjoint s.exposed s.challenged`. The first set records compromised epochs;
the second records epochs whose key challenge has been answered.

**Results.** For every scheme, correctness query, and supported successor,
both sets equal their initial values. Every leaking-send oracle preserves
disjointness and retains the challenged set. Challenges preserve membership
of previously challenged epochs and insert each newly answered epoch.

**Proof.** Rejected sends retain both sets. Accepted sends add a set `E`
passing `E ∩ challenged = ∅`. Combining this guard with initial disjointness
proves disjointness after the union. The challenge and corruption cases are
in `Exposure`; together these facts separate exposed epochs from challenged
epochs throughout the security game.
-/

open OracleSpec OracleComp

namespace SCKAScheme

variable {IK StA StB I Rho Rand : Type} [DecidableEq I]

/-- Every correctness oracle leaves the exposed and challenged sets
unchanged, including failed sends, unavailable deliveries, and receives
that set the correctness flag to `false`. -/
theorem correctnessImpl_securitySets_eq
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (t : (sckaCorrectnessSpec Rho).Domain) (s : GameState StA StB I Rho)
    (z : (sckaCorrectnessSpec Rho).Range t × GameState StA StB I Rho)
    (hz : z ∈ support ((sckaCorrectnessImpl scka t).run s)) :
    z.2.exposed = s.exposed ∧ z.2.challenged = s.challenged := by
  rcases t with ((((n | u) | u) | n) | n)
  · have hz' : ∃ r, (r, s) = z := by
      simpa [sckaCorrectnessImpl, oracleUnif] using hz
    obtain ⟨_, rfl⟩ := hz'
    exact ⟨rfl, rfl⟩
  all_goals
    simp only [sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      oracleSendA, oracleSendB, oracleRecvA, oracleRecvB,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      bind_assoc, pure_bind] at hz
  all_goals
    first
    | rw [mem_support_bind_iff] at hz
      obtain ⟨out, _, hz⟩ := hz
    | skip
  all_goals
    try dsimp only at hz
    repeat' split at hz
  all_goals
    simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
      mem_support_pure_iff] at hz
    obtain rfl := hz
    exact ⟨rfl, rfl⟩

/-- A's leaking-send oracle preserves disjointness of the exposed and
challenged sets: rejection retains both sets, and acceptance adds only
epochs passing the exposure guard. The proof applies to every send-exposure rule. -/
theorem oracleSendArleak_preserves_disjoint
    (leak : StA → StA → Rand → Finset ℕ) (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) :
    QueryImpl.PreservesInv (oracleSendArleak leak scka)
      (fun s => Disjoint s.exposed s.challenged) := by
  intro u s hs z hz
  cases u
  simp only [oracleSendArleak, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
    monadLift_self, bind_assoc, pure_bind, mem_support_bind_iff] at hz
  obtain ⟨out, _, hz⟩ := hz
  cases out with
  | none => simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
  | some out =>
    rcases out with ⟨key, msg, epoch, state, coins⟩
    dsimp only at hz
    split at hz
    · simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
    · rename_i hguard
      have he := Finset.disjoint_iff_inter_eq_empty.mpr (not_not.mp hguard)
      cases key <;>
        simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
          mem_support_pure_iff] at hz
      all_goals
        obtain rfl := hz
        exact Finset.disjoint_union_left.mpr ⟨hs, he⟩

/-- B's leaking-send oracle preserves disjointness of exposed and
challenged epochs, for every send-exposure rule. -/
theorem oracleSendBrleak_preserves_disjoint
    (leak : StB → StB → Rand → Finset ℕ) (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) :
    QueryImpl.PreservesInv (oracleSendBrleak leak scka)
      (fun s => Disjoint s.exposed s.challenged) := by
  intro u s hs z hz
  cases u
  simp only [oracleSendBrleak, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
    monadLift_self, bind_assoc, pure_bind, mem_support_bind_iff] at hz
  obtain ⟨out, _, hz⟩ := hz
  cases out with
  | none => simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
  | some out =>
    rcases out with ⟨key, msg, epoch, state, coins⟩
    dsimp only at hz
    split at hz
    · simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
    · rename_i hguard
      have he := Finset.disjoint_iff_inter_eq_empty.mpr (not_not.mp hguard)
      cases key <;>
        simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
          mem_support_pure_iff] at hz
      all_goals
        obtain rfl := hz
        exact Finset.disjoint_union_left.mpr ⟨hs, he⟩

/-- For every scheme, send-exposure rule, initial state, and supported
response/state pair, party A's leaking send retains the challenged set. -/
theorem oracleSendArleak_challenged_eq
    (leak : StA → StA → Rand → Finset ℕ)
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (u : Unit) (s : GameState StA StB I Rho)
    (z : Option (ℕ × Option ℕ × Rho × Rand) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleSendArleak leak scka u).run s)) :
    z.2.challenged = s.challenged := by
  cases u
  simp only [oracleSendArleak, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
    monadLift_self, bind_assoc, pure_bind, mem_support_bind_iff] at hz
  obtain ⟨out, _, hz⟩ := hz
  cases out with
  | none => simpa using (mem_support_pure_iff _ _).mp hz ▸ rfl
  | some out =>
    rcases out with ⟨key, msg, epoch, state, coins⟩
    dsimp only at hz
    split at hz
    · simpa using (mem_support_pure_iff _ _).mp hz ▸ rfl
    · cases key <;>
        simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
          mem_support_pure_iff] at hz
      all_goals obtain rfl := hz; rfl


/-- For every scheme, send-exposure rule, initial state, and supported
response/state pair, party B's leaking send retains the challenged set. -/
theorem oracleSendBrleak_challenged_eq
    (leak : StB → StB → Rand → Finset ℕ)
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (u : Unit) (s : GameState StA StB I Rho)
    (z : Option (ℕ × Option ℕ × Rho × Rand) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleSendBrleak leak scka u).run s)) :
    z.2.challenged = s.challenged := by
  cases u
  simp only [oracleSendBrleak, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
    monadLift_self, bind_assoc, pure_bind, mem_support_bind_iff] at hz
  obtain ⟨out, _, hz⟩ := hz
  cases out with
  | none => simpa using (mem_support_pure_iff _ _).mp hz ▸ rfl
  | some out =>
    rcases out with ⟨key, msg, epoch, state, coins⟩
    dsimp only at hz
    split at hz
    · simpa using (mem_support_pure_iff _ _).mp hz ▸ rfl
    · cases key <;>
        simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
          mem_support_pure_iff] at hz
      all_goals obtain rfl := hz; rfl


omit [DecidableEq I] in
/-- For every challenge bit `b`, epoch `e`, and initial state containing
`e` in `challenged`, every supported successor of every challenge query
also contains `e` in `challenged`. -/
theorem oracleChall_preserves_challenged [SampleableType I] (b : Bool) (e : ℕ) :
    QueryImpl.PreservesInv (oracleChall b StA StB I Rho)
      (fun s => e ∈ s.challenged) := by
  intro t s hs z hz
  by_cases h : t ∈ s.exposed ∨ t ∈ s.challenged
  · rw [oracleChall_rejected b s t h] at hz
    simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
  · cases hA : s.keyA t <;> cases hB : s.keyB t <;> cases b <;>
      simp only [oracleChall, Bool.false_eq_true, ↓reduceIte, bind_pure_comp,
        pure_bind, StateT.run_bind, StateT.run_get, h, hA, hB, StateT.run_pure,
        StateT.run_map, StateT.run_set, StateT.run_monadLift, monadLift_self,
        map_pure, Functor.map_map, support_pure, Set.mem_singleton_iff,
        support_map, support_uniformSample, Set.image_univ, Set.mem_range] at hz
    all_goals
      first
      | obtain rfl := hz
      | obtain ⟨k, rfl⟩ := hz
    all_goals first | exact hs | exact Finset.mem_insert_of_mem hs

omit [DecidableEq I] in
/-- For every challenge bit `b`, state `s`, and eligible epoch `t` with
an available key, every supported response/state pair has `t` in its
successor's challenged set. Eligibility means `t ∉ exposed ∪ challenged`. -/
theorem oracleChall_adds_challenged [SampleableType I]
    (b : Bool) (s : GameState StA StB I Rho) (t : ℕ)
    (helig : ¬(t ∈ s.exposed ∨ t ∈ s.challenged))
    (hkey : (s.keyA t).isSome ∨ (s.keyB t).isSome)
    (z : Option I × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleChall b StA StB I Rho t).run s)) :
    t ∈ z.2.challenged := by
  cases hA : s.keyA t <;> cases hB : s.keyB t
  all_goals try simp [hA, hB] at hkey
  all_goals cases b <;>
    simp only [oracleChall, Bool.false_eq_true, ↓reduceIte, bind_pure_comp,
      pure_bind, StateT.run_bind, StateT.run_get, helig, hA, hB,
      StateT.run_map, StateT.run_set, StateT.run_monadLift, monadLift_self,
      map_pure, Functor.map_map, support_pure, Set.mem_singleton_iff,
      support_map, support_uniformSample, Set.image_univ, Set.mem_range] at hz
  all_goals
    first
    | obtain rfl := hz
    | obtain ⟨k, rfl⟩ := hz
  all_goals exact Finset.mem_insert_self _ _


/-- For every scheme and epoch `e`, every correctness query preserves the
availability of an existing B-table key at `e`. These oracles retain the
entry or replace it by another present key. -/
theorem correctnessImpl_preserves_keyB_available
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) (e : ℕ) :
    QueryImpl.PreservesInv (sckaCorrectnessImpl scka) (fun s => (s.keyB e).isSome) := by
  intro t s hs z hz
  rcases t with ((((n | u) | u) | n) | n)
  · have hz' : ∃ r, (r, s) = z := by
      simpa [sckaCorrectnessImpl, oracleUnif] using hz
    obtain ⟨_, rfl⟩ := hz'
    exact hs
  all_goals
    simp only [sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      oracleSendA, oracleSendB, oracleRecvA, oracleRecvB,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      bind_assoc, pure_bind] at hz
  all_goals
    first
    | rw [mem_support_bind_iff] at hz
      obtain ⟨out, _, hz⟩ := hz
    | skip
  all_goals
    try dsimp only at hz
    repeat' split at hz
  all_goals
    simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
      mem_support_pure_iff] at hz
    obtain rfl := hz
    simp [Function.update, apply_ite, hs]

end SCKAScheme
