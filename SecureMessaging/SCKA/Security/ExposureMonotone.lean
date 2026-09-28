/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Security.Exposure

/-!
# Persistence of exposed epochs

**Statement.** For every scheme, send-exposure rule, epoch `e`, and game
state `s` with `e ∈ s.exposed`, every supported successor `s'` of an
ordinary send, receive, leaking send, or corruption satisfies `e ∈ s'.exposed`.

**Proof.** Ordinary sends and receives preserve `exposed`. Accepted leaking
sends and corruptions replace it by a union containing its previous value.
Rejected queries retain the state. Challenges preserve exposure by the
invariant lemma in `Exposure`.

`HybridExposure` combines these per-query facts for adaptive execution.
Persistence ensures that challenges at an exposed epoch remain rejected
through later deliveries, state changes, and erasures.
-/

open OracleSpec OracleComp

namespace SCKAScheme

variable {IK StA StB I Rho Rand : Type} [DecidableEq I]

/-- A's ordinary send preserves exposure of every previously exposed epoch. -/
theorem oracleSendA_preserves_exposed
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) (e : ℕ) :
    QueryImpl.PreservesInv (oracleSendA scka) (fun s => e ∈ s.exposed) := by
  intro _ s hs z hz
  simp only [oracleSendA, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc] at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨out, _, hz⟩ := hz
  cases out with
  | none => simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
  | some out =>
    rcases out with ⟨key, msg, epoch, state⟩
    cases key <;>
      simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
        mem_support_pure_iff] at hz
    all_goals obtain rfl := hz; exact hs

/-- B's ordinary send preserves exposure of every previously exposed epoch. -/
theorem oracleSendB_preserves_exposed
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) (e : ℕ) :
    QueryImpl.PreservesInv (oracleSendB scka) (fun s => e ∈ s.exposed) := by
  intro _ s hs z hz
  simp only [oracleSendB, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc] at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨out, _, hz⟩ := hz
  cases out with
  | none => simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
  | some out =>
    rcases out with ⟨key, msg, epoch, state⟩
    cases key <;>
      simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
        mem_support_pure_iff] at hz
    all_goals obtain rfl := hz; exact hs

/-- A's receive oracle preserves every previously exposed epoch, including
failed, stale, repeated, and out-of-order deliveries. -/
theorem oracleRecvA_preserves_exposed
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) (e : ℕ) :
    QueryImpl.PreservesInv (oracleRecvA scka) (fun s => e ∈ s.exposed) := by
  intro n s hs z hz
  simp only [oracleRecvA, StateT.run_bind, StateT.run_get, pure_bind] at hz
  repeat' split at hz
  all_goals
    simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
      mem_support_pure_iff] at hz
    obtain rfl := hz
    exact hs

/-- B's receive oracle preserves every previously exposed epoch, including
failed, stale, repeated, and out-of-order deliveries. -/
theorem oracleRecvB_preserves_exposed
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) (e : ℕ) :
    QueryImpl.PreservesInv (oracleRecvB scka) (fun s => e ∈ s.exposed) := by
  intro n s hs z hz
  simp only [oracleRecvB, StateT.run_bind, StateT.run_get, pure_bind] at hz
  repeat' split at hz
  all_goals
    simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
      mem_support_pure_iff] at hz
    obtain rfl := hz
    exact hs

/-- A's leaking send preserves every exposed epoch: rejection leaves
exposure unchanged, and acceptance adds its newly exposed set. -/
theorem oracleSendArleak_preserves_exposed
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StA → StA → Rand → Finset ℕ) (e : ℕ) :
    QueryImpl.PreservesInv (oracleSendArleak leak scka) (fun s => e ∈ s.exposed) := by
  intro _ s hs z hz
  simp only [oracleSendArleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc] at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨out, _, hz⟩ := hz
  cases out with
  | none => simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
  | some out =>
    rcases out with ⟨key, msg, epoch, state, coins⟩
    dsimp only at hz
    split at hz
    · simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
    · cases key <;>
        simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
          mem_support_pure_iff] at hz
      all_goals obtain rfl := hz; exact Finset.mem_union_left _ hs

/-- B's leaking send preserves every exposed epoch: rejection leaves
exposure unchanged, and acceptance adds its newly exposed set. -/
theorem oracleSendBrleak_preserves_exposed
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (leak : StB → StB → Rand → Finset ℕ) (e : ℕ) :
    QueryImpl.PreservesInv (oracleSendBrleak leak scka) (fun s => e ∈ s.exposed) := by
  intro _ s hs z hz
  simp only [oracleSendBrleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc] at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨out, _, hz⟩ := hz
  cases out with
  | none => simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
  | some out =>
    rcases out with ⟨key, msg, epoch, state, coins⟩
    dsimp only at hz
    split at hz
    · simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
    · cases key <;>
        simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
          mem_support_pure_iff] at hz
      all_goals obtain rfl := hz; exact Finset.mem_union_left _ hs

omit [DecidableEq I] in
/-- Corrupting A preserves every exposed epoch, whether the query is
accepted or rejected by the challenged-epoch guard. -/
theorem oracleCorruptA_preserves_exposed (vuln : StA → Finset ℕ) (e : ℕ) :
    QueryImpl.PreservesInv (oracleCorruptA vuln StB I Rho) (fun s => e ∈ s.exposed) := by
  intro _ s hs z hz
  simp only [oracleCorruptA, StateT.run_bind, StateT.run_get, pure_bind] at hz
  split at hz
  all_goals
    simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
      mem_support_pure_iff] at hz
    obtain rfl := hz
  · exact hs
  · exact Finset.mem_union_left _ hs

omit [DecidableEq I] in
/-- Corrupting B preserves every exposed epoch, whether the query is
accepted or rejected by the challenged-epoch guard. -/
theorem oracleCorruptB_preserves_exposed (vuln : StB → Finset ℕ) (e : ℕ) :
    QueryImpl.PreservesInv (oracleCorruptB vuln StA I Rho) (fun s => e ∈ s.exposed) := by
  intro _ s hs z hz
  simp only [oracleCorruptB, StateT.run_bind, StateT.run_get, pure_bind] at hz
  split at hz
  all_goals
    simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
      mem_support_pure_iff] at hz
    obtain rfl := hz
  · exact hs
  · exact Finset.mem_union_left _ hs

end SCKAScheme
