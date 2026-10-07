/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Defs

/-!
# State preservation by correctness queries

Let `scka : SCKAScheme ProbComp IK StA StB I Rho Rand` be a scheme, and let
`s : GameState StA StB I Rho` be a game state. The correctness oracles provide uniform
randomness, ordinary sends, and receives. For every query `t` and every possible result
`(a, s')` of `(sckaCorrectnessImpl scka t).run s`:

- `s'.exposed = s.exposed` and `s'.challenged = s.challenged`;
- `s'.nA ≤ s.nA + (if isSendQuery t then 1 else 0)`;
- a predicate on the two local states holds at `s'` if it holds at `s` and every possible
  successful local send and every successful local receive from `s` preserves it
  (`correctnessImpl_preserves_localInv_at`);
- a predicate on B's key table holds at `s'` if it holds at `s` and after inserting every key
  that a possible successful send or receive by B from `s` derives
  (`correctnessImpl_preserves_keyBInv_at`).
-/

open OracleSpec OracleComp

namespace SCKAScheme

variable {IK StA StB I Rho Rand : Type}

/-- A uniform-randomness query leaves the game state unchanged. -/
theorem mem_support_oracleUnif_run (n : ℕ) (s : GameState StA StB I Rho)
    (z : unifSpec.Range n × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleUnif StA StB I Rho n).run s)) : z.2 = s := by
  have hz' : ∃ r, (r, s) = z := by simpa [oracleUnif] using hz
  obtain ⟨_, rfl⟩ := hz'
  rfl

variable [DecidableEq I]

/-- Every correctness query preserves `exposed` and `challenged`. -/
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

/-- A correctness query satisfies `s'.nA ≤ s.nA + 1` if it is a send query and
`s'.nA ≤ s.nA` otherwise. -/
theorem correctnessImpl_nA_step
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (t : (sckaCorrectnessSpec Rho).Domain) (s : GameState StA StB I Rho)
    (z : (sckaCorrectnessSpec Rho).Range t × GameState StA StB I Rho)
    (hz : z ∈ support ((sckaCorrectnessImpl scka t).run s)) :
    z.2.nA ≤ s.nA + if isSendQuery t then 1 else 0 := by
  rcases t with ((((n | u) | u) | n) | n)
  · have hz' : ∃ r, (r, s) = z := by
      simpa [sckaCorrectnessImpl, oracleUnif] using hz
    obtain ⟨_, rfl⟩ := hz'
    simp [isSendQuery]
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
    try cases u
    simp [isSendQuery]

/-- Let `P : StA → StB → Prop` hold at `s`. If every supported successful local send and
successful local receive from `s` preserves `P`, every correctness-query successor from `s`
satisfies `P`. -/
theorem correctnessImpl_preserves_localInv_at
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) (P : StA → StB → Prop)
    (s : GameState StA StB I Rho) (hs : P s.stA s.stB)
    (hsa : ∀ key msg epoch next,
      some (key, msg, epoch, next) ∈ support (scka.sendA s.stA) → P next s.stB)
    (hsb : ∀ key msg epoch next,
      some (key, msg, epoch, next) ∈ support (scka.sendB s.stB) → P s.stA next)
    (hra : ∀ msg key epoch next,
      scka.recvA s.stA msg = some (key, epoch, next) → P next s.stB)
    (hrb : ∀ msg key epoch next,
      scka.recvB s.stB msg = some (key, epoch, next) → P s.stA next)
    (t : (sckaCorrectnessSpec Rho).Domain)
    (z : (sckaCorrectnessSpec Rho).Range t × GameState StA StB I Rho)
    (hz : z ∈ support ((sckaCorrectnessImpl scka t).run s)) :
    P z.2.stA z.2.stB := by
  rcases t with ((((n | u) | u) | n) | n)
  · have hz' : ∃ r, (r, s) = z := by
      simpa [sckaCorrectnessImpl, oracleUnif] using hz
    obtain ⟨_, rfl⟩ := hz'
    exact hs
  · cases u
    simp only [sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      oracleSendA, StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      bind_assoc, pure_bind, mem_support_bind_iff] at hz
    obtain ⟨out, hout, hz⟩ := hz
    cases out with
    | none => simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
    | some out =>
      rcases out with ⟨key, msg, epoch, next⟩
      have hnext := hsa key msg epoch next hout
      cases key <;>
        simp only [StateT.run_bind, StateT.run_set, pure_bind,
          StateT.run_pure, mem_support_pure_iff] at hz
      all_goals obtain rfl := hz; exact hnext
  · cases u
    simp only [sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      oracleSendB, StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      bind_assoc, pure_bind, mem_support_bind_iff] at hz
    obtain ⟨out, hout, hz⟩ := hz
    cases out with
    | none => simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
    | some out =>
      rcases out with ⟨key, msg, epoch, next⟩
      have hnext := hsb key msg epoch next hout
      cases key <;>
        simp only [StateT.run_bind, StateT.run_set, pure_bind,
          StateT.run_pure, mem_support_pure_iff] at hz
      all_goals obtain rfl := hz; exact hnext
  · simp only [sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      oracleRecvA, StateT.run_bind, StateT.run_get, pure_bind] at hz
    cases hm : s.msgB n with
    | none =>
      simp only [hm, StateT.run_pure, mem_support_pure_iff] at hz
      obtain rfl := hz
      exact hs
    | some entry =>
      rcases entry with ⟨msg, epoch⟩
      simp only [hm] at hz
      cases hr : scka.recvA s.stA msg with
      | none =>
        simp only [hr, StateT.run_bind, StateT.run_set, pure_bind,
          StateT.run_pure, mem_support_pure_iff] at hz
        obtain rfl := hz
        exact hs
      | some out =>
        rcases out with ⟨key, t, next⟩
        have hnext := hra msg key t next hr
        cases key <;>
          simp only [hr, StateT.run_bind, StateT.run_set, pure_bind,
            StateT.run_pure, mem_support_pure_iff] at hz
        all_goals obtain rfl := hz; exact hnext
  · simp only [sckaCorrectnessImpl, QueryImpl.add_apply_inr,
      oracleRecvB, StateT.run_bind, StateT.run_get, pure_bind] at hz
    cases hm : s.msgA n with
    | none =>
      simp only [hm, StateT.run_pure, mem_support_pure_iff] at hz
      obtain rfl := hz
      exact hs
    | some entry =>
      rcases entry with ⟨msg, epoch⟩
      simp only [hm] at hz
      cases hr : scka.recvB s.stB msg with
      | none =>
        simp only [hr, StateT.run_bind, StateT.run_set, pure_bind,
          StateT.run_pure, mem_support_pure_iff] at hz
        obtain rfl := hz
        exact hs
      | some out =>
        rcases out with ⟨key, t, next⟩
        have hnext := hrb msg key t next hr
        cases key <;>
          simp only [hr, StateT.run_bind, StateT.run_set, pure_bind,
            StateT.run_pure, mem_support_pure_iff] at hz
        all_goals obtain rfl := hz; exact hnext

/-- Let `P` be a predicate on key tables `ℕ → Option I` with `P s.keyB`. Assume that
`P (Function.update s.keyB tI (some key))` holds for every epoch key `(tI, key)` that a possible
successful local send by B from `s.stB` returns, and for every one that a successful local
receive by B from `s.stB` returns. Then every correctness-query successor `s'` from `s`
satisfies `P s'.keyB`. Queries by A and keyless queries by B leave the table unchanged. -/
theorem correctnessImpl_preserves_keyBInv_at
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) (P : (ℕ → Option I) → Prop)
    (s : GameState StA StB I Rho) (hs : P s.keyB)
    (hsb : ∀ tI key msg epoch next,
      some (some (tI, key), msg, epoch, next) ∈ support (scka.sendB s.stB) →
      P (Function.update s.keyB tI (some key)))
    (hrb : ∀ msg tI key epoch next,
      scka.recvB s.stB msg = some (some (tI, key), epoch, next) →
      P (Function.update s.keyB tI (some key)))
    (t : (sckaCorrectnessSpec Rho).Domain)
    (z : (sckaCorrectnessSpec Rho).Range t × GameState StA StB I Rho)
    (hz : z ∈ support ((sckaCorrectnessImpl scka t).run s)) :
    P z.2.keyB := by
  rcases t with ((((n | u) | u) | n) | n)
  · have hz' : ∃ r, (r, s) = z := by
      simpa [sckaCorrectnessImpl, oracleUnif] using hz
    obtain ⟨_, rfl⟩ := hz'
    exact hs
  · cases u
    simp only [sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      oracleSendA, StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      bind_assoc, pure_bind, mem_support_bind_iff] at hz
    obtain ⟨out, _, hz⟩ := hz
    cases out with
    | none => simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
    | some out =>
      rcases out with ⟨key, msg, epoch, next⟩
      cases key <;>
        simp only [StateT.run_bind, StateT.run_set, pure_bind,
          StateT.run_pure, mem_support_pure_iff] at hz
      all_goals obtain rfl := hz; exact hs
  · cases u
    simp only [sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      oracleSendB, StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      bind_assoc, pure_bind, mem_support_bind_iff] at hz
    obtain ⟨out, hout, hz⟩ := hz
    cases out with
    | none => simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
    | some out =>
      rcases out with ⟨key, msg, epoch, next⟩
      cases key with
      | none =>
        simp only [StateT.run_bind, StateT.run_set, pure_bind,
          StateT.run_pure, mem_support_pure_iff] at hz
        obtain rfl := hz
        exact hs
      | some key =>
        rcases key with ⟨tI, key⟩
        simp only [StateT.run_bind, StateT.run_set, pure_bind,
          StateT.run_pure, mem_support_pure_iff] at hz
        obtain rfl := hz
        exact hsb tI key msg epoch next hout
  · simp only [sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      oracleRecvA, StateT.run_bind, StateT.run_get, pure_bind] at hz
    repeat' split at hz
    all_goals
      simp only [StateT.run_bind, StateT.run_set, pure_bind,
        StateT.run_pure, mem_support_pure_iff] at hz
      obtain rfl := hz
      exact hs
  · simp only [sckaCorrectnessImpl, QueryImpl.add_apply_inr,
      oracleRecvB, StateT.run_bind, StateT.run_get, pure_bind] at hz
    cases hm : s.msgA n with
    | none =>
      simp only [hm, StateT.run_pure, mem_support_pure_iff] at hz
      obtain rfl := hz
      exact hs
    | some entry =>
      rcases entry with ⟨msg, epoch⟩
      simp only [hm] at hz
      cases hr : scka.recvB s.stB msg with
      | none =>
        simp only [hr, StateT.run_bind, StateT.run_set, pure_bind,
          StateT.run_pure, mem_support_pure_iff] at hz
        obtain rfl := hz
        exact hs
      | some out =>
        rcases out with ⟨key, trcv, next⟩
        cases key with
        | none =>
          simp only [hr, StateT.run_bind, StateT.run_set, pure_bind,
            StateT.run_pure, mem_support_pure_iff] at hz
          obtain rfl := hz
          exact hs
        | some key =>
          rcases key with ⟨tI, key⟩
          simp only [hr, StateT.run_bind, StateT.run_set, pure_bind,
            StateT.run_pure, mem_support_pure_iff] at hz
          obtain rfl := hz
          exact hrb msg tI key trcv next hr

end SCKAScheme
