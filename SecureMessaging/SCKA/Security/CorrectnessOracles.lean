/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Defs

/-!
# State preservation by correctness queries

Let `scka : SCKAScheme ProbComp IK StA StB I Rho Rand` be a scheme, and let
`s : GameState StA StB I Rho` be a game state. For every correctness query `t` and every
`(a, s')` in the support of `(sckaCorrectnessImpl scka t).run s`:

- `s'.exposed = s.exposed` and `s'.challenged = s.challenged`;
- `s'.nA ≤ s.nA + (if isSendQuery t then 1 else 0)`.
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

/-- A correctness query increases A's send counter by at most one on send queries and
does not increase it otherwise. -/
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

end SCKAScheme
