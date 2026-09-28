/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Defs

/-!
# Lifting local-state invariants through SCKA bookkeeping

For a predicate `P : StA → StB → Prop`, game bookkeeping preserves `P`
whenever the local send and receive algorithms do. The theorem is pointwise:
its premises concern one input state, allowing a proof to instantiate it
with a scheme chosen from that state. Message and key recording retain the
local successor states supplied by the protocol algorithms.
-/

open OracleSpec OracleComp

namespace SCKAScheme

variable {IK StA StB I Rho Rand : Type} [DecidableEq I]

/-- Fix a scheme, local-state predicate `P`, and input state `s` satisfying
`P s.stA s.stB`. If every supported successful local send and every successful
local receive preserves `P` at `s`, then every correctness query from `s`
has only successors satisfying `P`. -/
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

end SCKAScheme
