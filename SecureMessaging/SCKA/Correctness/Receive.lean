/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Defs

/-!
# Successful SCKA receives and current epochs

A supported outer `some` result advances the receiver's current epoch by taking
the maximum with the reported receiving epoch and leaves the other current epoch
unchanged. This success condition neither asserts `correct = true` nor guarantees
that a recorded message will be received successfully.
-/

open OracleSpec OracleComp

namespace SCKAScheme

variable {IK StA StB I Rho Rand : Type}

/-- A successful receive at A updates A's current epoch and preserves B's. -/
theorem oracleRecvA_success_currentEpoch
    [DecidableEq I]
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (s s' : GameState StA StB I Rho)
    (n trcv : ℕ) (tI : Option ℕ)
    (hout : (some (trcv, tI), s') ∈ support
      ((oracleRecvA scka n).run s)) :
    s'.tcurA = max s.tcurA trcv ∧
      s'.tcurB = s.tcurB := by
  cases hmsg : s.msgB n with
  | none => simp [oracleRecvA, hmsg] at hout
  | some entry =>
    rcases entry with ⟨ρ, tsnd⟩
    cases hrecv : scka.recvA s.stA ρ with
    | none => simp [oracleRecvA, hmsg, hrecv] at hout
    | some out =>
      rcases out with ⟨key?, epoch, st'⟩
      cases key? with
      | none =>
        simp only [oracleRecvA, bind_pure_comp, StateT.run_bind, StateT.run_get,
          pure_bind, hmsg, hrecv, StateT.run_map, StateT.run_set, map_pure,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hout
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hout
        exact ⟨rfl, rfl⟩
      | some key =>
        rcases key with ⟨epochI, key⟩
        simp only [oracleRecvA, bind_pure_comp, StateT.run_bind, StateT.run_get,
          pure_bind, hmsg, hrecv, StateT.run_map, StateT.run_set, map_pure,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hout
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hout
        exact ⟨rfl, rfl⟩

/-- A successful receive at B updates B's current epoch and preserves A's. -/
theorem oracleRecvB_success_currentEpoch
    [DecidableEq I]
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (s s' : GameState StA StB I Rho)
    (n trcv : ℕ) (tI : Option ℕ)
    (hout : (some (trcv, tI), s') ∈ support
      ((oracleRecvB scka n).run s)) :
    s'.tcurB = max s.tcurB trcv ∧
      s'.tcurA = s.tcurA := by
  cases hmsg : s.msgA n with
  | none => simp [oracleRecvB, hmsg] at hout
  | some entry =>
    rcases entry with ⟨ρ, tsnd⟩
    cases hrecv : scka.recvB s.stB ρ with
    | none => simp [oracleRecvB, hmsg, hrecv] at hout
    | some out =>
      rcases out with ⟨key?, epoch, st'⟩
      cases key? with
      | none =>
        simp only [oracleRecvB, bind_pure_comp, StateT.run_bind, StateT.run_get,
          pure_bind, hmsg, hrecv, StateT.run_map, StateT.run_set, map_pure,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hout
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hout
        exact ⟨rfl, rfl⟩
      | some key =>
        rcases key with ⟨epochI, key⟩
        simp only [oracleRecvB, bind_pure_comp, StateT.run_bind, StateT.run_get,
          pure_bind, hmsg, hrecv, StateT.run_map, StateT.run_set, map_pure,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hout
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hout
        exact ⟨rfl, rfl⟩

end SCKAScheme
