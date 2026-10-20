/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Correctness

/-!
# State preservation by correctness queries

Let `scka` be an SCKA scheme over `ProbComp`. Every query of `sckaCorrectnessImpl scka` keeps
`exposed` and `challenged` unchanged and increases A's send counter `nA` by at most one, only on
sends. A predicate on the local states, or on B's key table, that the local send and receive
algorithms preserve is preserved by these queries.
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
  · rw [mem_support_oracleUnif_run n s z hz]
    exact ⟨rfl, rfl⟩
  · cases u
    obtain ⟨out, _, rfl⟩ := (mem_support_oracleSendA_run_iff scka s z).mp hz
    rcases out with _ | ⟨_ | ⟨_, _⟩, _, _, _⟩ <;> exact ⟨rfl, rfl⟩
  · cases u
    obtain ⟨out, _, rfl⟩ := (mem_support_oracleSendB_run_iff scka s z).mp hz
    rcases out with _ | ⟨_ | ⟨_, _⟩, _, _, _⟩ <;> exact ⟨rfl, rfl⟩
  · rcases (mem_support_oracleRecvA_run_iff scka s n z).mp hz with
      ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _ | ⟨_, _⟩, _, _, _, _, rfl⟩ <;> exact ⟨rfl, rfl⟩
  · rcases (mem_support_oracleRecvB_run_iff scka s n z).mp hz with
      ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _ | ⟨_, _⟩, _, _, _, _, rfl⟩ <;> exact ⟨rfl, rfl⟩

/-- Every possible successor `s'` of a correctness query `t` from `s` satisfies
`s'.nA ≤ s.nA + 1` if `t` is a send and `s'.nA ≤ s.nA` otherwise. -/
theorem correctnessImpl_nA_step
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (t : (sckaCorrectnessSpec Rho).Domain) (s : GameState StA StB I Rho)
    (z : (sckaCorrectnessSpec Rho).Range t × GameState StA StB I Rho)
    (hz : z ∈ support ((sckaCorrectnessImpl scka t).run s)) :
    z.2.nA ≤ s.nA + if isSendQuery t then 1 else 0 := by
  rcases t with ((((n | u) | u) | n) | n)
  · rw [mem_support_oracleUnif_run n s z hz]
    exact Nat.le_refl _
  · cases u
    obtain ⟨out, _, rfl⟩ := (mem_support_oracleSendA_run_iff scka s z).mp hz
    rcases out with _ | ⟨key, _, _, _⟩
    · exact Nat.le_succ _
    · rcases key with _ | ⟨_, _⟩ <;> exact Nat.le_refl _
  · cases u
    obtain ⟨out, _, rfl⟩ := (mem_support_oracleSendB_run_iff scka s z).mp hz
    rcases out with _ | ⟨_ | ⟨_, _⟩, _, _, _⟩ <;> exact Nat.le_succ _
  · rcases (mem_support_oracleRecvA_run_iff scka s n z).mp hz with
      ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _ | ⟨_, _⟩, _, _, _, _, rfl⟩ <;> exact Nat.le_refl _
  · rcases (mem_support_oracleRecvB_run_iff scka s n z).mp hz with
      ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _ | ⟨_, _⟩, _, _, _, _, rfl⟩ <;> exact Nat.le_refl _

/-- Let `P : StA → StB → Prop` hold at the local states of `s`. If every possible successful
local send and every successful local receive of a message from these states preserve `P`, then
every possible successor of a correctness query from `s` satisfies `P`. -/
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
  · rw [mem_support_oracleUnif_run n s z hz]
    exact hs
  · cases u
    obtain ⟨out, hout, rfl⟩ := (mem_support_oracleSendA_run_iff scka s z).mp hz
    rcases out with _ | ⟨key, msg, epoch, next⟩
    · exact hs
    · rcases key with _ | ⟨_, _⟩ <;> exact hsa _ msg epoch next hout
  · cases u
    obtain ⟨out, hout, rfl⟩ := (mem_support_oracleSendB_run_iff scka s z).mp hz
    rcases out with _ | ⟨key, msg, epoch, next⟩
    · exact hs
    · rcases key with _ | ⟨_, _⟩ <;> exact hsb _ msg epoch next hout
  · rcases (mem_support_oracleRecvA_run_iff scka s n z).mp hz with
      ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨msg, _, key, epoch, next, _, hr, rfl⟩
    · exact hs
    · exact hs
    · rcases key with _ | ⟨_, _⟩ <;> exact hra msg _ epoch next hr
  · rcases (mem_support_oracleRecvB_run_iff scka s n z).mp hz with
      ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨msg, _, key, epoch, next, _, hr, rfl⟩
    · exact hs
    · exact hs
    · rcases key with _ | ⟨_, _⟩ <;> exact hrb msg _ epoch next hr

/-- Let `P` be a predicate on key tables `ℕ → Option I` with `P s.keyB`. Assume that
`P (Function.update s.keyB tI (some key))` holds for every epoch key `(tI, key)` that a possible
successful local send by B from `s.stB` returns, and for every one that a successful local
receive by B from `s.stB` returns. Then every possible successor `s'` of a correctness query
from `s` satisfies `P s'.keyB`. -/
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
  · rw [mem_support_oracleUnif_run n s z hz]
    exact hs
  · cases u
    obtain ⟨out, _, rfl⟩ := (mem_support_oracleSendA_run_iff scka s z).mp hz
    rcases out with _ | ⟨_ | ⟨_, _⟩, _, _, _⟩ <;> exact hs
  · cases u
    obtain ⟨out, hout, rfl⟩ := (mem_support_oracleSendB_run_iff scka s z).mp hz
    rcases out with _ | ⟨key, msg, epoch, next⟩
    · exact hs
    · rcases key with _ | ⟨tI, key⟩
      · exact hs
      · exact hsb tI key msg epoch next hout
  · rcases (mem_support_oracleRecvA_run_iff scka s n z).mp hz with
      ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _ | ⟨_, _⟩, _, _, _, _, rfl⟩ <;> exact hs
  · rcases (mem_support_oracleRecvB_run_iff scka s n z).mp hz with
      ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨msg, _, key, epoch, next, _, hr, rfl⟩
    · exact hs
    · exact hs
    · rcases key with _ | ⟨tI, key⟩
      · exact hs
      · exact hrb msg tI key epoch next hr

/-- For every epoch `e`, correctness queries preserve `(s.keyB e).isSome`. -/
theorem correctnessImpl_preserves_keyB_available
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) (e : ℕ) :
    QueryImpl.PreservesInv (sckaCorrectnessImpl scka) (fun s => (s.keyB e).isSome) :=
  fun t s hs z hz => correctnessImpl_preserves_keyBInv_at scka (fun keyB => (keyB e).isSome)
    s hs (fun _ _ _ _ _ _ => by simp [Function.update_apply, apply_ite, hs])
    (fun _ _ _ _ _ _ => by simp [Function.update_apply, apply_ite, hs]) t z hz

end SCKAScheme
