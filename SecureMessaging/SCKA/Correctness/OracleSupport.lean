/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Defs

/-!
# SCKA correctness oracles as pure game-state updates

Each correctness-game oracle (`oracleSendA`, `oracleSendB`, `oracleRecvA`, `oracleRecvB`)
first runs the scheme's local `send` or `recv` and then applies a *pure* update to the game
state. This file names those updates (`applySendA`, `applySendB`, `applyRecvA`,
`applyRecvB`) and restates the oracle runs in terms of them:

* `oracleSendA_run_cases` and its three twins characterize the support of each send and
  receive run, for invariant-preservation proofs;
* `oracleSendA_run_eq` and `oracleSendB_run_eq` rewrite a send run as the local send followed
  by a pure outcome (`sendAOutcome`, `sendBOutcome`), for expected-value proofs.

The projection lemmas (`applySendA_stA`, …) expose the fields that such proofs read, so the
`StateT` plumbing of the oracle implementations is not unfolded downstream.
-/

open OracleSpec OracleComp

namespace SCKAScheme

variable {IK StA StB I Rho Rand : Type}

section Send

variable [DecidableEq I]

/-- Pure game-state update of `oracleSendA` on a successful local send. -/
def applySendA (s : GameState StA StB I Rho) (key? : Option (ℕ × I)) (ρ : Rho)
    (tsnd : ℕ) (stA' : StA) : GameState StA StB I Rho :=
  match key? with
  | none =>
    { s with
      stA := stA'
      tcurA := tsnd
      msgA := Function.update s.msgA (s.nA + 1) (some (ρ, tsnd))
      nA := s.nA + 1
      correct := s.correct && decide (s.tcurA ≤ tsnd) &&
        (List.range (tsnd + 1)).all (fun t => t = 0 || (s.keyA t).isSome) }
  | some (tI, key) =>
    { s with
      stA := stA'
      tcurA := tsnd
      keyA := Function.update s.keyA tI (some key)
      msgA := Function.update s.msgA (s.nA + 1) (some (ρ, tsnd))
      nA := s.nA + 1
      correct := s.correct && decide (s.tcurA ≤ tsnd) && (s.keyA tI).isNone &&
        ((s.keyB tI).isNone || s.keyB tI == some key) &&
        (List.range (tsnd + 1)).all
          (fun t => t = 0 || (Function.update s.keyA tI (some key) t).isSome) }

/-- Pure game-state update of `oracleSendB` on a successful local send. -/
def applySendB (s : GameState StA StB I Rho) (key? : Option (ℕ × I)) (ρ : Rho)
    (tsnd : ℕ) (stB' : StB) : GameState StA StB I Rho :=
  match key? with
  | none =>
    { s with
      stB := stB'
      tcurB := tsnd
      msgB := Function.update s.msgB (s.nB + 1) (some (ρ, tsnd))
      nB := s.nB + 1
      correct := s.correct && decide (s.tcurB ≤ tsnd) &&
        (List.range (tsnd + 1)).all (fun t => t = 0 || (s.keyB t).isSome) }
  | some (tI, key) =>
    { s with
      stB := stB'
      tcurB := tsnd
      keyB := Function.update s.keyB tI (some key)
      msgB := Function.update s.msgB (s.nB + 1) (some (ρ, tsnd))
      nB := s.nB + 1
      correct := s.correct && decide (s.tcurB ≤ tsnd) && (s.keyB tI).isNone &&
        ((s.keyA tI).isNone || s.keyA tI == some key) &&
        (List.range (tsnd + 1)).all
          (fun t => t = 0 || (Function.update s.keyB tI (some key) t).isSome) }

/-- Pure game-state update of `oracleRecvA` on a successful local receive of the
recorded entry `(ρ, tsnd)`. -/
def applyRecvA (s : GameState StA StB I Rho) (tsnd : ℕ) (key? : Option (ℕ × I))
    (trcv : ℕ) (stA' : StA) : GameState StA StB I Rho :=
  match key? with
  | none =>
    { s with
      stA := stA'
      tcurA := max s.tcurA trcv
      correct := s.correct && (trcv == tsnd) &&
        (List.range (max s.tcurA trcv + 1)).all (fun t => t = 0 || (s.keyA t).isSome) }
  | some (tI, key) =>
    { s with
      stA := stA'
      tcurA := max s.tcurA trcv
      keyA := Function.update s.keyA tI (some key)
      correct := s.correct && (trcv == tsnd) && (s.keyA tI).isNone &&
        ((s.keyB tI).isNone || s.keyB tI == some key) &&
        (List.range (max s.tcurA trcv + 1)).all
          (fun t => t = 0 || (Function.update s.keyA tI (some key) t).isSome) }

/-- Pure game-state update of `oracleRecvB` on a successful local receive. -/
def applyRecvB (s : GameState StA StB I Rho) (tsnd : ℕ) (key? : Option (ℕ × I))
    (trcv : ℕ) (stB' : StB) : GameState StA StB I Rho :=
  match key? with
  | none =>
    { s with
      stB := stB'
      tcurB := max s.tcurB trcv
      correct := s.correct && (trcv == tsnd) &&
        (List.range (max s.tcurB trcv + 1)).all (fun t => t = 0 || (s.keyB t).isSome) }
  | some (tI, key) =>
    { s with
      stB := stB'
      tcurB := max s.tcurB trcv
      keyB := Function.update s.keyB tI (some key)
      correct := s.correct && (trcv == tsnd) && (s.keyB tI).isNone &&
        ((s.keyA tI).isNone || s.keyA tI == some key) &&
        (List.range (max s.tcurB trcv + 1)).all
          (fun t => t = 0 || (Function.update s.keyB tI (some key) t).isSome) }

/-! ### Projections (the fields every invariant proof reads) -/

section Proj
variable (s : GameState StA StB I Rho) (key? : Option (ℕ × I)) (ρ : Rho) (tsnd trcv : ℕ)
  (stA' : StA) (stB' : StB)

/-- `applySendA` installs A's new state. -/
@[simp] theorem applySendA_stA : (applySendA s key? ρ tsnd stA').stA = stA' := by
  rcases key? with _ | ⟨_, _⟩ <;> rfl
/-- `applySendA` keeps B's state. -/
@[simp] theorem applySendA_stB : (applySendA s key? ρ tsnd stA').stB = s.stB := by
  rcases key? with _ | ⟨_, _⟩ <;> rfl
/-- `applySendA` records the message in A's table. -/
@[simp] theorem applySendA_msgA :
    (applySendA s key? ρ tsnd stA').msgA = Function.update s.msgA (s.nA + 1) (some (ρ, tsnd)) := by
  rcases key? with _ | ⟨_, _⟩ <;> rfl
/-- `applySendA` keeps B's message table. -/
@[simp] theorem applySendA_msgB : (applySendA s key? ρ tsnd stA').msgB = s.msgB := by
  rcases key? with _ | ⟨_, _⟩ <;> rfl
/-- `applySendA` keeps B's key table. -/
@[simp] theorem applySendA_keyB : (applySendA s key? ρ tsnd stA').keyB = s.keyB := by
  rcases key? with _ | ⟨_, _⟩ <;> rfl
/-- Without an emitted key, `applySendA` keeps A's key table. -/
@[simp] theorem applySendA_keyA_none : (applySendA s none ρ tsnd stA').keyA = s.keyA := rfl
/-- `applySendA` records an emitted key in A's key table. -/
@[simp] theorem applySendA_keyA_some (tI : ℕ) (key : I) :
    (applySendA s (some (tI, key)) ρ tsnd stA').keyA = Function.update s.keyA tI (some key) := rfl
/-- `applySendA` sets A's current epoch to the sending epoch. -/
@[simp] theorem applySendA_tcurA : (applySendA s key? ρ tsnd stA').tcurA = tsnd := by
  rcases key? with _ | ⟨_, _⟩ <;> rfl
/-- `applySendA` keeps B's current epoch. -/
@[simp] theorem applySendA_tcurB : (applySendA s key? ρ tsnd stA').tcurB = s.tcurB := by
  rcases key? with _ | ⟨_, _⟩ <;> rfl

/-- `applySendB` installs B's new state. -/
@[simp] theorem applySendB_stB : (applySendB s key? ρ tsnd stB').stB = stB' := by
  rcases key? with _ | ⟨_, _⟩ <;> rfl
/-- `applySendB` keeps A's state. -/
@[simp] theorem applySendB_stA : (applySendB s key? ρ tsnd stB').stA = s.stA := by
  rcases key? with _ | ⟨_, _⟩ <;> rfl
/-- `applySendB` records the message in B's table. -/
@[simp] theorem applySendB_msgB :
    (applySendB s key? ρ tsnd stB').msgB = Function.update s.msgB (s.nB + 1) (some (ρ, tsnd)) := by
  rcases key? with _ | ⟨_, _⟩ <;> rfl
/-- `applySendB` keeps A's message table. -/
@[simp] theorem applySendB_msgA : (applySendB s key? ρ tsnd stB').msgA = s.msgA := by
  rcases key? with _ | ⟨_, _⟩ <;> rfl
/-- `applySendB` keeps A's key table. -/
@[simp] theorem applySendB_keyA : (applySendB s key? ρ tsnd stB').keyA = s.keyA := by
  rcases key? with _ | ⟨_, _⟩ <;> rfl
/-- Without an emitted key, `applySendB` keeps B's key table. -/
@[simp] theorem applySendB_keyB_none : (applySendB s none ρ tsnd stB').keyB = s.keyB := rfl
/-- `applySendB` records an emitted key in B's key table. -/
@[simp] theorem applySendB_keyB_some (tI : ℕ) (key : I) :
    (applySendB s (some (tI, key)) ρ tsnd stB').keyB = Function.update s.keyB tI (some key) := rfl
/-- `applySendB` sets B's current epoch to the sending epoch. -/
@[simp] theorem applySendB_tcurB : (applySendB s key? ρ tsnd stB').tcurB = tsnd := by
  rcases key? with _ | ⟨_, _⟩ <;> rfl
/-- `applySendB` keeps A's current epoch. -/
@[simp] theorem applySendB_tcurA : (applySendB s key? ρ tsnd stB').tcurA = s.tcurA := by
  rcases key? with _ | ⟨_, _⟩ <;> rfl

/-- `applyRecvA` installs A's new state. -/
@[simp] theorem applyRecvA_stA : (applyRecvA s tsnd key? trcv stA').stA = stA' := by
  rcases key? with _ | ⟨_, _⟩ <;> rfl
/-- `applyRecvA` keeps B's state. -/
@[simp] theorem applyRecvA_stB : (applyRecvA s tsnd key? trcv stA').stB = s.stB := by
  rcases key? with _ | ⟨_, _⟩ <;> rfl
/-- `applyRecvA` keeps A's message table. -/
@[simp] theorem applyRecvA_msgA : (applyRecvA s tsnd key? trcv stA').msgA = s.msgA := by
  rcases key? with _ | ⟨_, _⟩ <;> rfl
/-- `applyRecvA` keeps B's message table. -/
@[simp] theorem applyRecvA_msgB : (applyRecvA s tsnd key? trcv stA').msgB = s.msgB := by
  rcases key? with _ | ⟨_, _⟩ <;> rfl
/-- `applyRecvA` keeps B's key table. -/
@[simp] theorem applyRecvA_keyB : (applyRecvA s tsnd key? trcv stA').keyB = s.keyB := by
  rcases key? with _ | ⟨_, _⟩ <;> rfl
/-- Without an emitted key, `applyRecvA` keeps A's key table. -/
@[simp] theorem applyRecvA_keyA_none : (applyRecvA s tsnd none trcv stA').keyA = s.keyA := rfl
/-- `applyRecvA` records an emitted key in A's key table. -/
@[simp] theorem applyRecvA_keyA_some (tI : ℕ) (key : I) :
    (applyRecvA s tsnd (some (tI, key)) trcv stA').keyA =
      Function.update s.keyA tI (some key) := rfl
/-- `applyRecvA` sets A's current epoch to the maximum of the old one and the receiving epoch. -/
@[simp] theorem applyRecvA_tcurA :
    (applyRecvA s tsnd key? trcv stA').tcurA = max s.tcurA trcv := by
  rcases key? with _ | ⟨_, _⟩ <;> rfl
/-- `applyRecvA` keeps B's current epoch. -/
@[simp] theorem applyRecvA_tcurB : (applyRecvA s tsnd key? trcv stA').tcurB = s.tcurB := by
  rcases key? with _ | ⟨_, _⟩ <;> rfl

/-- `applyRecvB` installs B's new state. -/
@[simp] theorem applyRecvB_stB : (applyRecvB s tsnd key? trcv stB').stB = stB' := by
  rcases key? with _ | ⟨_, _⟩ <;> rfl
/-- `applyRecvB` keeps A's state. -/
@[simp] theorem applyRecvB_stA : (applyRecvB s tsnd key? trcv stB').stA = s.stA := by
  rcases key? with _ | ⟨_, _⟩ <;> rfl
/-- `applyRecvB` keeps A's message table. -/
@[simp] theorem applyRecvB_msgA : (applyRecvB s tsnd key? trcv stB').msgA = s.msgA := by
  rcases key? with _ | ⟨_, _⟩ <;> rfl
/-- `applyRecvB` keeps B's message table. -/
@[simp] theorem applyRecvB_msgB : (applyRecvB s tsnd key? trcv stB').msgB = s.msgB := by
  rcases key? with _ | ⟨_, _⟩ <;> rfl
/-- `applyRecvB` keeps A's key table. -/
@[simp] theorem applyRecvB_keyA : (applyRecvB s tsnd key? trcv stB').keyA = s.keyA := by
  rcases key? with _ | ⟨_, _⟩ <;> rfl
/-- Without an emitted key, `applyRecvB` keeps B's key table. -/
@[simp] theorem applyRecvB_keyB_none : (applyRecvB s tsnd none trcv stB').keyB = s.keyB := rfl
/-- `applyRecvB` records an emitted key in B's key table. -/
@[simp] theorem applyRecvB_keyB_some (tI : ℕ) (key : I) :
    (applyRecvB s tsnd (some (tI, key)) trcv stB').keyB =
      Function.update s.keyB tI (some key) := rfl
/-- `applyRecvB` sets B's current epoch to the maximum of the old one and the receiving epoch. -/
@[simp] theorem applyRecvB_tcurB :
    (applyRecvB s tsnd key? trcv stB').tcurB = max s.tcurB trcv := by
  rcases key? with _ | ⟨_, _⟩ <;> rfl
/-- `applyRecvB` keeps A's current epoch. -/
@[simp] theorem applyRecvB_tcurA : (applyRecvB s tsnd key? trcv stB').tcurA = s.tcurA := by
  rcases key? with _ | ⟨_, _⟩ <;> rfl
end Proj

/-! ### Support characterizations -/

variable (scka : SCKAScheme ProbComp IK StA StB I Rho Rand)

/-- An outcome of `oracleSendA` is a rejected send with the state unchanged, or a successful
send followed by `applySendA`. -/
theorem oracleSendA_run_cases (s : GameState StA StB I Rho)
    (z : Option (ℕ × Option ℕ × Rho) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleSendA scka ()).run s)) :
    (none ∈ support (scka.sendA s.stA) ∧ z = (none, s)) ∨
    ∃ key? ρ tsnd stA', some (key?, ρ, tsnd, stA') ∈ support (scka.sendA s.stA) ∧
      z = (some (tsnd, key?.map Prod.fst, ρ), applySendA s key? ρ tsnd stA') := by
  simp only [oracleSendA, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_liftM,
    bind_assoc] at hz
  obtain ⟨out, hout, hz⟩ := mem_support_bind_peel _ _ hz
  rcases out with _ | ⟨key?, ρ, tsnd, stA'⟩
  · left
    refine ⟨hout, ?_⟩
    simpa using hz
  · right
    refine ⟨key?, ρ, tsnd, stA', hout, ?_⟩
    rcases key? with _ | ⟨tI, key⟩
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      rfl
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      rfl

/-- An outcome of `oracleSendB` is a rejected send with the state unchanged, or a successful
send followed by `applySendB`. -/
theorem oracleSendB_run_cases (s : GameState StA StB I Rho)
    (z : Option (ℕ × Option ℕ × Rho) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleSendB scka ()).run s)) :
    (none ∈ support (scka.sendB s.stB) ∧ z = (none, s)) ∨
    ∃ key? ρ tsnd stB', some (key?, ρ, tsnd, stB') ∈ support (scka.sendB s.stB) ∧
      z = (some (tsnd, key?.map Prod.fst, ρ), applySendB s key? ρ tsnd stB') := by
  simp only [oracleSendB, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_liftM,
    bind_assoc] at hz
  obtain ⟨out, hout, hz⟩ := mem_support_bind_peel _ _ hz
  rcases out with _ | ⟨key?, ρ, tsnd, stB'⟩
  · left
    refine ⟨hout, ?_⟩
    simpa using hz
  · right
    refine ⟨key?, ρ, tsnd, stB', hout, ?_⟩
    rcases key? with _ | ⟨tI, key⟩
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      rfl
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      rfl

/-- An outcome of `oracleRecvA n` is one of: no recorded message, with the state unchanged; a
failed receive, with `correct` cleared; a successful receive followed by `applyRecvA`. -/
theorem oracleRecvA_run_cases (n : ℕ) (s : GameState StA StB I Rho)
    (z : Option (ℕ × Option ℕ) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleRecvA scka n).run s)) :
    (s.msgB n = none ∧ z = (none, s)) ∨
    (∃ ρ tsnd, s.msgB n = some (ρ, tsnd) ∧ scka.recvA s.stA ρ = none ∧
      z = (none, { s with correct := false })) ∨
    ∃ ρ tsnd key? trcv stA', s.msgB n = some (ρ, tsnd) ∧
      scka.recvA s.stA ρ = some (key?, trcv, stA') ∧
      z = (some (trcv, key?.map Prod.fst), applyRecvA s tsnd key? trcv stA') := by
  rcases hmsg : s.msgB n with _ | ⟨ρ, tsnd⟩
  · left
    refine ⟨rfl, ?_⟩
    simpa [oracleRecvA, hmsg] using hz
  · right
    rcases hrecv : scka.recvA s.stA ρ with _ | ⟨key?, trcv, stA'⟩
    · left
      refine ⟨ρ, tsnd, rfl, hrecv, ?_⟩
      simp only [oracleRecvA, bind_pure_comp, StateT.run_bind, StateT.run_get, pure_bind, hmsg,
        hrecv, StateT.run_map, StateT.run_set, map_pure, support_pure,
        Set.mem_singleton_iff] at hz
      exact hz
    · right
      refine ⟨ρ, tsnd, key?, trcv, stA', rfl, hrecv, ?_⟩
      rcases key? with _ | ⟨tI, key⟩ <;>
        simp only [oracleRecvA, bind_pure_comp, StateT.run_bind, StateT.run_get, pure_bind,
          hmsg, hrecv, StateT.run_map, StateT.run_set, map_pure, support_pure,
          Set.mem_singleton_iff] at hz <;>
        subst hz <;>
        rfl

/-- An outcome of `oracleRecvB n` is one of: no recorded message, with the state unchanged; a
failed receive, with `correct` cleared; a successful receive followed by `applyRecvB`. -/
theorem oracleRecvB_run_cases (n : ℕ) (s : GameState StA StB I Rho)
    (z : Option (ℕ × Option ℕ) × GameState StA StB I Rho)
    (hz : z ∈ support ((oracleRecvB scka n).run s)) :
    (s.msgA n = none ∧ z = (none, s)) ∨
    (∃ ρ tsnd, s.msgA n = some (ρ, tsnd) ∧ scka.recvB s.stB ρ = none ∧
      z = (none, { s with correct := false })) ∨
    ∃ ρ tsnd key? trcv stB', s.msgA n = some (ρ, tsnd) ∧
      scka.recvB s.stB ρ = some (key?, trcv, stB') ∧
      z = (some (trcv, key?.map Prod.fst), applyRecvB s tsnd key? trcv stB') := by
  rcases hmsg : s.msgA n with _ | ⟨ρ, tsnd⟩
  · left
    refine ⟨rfl, ?_⟩
    simpa [oracleRecvB, hmsg] using hz
  · right
    rcases hrecv : scka.recvB s.stB ρ with _ | ⟨key?, trcv, stB'⟩
    · left
      refine ⟨ρ, tsnd, rfl, hrecv, ?_⟩
      simp only [oracleRecvB, bind_pure_comp, StateT.run_bind, StateT.run_get, pure_bind, hmsg,
        hrecv, StateT.run_map, StateT.run_set, map_pure, support_pure,
        Set.mem_singleton_iff] at hz
      exact hz
    · right
      refine ⟨ρ, tsnd, key?, trcv, stB', rfl, hrecv, ?_⟩
      rcases key? with _ | ⟨tI, key⟩ <;>
        simp only [oracleRecvB, bind_pure_comp, StateT.run_bind, StateT.run_get, pure_bind,
          hmsg, hrecv, StateT.run_map, StateT.run_set, map_pure, support_pure,
          Set.mem_singleton_iff] at hz <;>
        subst hz <;>
        rfl

/-! ### The send runs as computations

For expected-value arguments the support characterizations are not enough; the send runs are
rewritten as the local send followed by a pure outcome. -/

/-- The game-state outcome of `oracleSendA` for a local send result. -/
def sendAOutcome (s : GameState StA StB I Rho) :
    Option (Option (ℕ × I) × Rho × ℕ × StA) →
      Option (ℕ × Option ℕ × Rho) × GameState StA StB I Rho
  | none => (none, s)
  | some (key?, ρ, tsnd, stA') => (some (tsnd, key?.map Prod.fst, ρ), applySendA s key? ρ tsnd stA')

/-- The game-state outcome of `oracleSendB` for a local send result. -/
def sendBOutcome (s : GameState StA StB I Rho) :
    Option (Option (ℕ × I) × Rho × ℕ × StB) →
      Option (ℕ × Option ℕ × Rho) × GameState StA StB I Rho
  | none => (none, s)
  | some (key?, ρ, tsnd, stB') => (some (tsnd, key?.map Prod.fst, ρ), applySendB s key? ρ tsnd stB')

/-- `oracleSendA` is A's local send followed by `sendAOutcome`. -/
theorem oracleSendA_run_eq (s : GameState StA StB I Rho) :
    (oracleSendA scka ()).run s = scka.sendA s.stA >>= fun out => pure (sendAOutcome s out) := by
  simp only [oracleSendA, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_liftM, bind_assoc]
  refine bind_congr fun out => ?_
  rcases out with _ | ⟨key?, ρ, tsnd, stA'⟩
  · simp [sendAOutcome]
  · rcases key? with _ | ⟨tI, k⟩ <;>
      simp [sendAOutcome, applySendA, StateT.run_set]

/-- `oracleSendB` is B's local send followed by `sendBOutcome`. -/
theorem oracleSendB_run_eq (s : GameState StA StB I Rho) :
    (oracleSendB scka ()).run s = scka.sendB s.stB >>= fun out => pure (sendBOutcome s out) := by
  simp only [oracleSendB, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_liftM, bind_assoc]
  refine bind_congr fun out => ?_
  rcases out with _ | ⟨key?, ρ, tsnd, stB'⟩
  · simp [sendBOutcome]
  · rcases key? with _ | ⟨tI, k⟩ <;>
      simp [sendBOutcome, applySendB, StateT.run_set]

end Send

end SCKAScheme
