/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Correctness
import SecureMessaging.SCKA.MLKEMBraid.Correctness.Edges

/-!
# The oracles of the Braid correctness game

The correctness game of `scheme` runs `send` and `receive`. A send query always succeeds and
writes `SCKAScheme.sendAUpdate` or `sendBUpdate`. A receive query of a recorded message writes
`recvAUpdate` or `recvBUpdate` when `receive` accepts the message and clears the correctness flag
when `receive` refuses it. The lemmas of this module state each query of
`sckaCorrectnessImpl (scheme …)` in these terms, so that a proof about the game reasons about
`SendEdge`, `ReceiveEdge` and the updates.
-/

open OracleComp

namespace MLKEMBraid

variable {P : Parameters ProbComp} [DecidableEq P.EpochKey] [DecidableEq P.Sym]
  {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
  (irl : P.kem.IncrementalRandLeak P.inc) (sampleInitKey : ProbComp InitKey)

/-- The state of the correctness game played by two Braid parties. -/
abbrev GameState (P : Parameters ProbComp) (AuthState : Type) : Type :=
  SCKAScheme.GameState (State P AuthState) (State P AuthState) P.EpochKey (Message P.Sym)

omit [DecidableEq P.EpochKey] in
/-- `recvSCKA` accepts `msg` exactly when `receive` does. It then returns the output key and the
successor state of `receive` and reports `msg.epoch - 1`. -/
theorem recvSCKA_eq_some_iff {st : State P AuthState} {msg : Message P.Sym}
    {keyOpt : Option (ℕ × P.EpochKey)} {treport : ℕ} {st' : State P AuthState} :
    recvSCKA P auth st msg = some (keyOpt, treport, st') ↔
      ∃ r, receive P auth st msg = .ok r ∧
        r.outputKey = keyOpt ∧ r.state = st' ∧ treport = msg.epoch - 1 := by
  cases hraw : receive P auth st msg with
  | error err => simp [recvSCKA, hraw]
  | ok r =>
      simp only [recvSCKA, hraw, Option.some.injEq, Prod.mk.injEq, Except.ok.injEq,
        exists_eq_left']
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h3, h2.symm⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h3.symm, h2⟩

/-- A `SendA` query runs `send` on A's state and maps its result `r` to the response
`(r.sendingEpoch, r.outputKey.map Prod.fst, r.msg)` and the state `sendAUpdate`. -/
theorem oracleSendA_run_eq (s : GameState P AuthState) :
    (SCKAScheme.oracleSendA (scheme P auth irl sampleInitKey) ()).run s =
      (fun r : SendResult P AuthState =>
        (some (r.sendingEpoch, r.outputKey.map Prod.fst, r.msg),
          SCKAScheme.sendAUpdate s r.outputKey r.msg r.sendingEpoch r.state)) <$>
        send P auth s.stA := by
  rw [SCKAScheme.oracleSendA_run_eq]
  simp only [scheme, bind_pure_comp, Functor.map_map]

/-- A `SendB` query runs `send` on B's state and maps its result; the mirror image of
`oracleSendA_run_eq`. -/
theorem oracleSendB_run_eq (s : GameState P AuthState) :
    (SCKAScheme.oracleSendB (scheme P auth irl sampleInitKey) ()).run s =
      (fun r : SendResult P AuthState =>
        (some (r.sendingEpoch, r.outputKey.map Prod.fst, r.msg),
          SCKAScheme.sendBUpdate s r.outputKey r.msg r.sendingEpoch r.state)) <$>
        send P auth s.stB := by
  rw [SCKAScheme.oracleSendB_run_eq]
  simp only [scheme, bind_pure_comp, Functor.map_map]

/-- A `SendA` query runs `send` on A's state. For the result `r` it returns
`(r.sendingEpoch, r.outputKey.map Prod.fst, r.msg)` and writes `sendAUpdate`. -/
theorem mem_support_oracleSendA_run_iff (s : GameState P AuthState)
    (z : Option (ℕ × Option ℕ × Message P.Sym) × GameState P AuthState) :
    z ∈ support ((SCKAScheme.oracleSendA (scheme P auth irl sampleInitKey) ()).run s) ↔
      ∃ r ∈ support (send P auth s.stA),
        z = (some (r.sendingEpoch, r.outputKey.map Prod.fst, r.msg),
          SCKAScheme.sendAUpdate s r.outputKey r.msg r.sendingEpoch r.state) := by
  rw [SCKAScheme.mem_support_oracleSendA_run_iff]
  simp only [scheme, mem_support_bind_iff, mem_support_pure_iff]
  constructor
  · rintro ⟨out, ⟨r, hr, rfl⟩, hz⟩
    exact ⟨r, hr, hz⟩
  · rintro ⟨r, hr, hz⟩
    exact ⟨_, ⟨r, hr, rfl⟩, hz⟩

/-- A `SendB` query runs `send` on B's state; the mirror image of
`mem_support_oracleSendA_run_iff`. -/
theorem mem_support_oracleSendB_run_iff (s : GameState P AuthState)
    (z : Option (ℕ × Option ℕ × Message P.Sym) × GameState P AuthState) :
    z ∈ support ((SCKAScheme.oracleSendB (scheme P auth irl sampleInitKey) ()).run s) ↔
      ∃ r ∈ support (send P auth s.stB),
        z = (some (r.sendingEpoch, r.outputKey.map Prod.fst, r.msg),
          SCKAScheme.sendBUpdate s r.outputKey r.msg r.sendingEpoch r.state) := by
  rw [SCKAScheme.mem_support_oracleSendB_run_iff]
  simp only [scheme, mem_support_bind_iff, mem_support_pure_iff]
  constructor
  · rintro ⟨out, ⟨r, hr, rfl⟩, hz⟩
    exact ⟨r, hr, hz⟩
  · rintro ⟨r, hr, hz⟩
    exact ⟨_, ⟨r, hr, rfl⟩, hz⟩

/-- A `RecvA n` query delivering a recorded message that `receive` accepts with result `r`
returns `(msg.epoch - 1, r.outputKey.map Prod.fst)` and writes `recvAUpdate`. -/
theorem oracleRecvA_run_eq_of_ok {s : GameState P AuthState} {n tsnd : ℕ} {msg : Message P.Sym}
    {r : RecvResult P AuthState} (h : s.msgB n = some (msg, tsnd))
    (hr : receive P auth s.stA msg = .ok r) :
    (SCKAScheme.oracleRecvA (scheme P auth irl sampleInitKey) n).run s =
      pure (some (msg.epoch - 1, r.outputKey.map Prod.fst),
        SCKAScheme.recvAUpdate s tsnd r.outputKey (msg.epoch - 1) r.state) :=
  SCKAScheme.oracleRecvA_run_eq_of_accept _ _ h (by simp [scheme, recvSCKA, hr])

/-- A `RecvA n` query delivering a recorded message that `receive` refuses returns `none` and
clears the correctness flag. -/
theorem oracleRecvA_run_eq_of_error {s : GameState P AuthState} {n tsnd : ℕ}
    {msg : Message P.Sym} {err : Failure} (h : s.msgB n = some (msg, tsnd))
    (hr : receive P auth s.stA msg = .error err) :
    (SCKAScheme.oracleRecvA (scheme P auth irl sampleInitKey) n).run s =
      pure (none, { s with correct := false }) :=
  SCKAScheme.oracleRecvA_run_eq_of_refuse _ _ h (by simp [scheme, recvSCKA, hr])

/-- A `RecvB n` query delivering a recorded message that `receive` accepts with result `r`
returns `(msg.epoch - 1, r.outputKey.map Prod.fst)` and writes `recvBUpdate`. -/
theorem oracleRecvB_run_eq_of_ok {s : GameState P AuthState} {n tsnd : ℕ} {msg : Message P.Sym}
    {r : RecvResult P AuthState} (h : s.msgA n = some (msg, tsnd))
    (hr : receive P auth s.stB msg = .ok r) :
    (SCKAScheme.oracleRecvB (scheme P auth irl sampleInitKey) n).run s =
      pure (some (msg.epoch - 1, r.outputKey.map Prod.fst),
        SCKAScheme.recvBUpdate s tsnd r.outputKey (msg.epoch - 1) r.state) :=
  SCKAScheme.oracleRecvB_run_eq_of_accept _ _ h (by simp [scheme, recvSCKA, hr])

/-- A `RecvB n` query delivering a recorded message that `receive` refuses returns `none` and
clears the correctness flag. -/
theorem oracleRecvB_run_eq_of_error {s : GameState P AuthState} {n tsnd : ℕ}
    {msg : Message P.Sym} {err : Failure} (h : s.msgA n = some (msg, tsnd))
    (hr : receive P auth s.stB msg = .error err) :
    (SCKAScheme.oracleRecvB (scheme P auth irl sampleInitKey) n).run s =
      pure (none, { s with correct := false }) :=
  SCKAScheme.oracleRecvB_run_eq_of_refuse _ _ h (by simp [scheme, recvSCKA, hr])

/-- The three outcomes of a `RecvA n` query: no recorded message `n`, a recorded message that
`receive` refuses, or a recorded message that `receive` accepts. -/
theorem oracleRecvA_run_cases {s : GameState P AuthState} {n : ℕ}
    {z : Option (ℕ × Option ℕ) × GameState P AuthState}
    (hz : z ∈ support ((SCKAScheme.oracleRecvA (scheme P auth irl sampleInitKey) n).run s)) :
    (s.msgB n = none ∧ z = (none, s)) ∨
    (∃ msg tsnd err, s.msgB n = some (msg, tsnd) ∧ receive P auth s.stA msg = .error err ∧
      z = (none, { s with correct := false })) ∨
    (∃ msg tsnd r, s.msgB n = some (msg, tsnd) ∧ receive P auth s.stA msg = .ok r ∧
      z = (some (msg.epoch - 1, r.outputKey.map Prod.fst),
        SCKAScheme.recvAUpdate s tsnd r.outputKey (msg.epoch - 1) r.state)) := by
  rcases hentry : s.msgB n with _ | ⟨msg, tsnd⟩
  · rw [SCKAScheme.oracleRecvA_run_eq_of_none _ _ hentry, mem_support_pure_iff] at hz
    exact Or.inl ⟨rfl, hz⟩
  rcases hraw : receive P auth s.stA msg with err | r
  · rw [oracleRecvA_run_eq_of_error auth irl sampleInitKey hentry hraw, mem_support_pure_iff] at hz
    exact Or.inr (Or.inl ⟨msg, tsnd, err, rfl, hraw, hz⟩)
  · rw [oracleRecvA_run_eq_of_ok auth irl sampleInitKey hentry hraw, mem_support_pure_iff] at hz
    exact Or.inr (Or.inr ⟨msg, tsnd, r, rfl, hraw, hz⟩)

/-- The three outcomes of a `RecvB n` query; the mirror image of `oracleRecvA_run_cases`. -/
theorem oracleRecvB_run_cases {s : GameState P AuthState} {n : ℕ}
    {z : Option (ℕ × Option ℕ) × GameState P AuthState}
    (hz : z ∈ support ((SCKAScheme.oracleRecvB (scheme P auth irl sampleInitKey) n).run s)) :
    (s.msgA n = none ∧ z = (none, s)) ∨
    (∃ msg tsnd err, s.msgA n = some (msg, tsnd) ∧ receive P auth s.stB msg = .error err ∧
      z = (none, { s with correct := false })) ∨
    (∃ msg tsnd r, s.msgA n = some (msg, tsnd) ∧ receive P auth s.stB msg = .ok r ∧
      z = (some (msg.epoch - 1, r.outputKey.map Prod.fst),
        SCKAScheme.recvBUpdate s tsnd r.outputKey (msg.epoch - 1) r.state)) := by
  rcases hentry : s.msgA n with _ | ⟨msg, tsnd⟩
  · rw [SCKAScheme.oracleRecvB_run_eq_of_none _ _ hentry, mem_support_pure_iff] at hz
    exact Or.inl ⟨rfl, hz⟩
  rcases hraw : receive P auth s.stB msg with err | r
  · rw [oracleRecvB_run_eq_of_error auth irl sampleInitKey hentry hraw, mem_support_pure_iff] at hz
    exact Or.inr (Or.inl ⟨msg, tsnd, err, rfl, hraw, hz⟩)
  · rw [oracleRecvB_run_eq_of_ok auth irl sampleInitKey hentry hraw, mem_support_pure_iff] at hz
    exact Or.inr (Or.inr ⟨msg, tsnd, r, rfl, hraw, hz⟩)

end MLKEMBraid
