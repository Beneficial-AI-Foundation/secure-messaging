/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Correctness
import SecureMessaging.SCKA.MLKEMBraid.Correctness.Edges

/-!
# The oracles of the Braid correctness game

A party is a `Bool`: `true` is A and `false` is B. `s.stateAt party`, `keysAt`, `messagesAt`,
`countAt` and `tcurAt` select the fields of `party` in a game state `s`; `oracleSend party` and
`oracleRecv party` are its queries.

For a send result `r`, `sendUpdate s party r` is the state written by the send query, and
`sendSuccessor s party r` is the same state with the correctness flag of `s`; the two agree when
both flags are true. `recvUpdate` and `recvSuccessor` are the receive analogues.
`oracleSend_run_eq` and `oracleRecv_run_cases` state the responses and successor states of the
queries in these terms.
-/

open OracleComp

namespace MLKEMBraid

variable {P : Parameters ProbComp} {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
  (irl : P.kem.IncrementalRandLeak P.inc) (sampleInitKey : ProbComp InitKey)

/-- The state of the correctness game played by two Braid parties. -/
abbrev GameState (P : Parameters ProbComp) (AuthState : Type) : Type :=
  SCKAScheme.GameState (State P AuthState) (State P AuthState) P.EpochKey (Message P.Sym)

/-! ### Party-indexed state and updates -/

/-- The protocol state of `party`; `true` denotes A and `false` denotes B. -/
def GameState.stateAt (s : GameState P AuthState) (party : Bool) : State P AuthState :=
  if party then s.stA else s.stB

/-- The state of the generator of epoch `e`, the party `decide (e % 2 = 1)`, is A's state if `e` is
odd and B's state otherwise. -/
theorem GameState.stateAt_generator (s : GameState P AuthState) (e : ℕ) :
    s.stateAt (decide (e % 2 = 1)) = if e % 2 = 1 then s.stA else s.stB := by
  simp [GameState.stateAt]

/-- The state of the encapsulator of epoch `e`, the peer of its generator, is B's state if `e` is
odd and A's state otherwise. -/
theorem GameState.stateAt_encapsulator (s : GameState P AuthState) (e : ℕ) :
    s.stateAt (!decide (e % 2 = 1)) = if e % 2 = 1 then s.stB else s.stA := by
  by_cases h : e % 2 = 1 <;> simp [GameState.stateAt, h]

/-- The key table of `party`. -/
def GameState.keysAt (s : GameState P AuthState) (party : Bool) : ℕ → Option P.EpochKey :=
  if party then s.keyA else s.keyB

/-- The messages sent by `party`, each stored with its reported epoch. -/
def GameState.messagesAt (s : GameState P AuthState) (party : Bool) :
    ℕ → Option (Message P.Sym × ℕ) :=
  if party then s.msgA else s.msgB

/-- The number of messages sent by `party`. -/
def GameState.countAt (s : GameState P AuthState) (party : Bool) : ℕ :=
  if party then s.nA else s.nB

/-- The current epoch of `party` in the correctness game. -/
def GameState.tcurAt (s : GameState P AuthState) (party : Bool) : ℕ :=
  if party then s.tcurA else s.tcurB

/-- The game state after `party` sends with result `r`, with the correctness flag of `s`. -/
def sendSuccessor (s : GameState P AuthState) (party : Bool)
    (r : SendResult P AuthState) : GameState P AuthState :=
  if party then
    { s with
      stA := r.state, tcurA := r.sendingEpoch, nA := s.nA + 1,
      msgA := Function.update s.msgA (s.nA + 1) (some (r.msg, r.sendingEpoch)),
      keyA := match r.outputKey with
        | none => s.keyA
        | some (e, key) => Function.update s.keyA e (some key) }
  else
    { s with
      stB := r.state, tcurB := r.sendingEpoch, nB := s.nB + 1,
      msgB := Function.update s.msgB (s.nB + 1) (some (r.msg, r.sendingEpoch)),
      keyB := match r.outputKey with
        | none => s.keyB
        | some (e, key) => Function.update s.keyB e (some key) }

/-- Sending changes only the sender's protocol state. -/
@[simp] theorem stateAt_sendSuccessor (s : GameState P AuthState) (party who : Bool)
    (r : SendResult P AuthState) :
    (sendSuccessor s party r).stateAt who = if who = party then r.state else s.stateAt who := by
  cases party <;> cases who <;> rfl

/-- A send that keeps the sender's epoch keeps every party's epoch. -/
theorem epoch_stateAt_sendSuccessor (s : GameState P AuthState) (party who : Bool)
    (r : SendResult P AuthState) (h : r.state.epoch = (s.stateAt party).epoch) :
    ((sendSuccessor s party r).stateAt who).epoch = (s.stateAt who).epoch := by
  by_cases hwho : who = party
  · subst who; simpa only [stateAt_sendSuccessor, ↓reduceIte] using h
  · simp only [stateAt_sendSuccessor, if_neg hwho]

/-- A send that keeps the sender's completed epoch keeps every party's completed epoch. -/
theorem completedEpoch_stateAt_sendSuccessor (s : GameState P AuthState) (party who : Bool)
    (r : SendResult P AuthState)
    (h : r.state.completedEpoch = (s.stateAt party).completedEpoch) :
    ((sendSuccessor s party r).stateAt who).completedEpoch =
      (s.stateAt who).completedEpoch := by
  by_cases hwho : who = party
  · subst who; simpa only [stateAt_sendSuccessor, ↓reduceIte] using h
  · simp only [stateAt_sendSuccessor, if_neg hwho]

/-- Sending records a new key only in the sender's key table. -/
@[simp] theorem keysAt_sendSuccessor (s : GameState P AuthState) (party who : Bool)
    (r : SendResult P AuthState) :
    (sendSuccessor s party r).keysAt who =
      if who = party then
        match r.outputKey with
        | none => s.keysAt who
        | some (e, key) => Function.update (s.keysAt who) e (some key)
      else s.keysAt who := by
  cases party <;> cases who <;> rfl

/-- Sending appends one message to the sender's message table. -/
@[simp] theorem messagesAt_sendSuccessor (s : GameState P AuthState) (party who : Bool)
    (r : SendResult P AuthState) :
    (sendSuccessor s party r).messagesAt who =
      if who = party then
        Function.update (s.messagesAt who) (s.countAt who + 1) (some (r.msg, r.sendingEpoch))
      else s.messagesAt who := by
  cases party <;> cases who <;> rfl

/-- `sendSuccessor` keeps the correctness flag. -/
@[simp] theorem correct_sendSuccessor (s : GameState P AuthState) (party : Bool)
    (r : SendResult P AuthState) : (sendSuccessor s party r).correct = s.correct := by
  cases party <;> rfl

/-- The game state after `party` receives with result `r` and report `trcv`, with the correctness
flag of `s`. -/
def recvSuccessor (s : GameState P AuthState) (party : Bool)
    (r : RecvResult P AuthState) (trcv : ℕ) : GameState P AuthState :=
  if party then
    { s with
      stA := r.state, tcurA := max s.tcurA trcv,
      keyA := match r.outputKey with
        | none => s.keyA
        | some (e, key) => Function.update s.keyA e (some key) }
  else
    { s with
      stB := r.state, tcurB := max s.tcurB trcv,
      keyB := match r.outputKey with
        | none => s.keyB
        | some (e, key) => Function.update s.keyB e (some key) }

/-- Receiving changes only the receiver's protocol state. -/
@[simp] theorem stateAt_recvSuccessor (s : GameState P AuthState) (party who : Bool)
    (r : RecvResult P AuthState) (trcv : ℕ) :
    (recvSuccessor s party r trcv).stateAt who =
      if who = party then r.state else s.stateAt who := by
  cases party <;> cases who <;> rfl

/-- Receiving records a new key only in the receiver's key table. -/
@[simp] theorem keysAt_recvSuccessor (s : GameState P AuthState) (party who : Bool)
    (r : RecvResult P AuthState) (trcv : ℕ) :
    (recvSuccessor s party r trcv).keysAt who =
      if who = party then
        match r.outputKey with
        | none => s.keysAt who
        | some (e, key) => Function.update (s.keysAt who) e (some key)
      else s.keysAt who := by
  cases party <;> cases who <;> rfl

/-- Receiving keeps both message tables. -/
@[simp] theorem messagesAt_recvSuccessor (s : GameState P AuthState) (party who : Bool)
    (r : RecvResult P AuthState) (trcv : ℕ) :
    (recvSuccessor s party r trcv).messagesAt who = s.messagesAt who := by
  cases party <;> cases who <;> rfl

/-- `recvSuccessor` keeps the correctness flag. -/
@[simp] theorem correct_recvSuccessor (s : GameState P AuthState) (party : Bool)
    (r : RecvResult P AuthState) (trcv : ℕ) :
    (recvSuccessor s party r trcv).correct = s.correct := by
  cases party <;> rfl

variable [DecidableEq P.EpochKey]

/-- The game state written by the send query of `party` for the send result `r`: `sendAUpdate` for A
and `sendBUpdate` for B. -/
def sendUpdate (s : GameState P AuthState) (party : Bool)
    (r : SendResult P AuthState) : GameState P AuthState :=
  if party then SCKAScheme.sendAUpdate s r.outputKey r.msg r.sendingEpoch r.state
  else SCKAScheme.sendBUpdate s r.outputKey r.msg r.sendingEpoch r.state

/-- The send update retains correctness exactly when the input flag is true and the sender's report,
key and prefix checks pass. -/
theorem sendUpdate_correct (s : GameState P AuthState) (party : Bool)
    (r : SendResult P AuthState) :
    (sendUpdate s party r).correct =
      match r.outputKey with
      | none => s.correct && decide (s.tcurAt party ≤ r.sendingEpoch) &&
          SCKAScheme.knownPrefix (s.keysAt party) r.sendingEpoch
      | some (e, key) => s.correct && decide (s.tcurAt party ≤ r.sendingEpoch) &&
          (s.keysAt party e).isNone &&
          ((s.keysAt (!party) e).isNone || s.keysAt (!party) e == some key) &&
          SCKAScheme.knownPrefix (Function.update (s.keysAt party) e (some key))
            r.sendingEpoch := by
  cases party <;> rcases hkey : r.outputKey with _ | ⟨e, key⟩ <;>
    simp [sendUpdate, SCKAScheme.sendAUpdate, SCKAScheme.sendBUpdate, hkey,
      GameState.keysAt, GameState.tcurAt]

/-- The send oracle changes only the sender's protocol state. -/
@[simp] theorem stateAt_sendUpdate (s : GameState P AuthState) (party who : Bool)
    (r : SendResult P AuthState) :
    (sendUpdate s party r).stateAt who = if who = party then r.state else s.stateAt who := by
  cases party <;> cases who <;> rcases hkey : r.outputKey with _ | ⟨e, key⟩ <;>
    simp [sendUpdate, SCKAScheme.sendAUpdate, SCKAScheme.sendBUpdate, hkey, GameState.stateAt]

/-- The send oracle records a new key only in the sender's key table. -/
@[simp] theorem keysAt_sendUpdate (s : GameState P AuthState) (party who : Bool)
    (r : SendResult P AuthState) :
    (sendUpdate s party r).keysAt who =
      if who = party then
        match r.outputKey with
        | none => s.keysAt who
        | some (e, key) => Function.update (s.keysAt who) e (some key)
      else s.keysAt who := by
  cases party <;> cases who <;> rcases hkey : r.outputKey with _ | ⟨e, key⟩ <;>
    simp [sendUpdate, SCKAScheme.sendAUpdate, SCKAScheme.sendBUpdate, hkey, GameState.keysAt]

/-- If `s` and `sendUpdate s party r` both have a true correctness flag, then
`sendUpdate s party r = sendSuccessor s party r`. -/
theorem sendUpdate_eq_successor_of_correct (s : GameState P AuthState) (party : Bool)
    (r : SendResult P AuthState) (hc : s.correct = true)
    (hc' : (sendUpdate s party r).correct = true) :
    sendUpdate s party r = sendSuccessor s party r := by
  cases party <;> rcases hkey : r.outputKey with _ | ⟨e, key⟩ <;>
    simp only [sendUpdate, sendSuccessor, SCKAScheme.sendAUpdate, SCKAScheme.sendBUpdate,
      hkey, Bool.false_eq_true, ↓reduceIte] at hc' ⊢ <;>
    rw [hc', hc]

/-- The game state written by the receive query of `party` for the receive result `r`: `recvAUpdate`
for A and `recvBUpdate` for B. -/
def recvUpdate (s : GameState P AuthState) (party : Bool) (tsnd : ℕ)
    (r : RecvResult P AuthState) (trcv : ℕ) : GameState P AuthState :=
  if party then SCKAScheme.recvAUpdate s tsnd r.outputKey trcv r.state
  else SCKAScheme.recvBUpdate s tsnd r.outputKey trcv r.state

/-- The receive update retains correctness exactly when the input flag is true and the receiver's
report, key and prefix checks pass. -/
theorem recvUpdate_correct (s : GameState P AuthState) (party : Bool) (tsnd : ℕ)
    (r : RecvResult P AuthState) (trcv : ℕ) :
    (recvUpdate s party tsnd r trcv).correct =
      match r.outputKey with
      | none => s.correct && (trcv == tsnd) &&
          SCKAScheme.knownPrefix (s.keysAt party) (max (s.tcurAt party) trcv)
      | some (e, key) => s.correct && (trcv == tsnd) && (s.keysAt party e).isNone &&
          ((s.keysAt (!party) e).isNone || s.keysAt (!party) e == some key) &&
          SCKAScheme.knownPrefix (Function.update (s.keysAt party) e (some key))
            (max (s.tcurAt party) trcv) := by
  cases party <;> rcases hkey : r.outputKey with _ | ⟨e, key⟩ <;>
    simp [recvUpdate, SCKAScheme.recvAUpdate, SCKAScheme.recvBUpdate, hkey,
      GameState.keysAt, GameState.tcurAt]

/-- The receive oracle changes only the receiver's protocol state. -/
@[simp] theorem stateAt_recvUpdate (s : GameState P AuthState) (party who : Bool) (tsnd : ℕ)
    (r : RecvResult P AuthState) (trcv : ℕ) :
    (recvUpdate s party tsnd r trcv).stateAt who =
      if who = party then r.state else s.stateAt who := by
  cases party <;> cases who <;> rcases hkey : r.outputKey with _ | ⟨e, key⟩ <;>
    simp [recvUpdate, SCKAScheme.recvAUpdate, SCKAScheme.recvBUpdate, hkey, GameState.stateAt]

/-- If `s` and `recvUpdate s party tsnd r trcv` both have a true correctness flag, then the update
equals `recvSuccessor s party r trcv`. -/
theorem recvUpdate_eq_successor_of_correct (s : GameState P AuthState) (party : Bool) (tsnd : ℕ)
    (r : RecvResult P AuthState) (trcv : ℕ) (hc : s.correct = true)
    (hc' : (recvUpdate s party tsnd r trcv).correct = true) :
    recvUpdate s party tsnd r trcv = recvSuccessor s party r trcv := by
  cases party <;> rcases hkey : r.outputKey with _ | ⟨e, key⟩ <;>
    simp only [recvUpdate, recvSuccessor, SCKAScheme.recvAUpdate, SCKAScheme.recvBUpdate,
      hkey, Bool.false_eq_true, ↓reduceIte] at hc' ⊢ <;>
    rw [hc', hc]

variable [DecidableEq P.Sym]

/-- The correctness game's send query for `party`; `true` denotes A and `false` denotes B. -/
abbrev oracleSend (party : Bool) :=
  if party then SCKAScheme.oracleSendA (scheme P auth irl sampleInitKey)
  else SCKAScheme.oracleSendB (scheme P auth irl sampleInitKey)

/-- The correctness game's receive query for `party`; `true` denotes A and `false` denotes B. -/
abbrev oracleRecv (party : Bool) :=
  if party then SCKAScheme.oracleRecvA (scheme P auth irl sampleInitKey)
  else SCKAScheme.oracleRecvB (scheme P auth irl sampleInitKey)

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

/-- The version of `oracleSendA_run_eq` for B. -/
theorem oracleSendB_run_eq (s : GameState P AuthState) :
    (SCKAScheme.oracleSendB (scheme P auth irl sampleInitKey) ()).run s =
      (fun r : SendResult P AuthState =>
        (some (r.sendingEpoch, r.outputKey.map Prod.fst, r.msg),
          SCKAScheme.sendBUpdate s r.outputKey r.msg r.sendingEpoch r.state)) <$>
        send P auth s.stB := by
  rw [SCKAScheme.oracleSendB_run_eq]
  simp only [scheme, bind_pure_comp, Functor.map_map]

/-- The support characterization corresponding to `oracleSendA_run_eq`. -/
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

/-- The version of `mem_support_oracleSendA_run_iff` for B. -/
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

/-- The send query of `party` runs `send` on the state of `party` and writes `sendUpdate`. -/
theorem oracleSend_run_eq (s : GameState P AuthState) (party : Bool) :
    (oracleSend auth irl sampleInitKey party ()).run s =
      (fun r : SendResult P AuthState =>
        (some (r.sendingEpoch, r.outputKey.map Prod.fst, r.msg), sendUpdate s party r)) <$>
        send P auth (s.stateAt party) := by
  cases party
  · simpa only [oracleSend, Bool.false_eq_true, ↓reduceIte, sendUpdate, GameState.stateAt] using
      oracleSendB_run_eq auth irl sampleInitKey s
  · simpa only [oracleSend, ↓reduceIte, sendUpdate, GameState.stateAt] using
      oracleSendA_run_eq auth irl sampleInitKey s

/-- Send-query outcomes are exactly the responses and `sendUpdate` states of supported sends by
`party`. -/
theorem mem_support_oracleSend_run_iff (s : GameState P AuthState) (party : Bool)
    (z : Option (ℕ × Option ℕ × Message P.Sym) × GameState P AuthState) :
    z ∈ support ((oracleSend auth irl sampleInitKey party ()).run s) ↔
      ∃ r ∈ support (send P auth (s.stateAt party)),
        z = (some (r.sendingEpoch, r.outputKey.map Prod.fst, r.msg), sendUpdate s party r) := by
  rw [oracleSend_run_eq auth irl sampleInitKey, support_map, Set.mem_image]
  exact exists_congr fun r => and_congr_right fun _ => eq_comm

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

/-- The version of `oracleRecvA_run_eq_of_ok` for B. -/
theorem oracleRecvB_run_eq_of_ok {s : GameState P AuthState} {n tsnd : ℕ} {msg : Message P.Sym}
    {r : RecvResult P AuthState} (h : s.msgA n = some (msg, tsnd))
    (hr : receive P auth s.stB msg = .ok r) :
    (SCKAScheme.oracleRecvB (scheme P auth irl sampleInitKey) n).run s =
      pure (some (msg.epoch - 1, r.outputKey.map Prod.fst),
        SCKAScheme.recvBUpdate s tsnd r.outputKey (msg.epoch - 1) r.state) :=
  SCKAScheme.oracleRecvB_run_eq_of_accept _ _ h (by simp [scheme, recvSCKA, hr])

/-- The version of `oracleRecvA_run_eq_of_error` for B. -/
theorem oracleRecvB_run_eq_of_error {s : GameState P AuthState} {n tsnd : ℕ}
    {msg : Message P.Sym} {err : Failure} (h : s.msgA n = some (msg, tsnd))
    (hr : receive P auth s.stB msg = .error err) :
    (SCKAScheme.oracleRecvB (scheme P auth irl sampleInitKey) n).run s =
      pure (none, { s with correct := false }) :=
  SCKAScheme.oracleRecvB_run_eq_of_refuse _ _ h (by simp [scheme, recvSCKA, hr])

/-- A `RecvA n` query finds no recorded message `n` and leaves the state unchanged, or delivers one
that `receive` refuses and clears the correctness flag, or delivers one that `receive` accepts and
writes `recvAUpdate`. -/
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

/-- The version of `oracleRecvA_run_cases` for B. -/
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

/-- The receive query of `party` finds no recorded message, or delivers one that `receive` refuses
and clears the correctness flag, or delivers one that `receive` accepts and writes `recvUpdate`. -/
theorem oracleRecv_run_cases {s : GameState P AuthState} (party : Bool) {n : ℕ}
    {z : Option (ℕ × Option ℕ) × GameState P AuthState}
    (hz : z ∈ support ((oracleRecv auth irl sampleInitKey party n).run s)) :
    (s.messagesAt (!party) n = none ∧ z = (none, s)) ∨
    (∃ msg tsnd err, s.messagesAt (!party) n = some (msg, tsnd) ∧
      receive P auth (s.stateAt party) msg = .error err ∧
      z = (none, { s with correct := false })) ∨
    (∃ msg tsnd r, s.messagesAt (!party) n = some (msg, tsnd) ∧
      receive P auth (s.stateAt party) msg = .ok r ∧
      z = (some (msg.epoch - 1, r.outputKey.map Prod.fst),
        recvUpdate s party tsnd r (msg.epoch - 1))) := by
  cases party
  · simpa only [oracleRecv, Bool.not_false, Bool.false_eq_true, ↓reduceIte, GameState.messagesAt,
      GameState.stateAt, recvUpdate] using oracleRecvB_run_cases auth irl sampleInitKey hz
  · simpa only [oracleRecv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, GameState.messagesAt,
      GameState.stateAt, recvUpdate] using oracleRecvA_run_cases auth irl sampleInitKey hz

end MLKEMBraid
