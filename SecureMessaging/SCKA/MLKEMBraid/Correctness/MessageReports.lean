/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.MLKEMBraid.Correctness.Oracles

/-!
# Reports of recorded messages

The correctness game stores each sent message with the epoch that the send reports, and checks
that the receive of the message reports the same epoch. A send edge with message `msg` reports
`msg.epoch - 1`. `RecordedReportInv` states that every recorded message is stored with this
report. Every send edge and every receive of either party preserves it.
-/

@[expose] public section

open OracleSpec OracleComp

namespace Braid

variable {P : Parameters ProbComp} {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)

/-- Every recorded message is stored with the report `msg.epoch - 1`. -/
structure RecordedReportInv {StA StB I Sym : Type}
    (s : SCKAScheme.GameState StA StB I (Message Sym)) : Prop where
  /-- Every message of A is stored with the report `msg.epoch - 1`. -/
  msgA : ∀ (n : ℕ) (msg : Message Sym) (tsnd : ℕ),
    s.msgA n = some (msg, tsnd) → tsnd = msg.epoch - 1
  /-- Every message of B is stored with the report `msg.epoch - 1`. -/
  msgB : ∀ (n : ℕ) (msg : Message Sym) (tsnd : ℕ),
    s.msgB n = some (msg, tsnd) → tsnd = msg.epoch - 1

/-- A message recorded by either party carries the report `msg.epoch - 1`. -/
theorem RecordedReportInv.report {s : GameState P AuthState} (hs : RecordedReportInv s)
    (party : Bool) (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ)
    (hentry : s.messagesAt party n = some (msg, tsnd)) : tsnd = msg.epoch - 1 := by
  cases party; exacts [hs.msgB n msg tsnd hentry, hs.msgA n msg tsnd hentry]

/-- The initial game state has no recorded message. -/
theorem recordedReportInv_initGameState {StA StB I Sym : Type} (stA : StA) (stB : StB) :
    RecordedReportInv (SCKAScheme.initGameState (I := I) (Rho := Message Sym) stA stB) := by
  constructor <;> intro n msg tsnd h <;> simp [SCKAScheme.initGameState] at h

variable [DecidableEq P.EpochKey]

/-- A send edge from the state of `party` records its message with the report `msg.epoch - 1`, so
`RecordedReportInv` is preserved. -/
theorem recordedReportInv_sendUpdate {s : GameState P AuthState} (hs : RecordedReportInv s)
    (party : Bool) {r : SendResult P AuthState} (hedge : SendEdge auth (s.stateAt party) r) :
    RecordedReportInv (sendUpdate s party r) := by
  have hreport : r.sendingEpoch = r.msg.epoch - 1 := by
    rw [hedge.sendingEpoch_eq, hedge.epoch_eq.2]
  cases party
  · simp only [sendUpdate, Bool.false_eq_true, ↓reduceIte]
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩
    all_goals
      refine ⟨hs.msgA, fun n msg tsnd hn => ?_⟩
      simp only [SCKAScheme.sendBUpdate] at hn
      by_cases hnew : n = s.nB + 1
      · subst hnew
        rw [Function.update_self] at hn
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
        exact hreport
      · rw [Function.update_of_ne hnew] at hn
        exact hs.msgB n msg tsnd hn
  · simp only [sendUpdate, ↓reduceIte]
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩
    all_goals
      refine ⟨fun n msg tsnd hn => ?_, hs.msgB⟩
      simp only [SCKAScheme.sendAUpdate] at hn
      by_cases hnew : n = s.nA + 1
      · subst hnew
        rw [Function.update_self] at hn
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
        exact hreport
      · rw [Function.update_of_ne hnew] at hn
        exact hs.msgA n msg tsnd hn

/-- A receive leaves the recorded messages unchanged, so `RecordedReportInv` is preserved. -/
theorem recordedReportInv_recvUpdate {s : GameState P AuthState} (hs : RecordedReportInv s)
    (party : Bool) (tsnd : ℕ) (r : RecvResult P AuthState) (trcv : ℕ) :
    RecordedReportInv (recvUpdate s party tsnd r trcv) := by
  cases party <;> simp only [recvUpdate, Bool.false_eq_true, ↓reduceIte] <;>
    rcases r.outputKey with _ | ⟨tI, key⟩ <;> exact ⟨hs.msgA, hs.msgB⟩

end Braid
