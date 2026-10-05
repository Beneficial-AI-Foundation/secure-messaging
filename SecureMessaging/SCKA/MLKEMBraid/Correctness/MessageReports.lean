/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Correctness.Oracles

/-!
# Reports of recorded messages

The correctness game stores each sent message with the epoch that the send reports, and checks
that the receive of the message reports the same epoch. A Braid send of `msg` reports
`msg.epoch - 1`. `RecordedReportInv` states that every recorded message is stored with this
report, and every oracle of the correctness game preserves it.
-/

open OracleSpec OracleComp

namespace MLKEMBraid

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

/-- Every oracle of the correctness game preserves `RecordedReportInv`. -/
theorem correctnessImpl_preserves_recordedReportInv
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (irl : P.kem.IncrementalRandLeak P.inc) (sampleInitKey : ProbComp InitKey) :
    QueryImpl.PreservesInv
      (SCKAScheme.sckaCorrectnessImpl (scheme P auth irl sampleInitKey)) RecordedReportInv := by
  refine SCKAScheme.sckaCorrectnessImpl_preservesInv _ ?_ ?_ ?_ ?_
  -- Sends record one message with the report `msg.epoch - 1`.
  · intro _ s hs z hz
    obtain ⟨r, hr, rfl⟩ := (mem_support_oracleSendA_run_iff auth irl sampleInitKey s z).mp hz
    have hedge := (mem_support_send_iff auth).mp hr
    have hreport : r.sendingEpoch = r.msg.epoch - 1 := by
      rw [hedge.sendingEpoch_eq, hedge.epoch_eq.2]
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
  · intro _ s hs z hz
    obtain ⟨r, hr, rfl⟩ := (mem_support_oracleSendB_run_iff auth irl sampleInitKey s z).mp hz
    have hedge := (mem_support_send_iff auth).mp hr
    have hreport : r.sendingEpoch = r.msg.epoch - 1 := by
      rw [hedge.sendingEpoch_eq, hedge.epoch_eq.2]
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
  -- Receives leave the recorded messages unchanged.
  · intro n s hs z hz
    rcases oracleRecvA_run_cases auth irl sampleInitKey hz with
      ⟨-, rfl⟩ | ⟨msg, tsnd, err, -, -, rfl⟩ | ⟨msg, tsnd, r, -, -, rfl⟩
    · exact hs
    · exact ⟨hs.msgA, hs.msgB⟩
    · rcases r.outputKey with _ | ⟨tI, key⟩ <;> exact ⟨hs.msgA, hs.msgB⟩
  · intro n s hs z hz
    rcases oracleRecvB_run_cases auth irl sampleInitKey hz with
      ⟨-, rfl⟩ | ⟨msg, tsnd, err, -, -, rfl⟩ | ⟨msg, tsnd, r, -, -, rfl⟩
    · exact hs
    · exact ⟨hs.msgA, hs.msgB⟩
    · rcases r.outputKey with _ | ⟨tI, key⟩ <;> exact ⟨hs.msgA, hs.msgB⟩

end MLKEMBraid
