/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Correctness
import SecureMessaging.SCKA.MLKEMBraid.Construction
import ToVCVio.Control.StateT

/-!
# Reports of recorded messages

The correctness game stores each sent message with the epoch that the send reports, and checks
that the receive of the message reports the same epoch. A Braid send of `msg` reports
`msg.epoch - 1`. `RecordedReportInv` states that every recorded message is stored with this
report, and every oracle of the correctness game preserves it.
-/

open OracleSpec OracleComp

namespace MLKEMBraid

variable (P : Parameters ProbComp) {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)

theorem send_report_eq_of_mem_support
    (st : State P AuthState)
    (r : SendResult P AuthState)
    (hr : r ∈ support (send P auth st)) :
    r.sendingEpoch = r.msg.epoch - 1 := by
  cases st
  case keysUnsampled =>
    simp only [send, mem_support_bind_iff] at hr
    obtain ⟨out, _, hr⟩ := hr
    rcases out with ⟨pk, sk⟩
    simp only [mem_support_pure_iff] at hr
    subst r
    rfl
  case headerReceived =>
    simp only [send, mem_support_bind_iff] at hr
    obtain ⟨out, _, hr⟩ := hr
    rcases out with ⟨encapsState, ct1, k⟩
    simp only [mem_support_pure_iff] at hr
    subst r
    rfl
  all_goals
    simp only [send, mem_support_pure_iff] at hr
    subst r
    rfl

/-- Every recorded message is stored with the report `msg.epoch - 1`. -/
def RecordedReportInv {StA StB I Sym : Type}
    (s : SCKAScheme.GameState StA StB I (Message Sym)) : Prop :=
  (∀ (n : ℕ) (msg : Message Sym) (tsnd : ℕ),
    s.msgA n = some (msg, tsnd) → tsnd = msg.epoch - 1) ∧
  (∀ (n : ℕ) (msg : Message Sym) (tsnd : ℕ),
    s.msgB n = some (msg, tsnd) → tsnd = msg.epoch - 1)

theorem recordedReportInv_initGameState
    {StA StB I Sym : Type}
    (stA : StA) (stB : StB) :
    RecordedReportInv
      (SCKAScheme.initGameState (I := I) (Rho := Message Sym) stA stB) := by
  constructor <;> intro n msg tsnd h <;>
    simp [SCKAScheme.initGameState] at h

theorem correctnessImpl_preserves_recordedReportInv
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (irl : P.kem.IncrementalRandLeak P.inc)
    (sampleInitKey : ProbComp InitKey) :
    QueryImpl.PreservesInv
      (SCKAScheme.sckaCorrectnessImpl
        (scheme P auth irl sampleInitKey))
      RecordedReportInv := by
  let scka := scheme P auth irl sampleInitKey
  have hSendA : QueryImpl.PreservesInv
      (SCKAScheme.oracleSendA scka) RecordedReportInv := by
    intro _ s hs z hz
    have hrecord (r : SendResult P AuthState)
        (hr : r ∈ support (send P auth s.stA)) :
        RecordedReportInv
          {s with
            msgA := Function.update s.msgA (s.nA + 1)
              (some (r.msg, r.sendingEpoch))} := by
      constructor
      · intro n msg tsnd hn
        by_cases hnew : n = s.nA + 1
        · subst n
          simp only [Function.update, ↓reduceDIte, Option.some.injEq,
            Prod.mk.injEq] at hn
          obtain ⟨rfl, rfl⟩ := hn
          exact send_report_eq_of_mem_support P auth s.stA r hr
        · simp only [Function.update, hnew, ↓reduceDIte] at hn
          exact hs.1 n msg tsnd hn
      · exact hs.2
    simp only [SCKAScheme.oracleSendA, scheme, bind_pure_comp, liftM_map, bind_map_left, stateTrun,
      support_bind, Set.mem_iUnion, exists_prop, scka] at hz
    obtain ⟨r, hr, hz⟩ := hz
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩
    all_goals
      simp [hkey, StateT.run_map, StateT.run_set] at hz
      subst z
      simpa [RecordedReportInv] using hrecord r hr
  have hSendB : QueryImpl.PreservesInv
      (SCKAScheme.oracleSendB scka) RecordedReportInv := by
    intro _ s hs z hz
    have hrecord (r : SendResult P AuthState)
        (hr : r ∈ support (send P auth s.stB)) :
        RecordedReportInv
          {s with
            msgB := Function.update s.msgB (s.nB + 1)
              (some (r.msg, r.sendingEpoch))} := by
      constructor
      · exact hs.1
      · intro n msg tsnd hn
        by_cases hnew : n = s.nB + 1
        · subst n
          simp only [Function.update, ↓reduceDIte, Option.some.injEq,
            Prod.mk.injEq] at hn
          obtain ⟨rfl, rfl⟩ := hn
          exact send_report_eq_of_mem_support P auth s.stB r hr
        · simp only [Function.update, hnew, ↓reduceDIte] at hn
          exact hs.2 n msg tsnd hn
    simp only [SCKAScheme.oracleSendB, scheme, bind_pure_comp, liftM_map, bind_map_left, stateTrun,
      support_bind, Set.mem_iUnion, exists_prop, scka] at hz
    obtain ⟨r, hr, hz⟩ := hz
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩
    all_goals
      simp [hkey, StateT.run_map, StateT.run_set] at hz
      subst z
      simpa [RecordedReportInv] using hrecord r hr
  have hRecvA : QueryImpl.PreservesInv
      (SCKAScheme.oracleRecvA scka) RecordedReportInv := by
    intro n s hs z hz
    rcases hentry : s.msgB n with _ | ⟨msg, tsnd⟩
    · have hz' : z = (none, s) := by
        simpa [SCKAScheme.oracleRecvA, hentry, stateTrun] using hz
      subst z
      exact hs
    rcases hrecv : recvSCKA P auth s.stA msg with
      _ | ⟨keyOpt, trcv, stA'⟩
    · have hz' : z = (none, {s with correct := false}) := by
        simpa [SCKAScheme.oracleRecvA, scka, scheme, hentry, hrecv, stateTrun] using hz
      subst z
      simpa [RecordedReportInv] using hs
    rcases hkey : keyOpt with _ | ⟨tI, key⟩
    · have hz' : z =
          (some (trcv, none),
            {s with
              stA := stA'
              tcurA := max s.tcurA trcv
              correct := s.correct && (trcv == tsnd) &&
                (List.range (max s.tcurA trcv + 1)).all
                  (fun t => t = 0 || (s.keyA t).isSome)}) := by
        simpa [SCKAScheme.oracleRecvA, scka, scheme, hentry, hrecv, hkey, stateTrun] using hz
      subst z
      simpa [RecordedReportInv] using hs
    let keyA' := Function.update s.keyA tI (some key)
    have hz' : z =
        (some (trcv, some tI),
          {s with
            stA := stA'
            tcurA := max s.tcurA trcv
            keyA := keyA'
            correct := s.correct && (trcv == tsnd) &&
              (s.keyA tI).isNone &&
              ((s.keyB tI).isNone || s.keyB tI == some key) &&
              (List.range (max s.tcurA trcv + 1)).all
                (fun t => t = 0 || (keyA' t).isSome)}) := by
      simpa [SCKAScheme.oracleRecvA, scka, scheme, hentry, hrecv, hkey, keyA', stateTrun] using hz
    subst z
    simpa [RecordedReportInv] using hs
  have hRecvB : QueryImpl.PreservesInv
      (SCKAScheme.oracleRecvB scka) RecordedReportInv := by
    intro n s hs z hz
    rcases hentry : s.msgA n with _ | ⟨msg, tsnd⟩
    · have hz' : z = (none, s) := by
        simpa [SCKAScheme.oracleRecvB, hentry, stateTrun] using hz
      subst z
      exact hs
    rcases hrecv : recvSCKA P auth s.stB msg with
      _ | ⟨keyOpt, trcv, stB'⟩
    · have hz' : z = (none, {s with correct := false}) := by
        simpa [SCKAScheme.oracleRecvB, scka, scheme, hentry, hrecv, stateTrun] using hz
      subst z
      simpa [RecordedReportInv] using hs
    rcases hkey : keyOpt with _ | ⟨tI, key⟩
    · have hz' : z =
          (some (trcv, none),
            {s with
              stB := stB'
              tcurB := max s.tcurB trcv
              correct := s.correct && (trcv == tsnd) &&
                (List.range (max s.tcurB trcv + 1)).all
                  (fun t => t = 0 || (s.keyB t).isSome)}) := by
        simpa [SCKAScheme.oracleRecvB, scka, scheme, hentry, hrecv, hkey, stateTrun] using hz
      subst z
      simpa [RecordedReportInv] using hs
    let keyB' := Function.update s.keyB tI (some key)
    have hz' : z =
        (some (trcv, some tI),
          {s with
            stB := stB'
            tcurB := max s.tcurB trcv
            keyB := keyB'
            correct := s.correct && (trcv == tsnd) &&
              (s.keyB tI).isNone &&
              ((s.keyA tI).isNone || s.keyA tI == some key) &&
              (List.range (max s.tcurB trcv + 1)).all
                (fun t => t = 0 || (keyB' t).isSome)}) := by
      simpa [SCKAScheme.oracleRecvB, scka, scheme, hentry, hrecv, hkey, keyB', stateTrun] using hz
    subst z
    simpa [RecordedReportInv] using hs
  exact SCKAScheme.sckaCorrectnessImpl_preservesInv hSendA hSendB hRecvA hRecvB

end MLKEMBraid
