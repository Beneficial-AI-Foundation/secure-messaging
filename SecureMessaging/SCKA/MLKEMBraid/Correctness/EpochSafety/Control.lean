/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Correctness.EpochKnowledge

/-!
# Roles and message order in the Braid correctness game

In each epoch one party generates the key pair and the other encapsulates; A generates the key
pairs of the odd epochs. `State.controlPosition` records the role of a state and its step within
the epoch. `ControlInv` states that each party's role matches the parity of its epoch and that
every recorded message fits its sender's role and step (`MessageControl`). `StatePairInv` lists
the pairs of states the two parties can be in. This module proves that every send and receive
oracle preserves `ControlInv`.
-/

open OracleSpec OracleComp
open ErasureCodePayload.Streaming
open SCKAScheme.sckaCorrectnessSpec

namespace MLKEMBraid

variable (P : Parameters ProbComp) {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)

/-- A party's position within its epoch. -/
@[ext] structure ControlPosition where
  /-- `true` in the key-generating states and `false` in the encapsulating states. -/
  isGenerator : Bool
  /-- The step within that role. -/
  step : ℕ
  deriving DecidableEq

/-- The position of a party state within its epoch. -/
def State.controlPosition
    {P : Parameters ProbComp} {AuthState : Type} :
    State P AuthState → ControlPosition
  | .keysUnsampled .. => ⟨true, 0⟩
  | .keysSampled .. => ⟨true, 1⟩
  | .headerSent .. => ⟨true, 2⟩
  | .ct1Received .. => ⟨true, 3⟩
  | .ekSentCt1Received .. => ⟨true, 4⟩
  | .noHeaderReceived .. => ⟨false, 0⟩
  | .headerReceived .. => ⟨false, 1⟩
  | .ct1Sampled .. => ⟨false, 2⟩
  | .ekReceivedCt1Sampled .. => ⟨false, 3⟩
  | .ct1Acknowledged .. => ⟨false, 3⟩
  | .ct2Sampled .. => ⟨false, 4⟩

/-- A message recorded by `party`, whose state is `st`, is well formed, and its epoch is at most
the epoch of `st`. A `hdr`, `ek` or `ekCt1Ack` message comes from the key generator of its epoch,
a `ct1` or `ct2` message from the encapsulator, and no recorded message has type `ct1Ack`. If the
message is from the current epoch of `st`, then `st` has reached the step from which its type is
sent. -/
def MessageControl
    {P : Parameters ProbComp} {AuthState : Type}
    (party : Bool) (st : State P AuthState)
    (msg : Message P.Sym) : Prop :=
  msg.wellFormed = true ∧ msg.epoch ≤ st.epoch ∧
    match msg.type with
    | .none => True
    | .hdr =>
        party = decide (msg.epoch % 2 = 1) ∧
          (msg.epoch = st.epoch → 1 ≤ st.controlPosition.step)
    | .ek =>
        party = decide (msg.epoch % 2 = 1) ∧
          (msg.epoch = st.epoch → 2 ≤ st.controlPosition.step)
    | .ekCt1Ack =>
        party = decide (msg.epoch % 2 = 1) ∧
          (msg.epoch = st.epoch → 3 ≤ st.controlPosition.step)
    | .ct1 =>
        party ≠ decide (msg.epoch % 2 = 1) ∧
          (msg.epoch = st.epoch → 2 ≤ st.controlPosition.step)
    | .ct2 =>
        party ≠ decide (msg.epoch % 2 = 1) ∧
          (msg.epoch = st.epoch → 4 ≤ st.controlPosition.step)
    | .ct1Ack => False

/-- Each party's role matches the parity of its epoch, and every recorded message fits its
sender's role and step. -/
structure ControlInv
    {P : Parameters ProbComp} {AuthState : Type}
    (s : GameState P AuthState) : Prop where
  epochKnowledge : EpochKnowledgeInv s
  recordedReport : RecordedReportInv s
  tcurA_le_sub_one : s.tcurA ≤ s.stA.epoch - 1
  tcurB_le_sub_one : s.tcurB ≤ s.stB.epoch - 1
  /-- Each party's role matches the parity of its epoch, a party whose peer is one epoch ahead is
  in `ct2Sampled`, and every message it recorded satisfies `MessageControl`. -/
  roles : ∀ party : Bool,
    let st := if party then s.stA else s.stB
    let peer := if party then s.stB else s.stA
    let messages := if party then s.msgA else s.msgB
    st.controlPosition.isGenerator = decide (st.epoch % 2 = if party then 1 else 0) ∧
    (peer.epoch = st.epoch + 1 → st.controlPosition = ⟨false, 4⟩) ∧
    ∀ n msg tsnd, messages n = some (msg, tsnd) → MessageControl party st msg

private def ReceiveControlStep
    {P : Parameters ProbComp} {AuthState : Type}
    (st : State P AuthState) (msg : Message P.Sym)
    (st' : State P AuthState) : Prop :=
  (st'.epoch = st.epoch ∧
    st'.controlPosition.isGenerator = st.controlPosition.isGenerator ∧
    st.controlPosition.step ≤ st'.controlPosition.step) ∨
  (st'.epoch = st.epoch + 1 ∧
    st.controlPosition = ⟨true, 4⟩ ∧
    st'.controlPosition = ⟨false, 0⟩ ∧
    msg.type = .ct2 ∧ msg.epoch = st.epoch) ∨
  (st'.epoch = st.epoch + 1 ∧
    st.controlPosition = ⟨false, 4⟩ ∧
    st'.controlPosition = ⟨true, 0⟩ ∧
    msg.epoch = st.epoch + 1)

/-- An encapsulating state at step `4` or later is at step `4`. -/
private theorem controlPosition_eq_false_four
    {P : Parameters ProbComp} {AuthState : Type} (st : State P AuthState)
    (hfirst : st.controlPosition.isGenerator = false) (hfour : 4 ≤ st.controlPosition.step) :
    st.controlPosition = ⟨false, 4⟩ :=
  ControlPosition.ext hfirst (Nat.le_antisymm (by cases st <;> simp [State.controlPosition]) hfour)

private theorem send_control
    (party : Bool) (st : State P AuthState)
    (hrole : st.controlPosition.isGenerator =
      decide (st.epoch % 2 = if party then 1 else 0))
    (r : SendResult P AuthState)
    (hr : r ∈ support (send P auth st)) :
    r.state.epoch = st.epoch ∧
      r.state.controlPosition.isGenerator = st.controlPosition.isGenerator ∧
      st.controlPosition.step ≤ r.state.controlPosition.step ∧
      MessageControl party r.state r.msg := by
  have hparity := Nat.mod_two_eq_zero_or_one st.epoch
  cases st
  case keysUnsampled =>
    simp only [send, mem_support_bind_iff] at hr
    obtain ⟨⟨pk, sk⟩, _, hr⟩ := hr
    simp only [mem_support_pure_iff] at hr
    subst r
    simp only [MessageControl, State.controlPosition, State.epoch,
      Message.wellFormed, Option.isSome, true_and] at hrole hparity ⊢
    rcases hparity with heven | hodd <;>
      cases party <;> simp_all
  case headerReceived =>
    simp only [send, mem_support_bind_iff] at hr
    obtain ⟨⟨encapsState, ct1, key⟩, _, hr⟩ := hr
    simp only [mem_support_pure_iff] at hr
    subst r
    simp only [MessageControl, State.controlPosition, State.epoch,
      Message.wellFormed, Option.isSome, true_and] at hrole hparity ⊢
    rcases hparity with heven | hodd <;>
      cases party <;> simp_all
  all_goals
    simp only [send, mem_support_pure_iff] at hr
    subst r
    simp only [MessageControl, State.controlPosition, State.epoch,
      Message.wellFormed, Option.isSome, Option.isNone, true_and] at hrole hparity ⊢
    rcases hparity with heven | hodd <;>
      cases party <;> simp_all

private theorem receive_control
    [DecidableEq P.Sym]
    (st : State P AuthState) (msg : Message P.Sym)
    (r : RecvResult P AuthState)
    (hr : receive P auth st msg = .ok r) :
    ReceiveControlStep st msg r.state := by
  cases st
  all_goals
    simp only [receive] at hr
    repeat' split at hr
    all_goals cases hr
    all_goals simp_all [ReceiveControlStep, State.epoch, State.controlPosition]

namespace Correctness.Internal

theorem oracleSendA_preserves_controlInv
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (irl : P.kem.IncrementalRandLeak P.inc)
    (sampleInitKey : ProbComp InitKey) :
    QueryImpl.PreservesInv
      (SCKAScheme.oracleSendA (scheme P auth irl sampleInitKey))
      ControlInv := by
  let scka := scheme P auth irl sampleInitKey
  intro t s hs z hz
  cases t
  have hEpoch' : EpochKnowledgeInv z.2 :=
    correctnessImpl_preserves_epochKnowledgeInv P auth irl sampleInitKey
      (OSendA (Rho := Message P.Sym)) s hs.epochKnowledge z hz
  have hReports' : RecordedReportInv z.2 :=
    correctnessImpl_preserves_recordedReportInv P auth irl sampleInitKey
      (OSendA (Rho := Message P.Sym)) s hs.recordedReport z hz
  rcases hs with ⟨hEpoch, hReports, htA, htB, hcontrol⟩
  have hA := hcontrol true
  have hB := hcontrol false
  simp only [if_true] at hA
  simp only [Bool.false_eq_true, ↓reduceIte] at hB
  simp only [SCKAScheme.oracleSendA, scheme, bind_pure_comp, liftM_map, bind_map_left, stateTrun,
    support_bind, Set.mem_iUnion, exists_prop] at hz
  obtain ⟨r, hr, hz⟩ := hz
  rcases send_control P auth true s.stA hA.1 r hr with
    ⟨hepoch, hroleSame, hrank, hnew⟩
  have hfields := send_epoch_fields_of_mem_support P auth s.stA r hr
  have hrole : r.state.controlPosition.isGenerator =
      decide (r.state.epoch % 2 = 1) := by
    rw [hroleSame, hA.1, hepoch]
  have htsend : r.sendingEpoch ≤ r.state.epoch - 1 := by
    have hreport := send_report_eq_of_mem_support P auth s.stA r hr
    omega
  have hfalseFour (hpos : s.stA.controlPosition = ⟨false, 4⟩) :
      r.state.controlPosition = ⟨false, 4⟩ :=
    controlPosition_eq_false_four r.state (by rw [hroleSame, hpos]) (by simpa [hpos] using hrank)
  have hlagA : s.stB.epoch = r.state.epoch + 1 →
      r.state.controlPosition = ⟨false, 4⟩ := by
    intro hpeer
    exact hfalseFour (hA.2.1 (by omega))
  have hlagB : r.state.epoch = s.stB.epoch + 1 →
      s.stB.controlPosition = ⟨false, 4⟩ := by
    intro hpeer
    exact hB.2.1 (by omega)
  have hmsgA : ∀ (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ),
      Function.update s.msgA (s.nA + 1)
          (some (r.msg, r.sendingEpoch)) n = some (msg, tsnd) →
        MessageControl true r.state msg := by
    intro n msg tsnd hn
    by_cases hnewIndex : n = s.nA + 1
    · subst n
      simp only [Function.update_self, Option.some.injEq,
        Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      exact hnew
    · simp only [Function.update_of_ne hnewIndex] at hn
      rcases hA.2.2 n msg tsnd hn with ⟨hwf, hbound, hphase⟩
      refine ⟨hwf, by omega, ?_⟩
      cases htype : msg.type <;> simp only [htype] at hphase ⊢
      all_goals first
        | trivial
        | contradiction
        | (rcases hphase with ⟨howner, holdRank⟩
           refine ⟨howner, ?_⟩
           intro hcurrent
           exact (holdRank (by omega)).trans hrank)
  rcases hkey : r.outputKey with _ | ⟨tI, key⟩
  all_goals
    simp only [hkey, StateT.run_map, StateT.run_set, map_pure,
      support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact ⟨hEpoch', hReports', htsend, htB,
      fun party => by
        cases party
        · simpa [MessageControl] using
            And.intro hB.1 (And.intro hlagB hB.2.2)
        · simpa [MessageControl] using
            And.intro hrole (And.intro hlagA hmsgA)⟩

theorem oracleSendB_preserves_controlInv
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (irl : P.kem.IncrementalRandLeak P.inc)
    (sampleInitKey : ProbComp InitKey) :
    QueryImpl.PreservesInv
      (SCKAScheme.oracleSendB (scheme P auth irl sampleInitKey))
      ControlInv := by
  let scka := scheme P auth irl sampleInitKey
  intro t s hs z hz
  cases t
  have hEpoch' : EpochKnowledgeInv z.2 :=
    correctnessImpl_preserves_epochKnowledgeInv P auth irl sampleInitKey
      (OSendB (Rho := Message P.Sym)) s hs.epochKnowledge z hz
  have hReports' : RecordedReportInv z.2 :=
    correctnessImpl_preserves_recordedReportInv P auth irl sampleInitKey
      (OSendB (Rho := Message P.Sym)) s hs.recordedReport z hz
  rcases hs with ⟨hEpoch, hReports, htA, htB, hcontrol⟩
  have hA := hcontrol true
  have hB := hcontrol false
  simp only [if_true] at hA
  simp only [Bool.false_eq_true, ↓reduceIte] at hB
  simp only [SCKAScheme.oracleSendB, scheme, bind_pure_comp, liftM_map, bind_map_left, stateTrun,
    support_bind, Set.mem_iUnion, exists_prop] at hz
  obtain ⟨r, hr, hz⟩ := hz
  rcases send_control P auth false s.stB hB.1 r hr with
    ⟨hepoch, hroleSame, hrank, hnew⟩
  have hfields := send_epoch_fields_of_mem_support P auth s.stB r hr
  have hrole : r.state.controlPosition.isGenerator =
      decide (r.state.epoch % 2 = 0) := by
    rw [hroleSame, hB.1, hepoch]
  have htsend : r.sendingEpoch ≤ r.state.epoch - 1 := by
    have hreport := send_report_eq_of_mem_support P auth s.stB r hr
    omega
  have hfalseFour (hpos : s.stB.controlPosition = ⟨false, 4⟩) :
      r.state.controlPosition = ⟨false, 4⟩ :=
    controlPosition_eq_false_four r.state (by rw [hroleSame, hpos]) (by simpa [hpos] using hrank)
  have hlagA : r.state.epoch = s.stA.epoch + 1 →
      s.stA.controlPosition = ⟨false, 4⟩ := by
    intro hpeer
    exact hA.2.1 (by omega)
  have hlagB : s.stA.epoch = r.state.epoch + 1 →
      r.state.controlPosition = ⟨false, 4⟩ := by
    intro hpeer
    exact hfalseFour (hB.2.1 (by omega))
  have hmsgB : ∀ (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ),
      Function.update s.msgB (s.nB + 1)
          (some (r.msg, r.sendingEpoch)) n = some (msg, tsnd) →
        MessageControl false r.state msg := by
    intro n msg tsnd hn
    by_cases hnewIndex : n = s.nB + 1
    · subst n
      simp only [Function.update_self, Option.some.injEq,
        Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      exact hnew
    · simp only [Function.update_of_ne hnewIndex] at hn
      rcases hB.2.2 n msg tsnd hn with ⟨hwf, hbound, hphase⟩
      refine ⟨hwf, by omega, ?_⟩
      cases htype : msg.type <;> simp only [htype] at hphase ⊢
      all_goals first
        | trivial
        | contradiction
        | (rcases hphase with ⟨howner, holdRank⟩
           refine ⟨howner, ?_⟩
           intro hcurrent
           exact (holdRank (by omega)).trans hrank)
  rcases hkey : r.outputKey with _ | ⟨tI, key⟩
  all_goals
    simp only [hkey, StateT.run_map, StateT.run_set, map_pure,
      support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact ⟨hEpoch', hReports', htA, htsend,
      fun party => by
        cases party
        · simpa [MessageControl] using
            And.intro hrole (And.intro hlagB hmsgB)
        · simpa [MessageControl] using
            And.intro hA.1 (And.intro hlagA hA.2.2)⟩

theorem oracleRecvA_preserves_controlInv
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (irl : P.kem.IncrementalRandLeak P.inc)
    (sampleInitKey : ProbComp InitKey) :
    QueryImpl.PreservesInv
      (SCKAScheme.oracleRecvA (scheme P auth irl sampleInitKey))
      ControlInv := by
  let scka := scheme P auth irl sampleInitKey
  intro n s hs z hz
  have hEpoch' : EpochKnowledgeInv z.2 :=
    correctnessImpl_preserves_epochKnowledgeInv P auth irl sampleInitKey
      (ORecvA (Rho := Message P.Sym) n) s hs.epochKnowledge z hz
  have hReports' : RecordedReportInv z.2 :=
    correctnessImpl_preserves_recordedReportInv P auth irl sampleInitKey
      (ORecvA (Rho := Message P.Sym) n) s hs.recordedReport z hz
  rcases hs with ⟨hEpoch, hReports, htA, htB, hcontrol⟩
  have hA := hcontrol true
  have hB := hcontrol false
  simp only [if_true] at hA
  simp only [Bool.false_eq_true, ↓reduceIte] at hB
  rcases hentry : s.msgB n with _ | ⟨msg, tsnd⟩
  · simp only [SCKAScheme.oracleRecvA, bind_pure_comp, stateTrun, hentry, support_pure,
      Set.mem_singleton_iff] at hz
    subst z
    exact ⟨hEpoch', hReports', htA, htB, hcontrol⟩
  rcases hrecv : recvSCKA P auth s.stA msg with
    _ | ⟨keyOpt, treport, stA'⟩
  · simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp, stateTrun, hentry, hrecv,
      StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact ⟨hEpoch', hReports', htA, htB, hcontrol⟩
  obtain ⟨r, hraw, hout, hstate, hreport⟩ := recvSCKA_eq_some_iff.mp hrecv
  subst stA'
  have hdelivered := hB.2.2 n msg tsnd hentry
  unfold MessageControl at hdelivered
  have hstep := receive_control P auth s.stA msg r hraw
  have htransition :
      s.stA.epoch ≤ r.state.epoch ∧
      r.state.epoch ≤ s.stA.epoch + 1 ∧
      (r.state.epoch = s.stA.epoch →
        s.stA.controlPosition.step ≤ r.state.controlPosition.step) ∧
      r.state.controlPosition.isGenerator =
        decide (r.state.epoch % 2 = 1) := by
    rcases hstep with hsame | hadvance | hadvance
    · refine ⟨by omega, by omega, fun _ => hsame.2.2, ?_⟩
      rw [hsame.2.1, hA.1, hsame.1]
    · have holdParity : s.stA.epoch % 2 = 1 := by
        by_contra hne
        have hrole := hA.1
        rw [hadvance.2.1] at hrole
        simp [hne] at hrole
      have hnextParity : (s.stA.epoch + 1) % 2 = 0 := by omega
      refine ⟨by omega, by omega, fun h => by omega, ?_⟩
      simp [hadvance.1, hadvance.2.2.1, hnextParity]
    · have holdParity : s.stA.epoch % 2 ≠ 1 := by
        intro heq
        have hrole := hA.1
        rw [hadvance.2.1] at hrole
        simp [heq] at hrole
      have hnextParity : (s.stA.epoch + 1) % 2 = 1 := by omega
      refine ⟨by omega, by omega, fun h => by omega, ?_⟩
      simp [hadvance.1, hadvance.2.2.1, hnextParity]
  have hmsgEpoch : msg.epoch ≤ r.state.epoch := by
    have hcross := hEpoch.epochB_le
    have hcompletedLe := s.stA.completedEpoch_le_epoch
    by_cases hle : msg.epoch ≤ s.stA.epoch
    · exact hle.trans htransition.1
    · have hmsgNext : msg.epoch = s.stA.epoch + 1 := by omega
      have hpeerNext : s.stB.epoch = s.stA.epoch + 1 := by omega
      have hposition := hA.2.1 hpeerNext
      cases hst : s.stA <;>
        simp [hst, State.controlPosition] at hposition
      simp [hst, receive, hdelivered.1, hmsgNext, State.epoch] at hraw
      subst r
      simpa [hst, State.epoch] using hmsgNext.le
  have htA' : max s.tcurA treport ≤ r.state.epoch - 1 := by
    apply Nat.max_le.2
    constructor
    · omega
    · rw [hreport]
      exact Nat.sub_le_sub_right hmsgEpoch 1
  have hmsgA : ∀ (i : ℕ) (oldMsg : Message P.Sym) (oldTsnd : ℕ),
      s.msgA i = some (oldMsg, oldTsnd) →
        MessageControl true r.state oldMsg := by
    intro i oldMsg oldTsnd hi
    rcases hA.2.2 i oldMsg oldTsnd hi with
      ⟨hwell, hbound, hphase⟩
    refine ⟨hwell, by omega, ?_⟩
    cases htype : oldMsg.type <;> simp only [htype] at hphase ⊢
    all_goals first
      | trivial
      | contradiction
      | (rcases hphase with ⟨howner, holdRank⟩
         refine ⟨howner, ?_⟩
         intro hcurrent
         by_cases hsame : r.state.epoch = s.stA.epoch
         · exact (holdRank (by omega)).trans
             (htransition.2.2.1 hsame)
         · omega)
  have hct2
      (htype : msg.type = .ct2)
      (hepoch : msg.epoch = s.stB.epoch) :
      s.stB.controlPosition = ⟨false, 4⟩ := by
    have hphase := hdelivered.2.2
    simp only [htype] at hphase
    have hodd : msg.epoch % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one msg.epoch with hzero | hone
      · simp [hzero] at hphase
      · exact hone
    have hfirst : s.stB.controlPosition.isGenerator = false := by
      rw [hB.1, ← hepoch]
      have hnotZero : msg.epoch % 2 ≠ 0 := by omega
      simp [hnotZero]
    exact controlPosition_eq_false_four s.stB hfirst (hphase.2 hepoch)
  have hcompletedMono :
      s.stA.completedEpoch ≤ r.state.completedEpoch := by
    have hcompleted := receive_completedEpoch_of_eq_ok P auth s.stA
      hEpoch.keyPrefix.posA msg r hraw
    cases hkey : r.outputKey <;> simp only [hkey] at hcompleted
    all_goals omega
  have hcross' : s.stB.epoch ≤ r.state.completedEpoch + 1 := by
    have hold := hEpoch.epochB_le
    omega
  have hpositive : 0 < r.state.epoch :=
    hEpoch.keyPrefix.posA.trans_le htransition.1
  have hlags :
      (s.stB.epoch = r.state.epoch + 1 →
        r.state.controlPosition = ⟨false, 4⟩) ∧
      (r.state.epoch = s.stB.epoch + 1 →
        s.stB.controlPosition = ⟨false, 4⟩) := by
    rcases hstep with hsame | hadvance | hadvance
    · constructor
      · intro hpeer
        have hold := hA.2.1 (by omega)
        apply controlPosition_eq_false_four r.state
        · rw [hsame.2.1, hold]
        · simpa [hold] using hsame.2.2
      · intro hpeer
        exact hB.2.1 (by omega)
    · constructor
      · intro hpeer
        have hcompleted :
            r.state.completedEpoch + 1 = r.state.epoch := by
          cases hrstate : r.state <;>
            simp [hrstate, State.completedEpoch, State.epoch,
              State.controlPosition] at hadvance hpositive ⊢
          all_goals omega
        omega
      · intro hpeer
        exact hct2 hadvance.2.2.2.1 (by omega)
    · constructor
      · intro hpeer
        have hcompleted :
            r.state.completedEpoch + 1 = r.state.epoch := by
          cases hrstate : r.state <;>
            simp [hrstate, State.completedEpoch, State.epoch,
              State.controlPosition] at hadvance hpositive ⊢
          all_goals omega
        omega
      · intro hpeer
        omega
  rcases hkey : keyOpt with _ | ⟨tI, key⟩
  · simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp, stateTrun, hentry, hrecv, hkey,
      StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact ⟨hEpoch', hReports', htA', htB,
      fun party => by
        cases party
        · simpa [MessageControl] using
            And.intro hB.1 (And.intro hlags.2 hB.2.2)
        · simpa [MessageControl] using
            And.intro htransition.2.2.2 (And.intro hlags.1 hmsgA)⟩
  · simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp, stateTrun, hentry, hrecv, hkey,
      StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact ⟨hEpoch', hReports', htA', htB,
      fun party => by
        cases party
        · simpa [MessageControl] using
            And.intro hB.1 (And.intro hlags.2 hB.2.2)
        · simpa [MessageControl] using
            And.intro htransition.2.2.2 (And.intro hlags.1 hmsgA)⟩

theorem oracleRecvB_preserves_controlInv
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (irl : P.kem.IncrementalRandLeak P.inc)
    (sampleInitKey : ProbComp InitKey) :
    QueryImpl.PreservesInv
      (SCKAScheme.oracleRecvB (scheme P auth irl sampleInitKey))
      ControlInv := by
  let scka := scheme P auth irl sampleInitKey
  intro n s hs z hz
  have hEpoch' : EpochKnowledgeInv z.2 :=
    correctnessImpl_preserves_epochKnowledgeInv P auth irl sampleInitKey
      (ORecvB (Rho := Message P.Sym) n) s hs.epochKnowledge z hz
  have hReports' : RecordedReportInv z.2 :=
    correctnessImpl_preserves_recordedReportInv P auth irl sampleInitKey
      (ORecvB (Rho := Message P.Sym) n) s hs.recordedReport z hz
  rcases hs with ⟨hEpoch, hReports, htA, htB, hcontrol⟩
  have hA := hcontrol true
  have hB := hcontrol false
  simp only [if_true] at hA
  simp only [Bool.false_eq_true, ↓reduceIte] at hB
  rcases hentry : s.msgA n with _ | ⟨msg, tsnd⟩
  · simp only [SCKAScheme.oracleRecvB, bind_pure_comp, stateTrun, hentry, support_pure,
      Set.mem_singleton_iff] at hz
    subst z
    exact ⟨hEpoch', hReports', htA, htB, hcontrol⟩
  rcases hrecv : recvSCKA P auth s.stB msg with
    _ | ⟨keyOpt, treport, stB'⟩
  · simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp, stateTrun, hentry, hrecv,
      StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact ⟨hEpoch', hReports', htA, htB, hcontrol⟩
  obtain ⟨r, hraw, hout, hstate, hreport⟩ := recvSCKA_eq_some_iff.mp hrecv
  subst stB'
  have hdelivered := hA.2.2 n msg tsnd hentry
  unfold MessageControl at hdelivered
  have hstep := receive_control P auth s.stB msg r hraw
  have htransition :
      s.stB.epoch ≤ r.state.epoch ∧
      r.state.epoch ≤ s.stB.epoch + 1 ∧
      (r.state.epoch = s.stB.epoch →
        s.stB.controlPosition.step ≤ r.state.controlPosition.step) ∧
      r.state.controlPosition.isGenerator =
        decide (r.state.epoch % 2 = 0) := by
    rcases hstep with hsame | hadvance | hadvance
    · refine ⟨by omega, by omega, fun _ => hsame.2.2, ?_⟩
      rw [hsame.2.1, hB.1, hsame.1]
    · have holdParity : s.stB.epoch % 2 = 0 := by
        by_contra hne
        have hrole := hB.1
        rw [hadvance.2.1] at hrole
        simp [hne] at hrole
      have hnextParity : (s.stB.epoch + 1) % 2 = 1 := by omega
      refine ⟨by omega, by omega, fun h => by omega, ?_⟩
      simp [hadvance.1, hadvance.2.2.1, hnextParity]
    · have holdParity : s.stB.epoch % 2 ≠ 0 := by
        intro heq
        have hrole := hB.1
        rw [hadvance.2.1] at hrole
        simp [heq] at hrole
      have hnextParity : (s.stB.epoch + 1) % 2 = 0 := by omega
      refine ⟨by omega, by omega, fun h => by omega, ?_⟩
      simp [hadvance.1, hadvance.2.2.1, hnextParity]
  have hmsgEpoch : msg.epoch ≤ r.state.epoch := by
    have hcross := hEpoch.epochA_le
    have hcompletedLe := s.stB.completedEpoch_le_epoch
    by_cases hle : msg.epoch ≤ s.stB.epoch
    · exact hle.trans htransition.1
    · have hmsgNext : msg.epoch = s.stB.epoch + 1 := by omega
      have hpeerNext : s.stA.epoch = s.stB.epoch + 1 := by omega
      have hposition := hB.2.1 hpeerNext
      cases hst : s.stB <;>
        simp [hst, State.controlPosition] at hposition
      simp [hst, receive, hdelivered.1, hmsgNext, State.epoch] at hraw
      subst r
      simpa [hst, State.epoch] using hmsgNext.le
  have htB' : max s.tcurB treport ≤ r.state.epoch - 1 := by
    apply Nat.max_le.2
    constructor
    · omega
    · rw [hreport]
      exact Nat.sub_le_sub_right hmsgEpoch 1
  have hmsgB : ∀ (i : ℕ) (oldMsg : Message P.Sym) (oldTsnd : ℕ),
      s.msgB i = some (oldMsg, oldTsnd) →
        MessageControl false r.state oldMsg := by
    intro i oldMsg oldTsnd hi
    rcases hB.2.2 i oldMsg oldTsnd hi with
      ⟨hwell, hbound, hphase⟩
    refine ⟨hwell, by omega, ?_⟩
    cases htype : oldMsg.type <;> simp only [htype] at hphase ⊢
    all_goals first
      | trivial
      | contradiction
      | (rcases hphase with ⟨howner, holdRank⟩
         refine ⟨howner, ?_⟩
         intro hcurrent
         by_cases hsame : r.state.epoch = s.stB.epoch
         · exact (holdRank (by omega)).trans
             (htransition.2.2.1 hsame)
         · omega)
  have hct2
      (htype : msg.type = .ct2)
      (hepoch : msg.epoch = s.stA.epoch) :
      s.stA.controlPosition = ⟨false, 4⟩ := by
    have hphase := hdelivered.2.2
    simp only [htype] at hphase
    have heven : msg.epoch % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one msg.epoch with hzero | hone
      · exact hzero
      · simp [hone] at hphase
    have hfirst : s.stA.controlPosition.isGenerator = false := by
      rw [hA.1, ← hepoch]
      have hnotOne : msg.epoch % 2 ≠ 1 := by omega
      simp [hnotOne]
    exact controlPosition_eq_false_four s.stA hfirst (hphase.2 hepoch)
  have hcompletedMono :
      s.stB.completedEpoch ≤ r.state.completedEpoch := by
    have hcompleted := receive_completedEpoch_of_eq_ok P auth s.stB
      hEpoch.keyPrefix.posB msg r hraw
    cases hkey : r.outputKey <;> simp only [hkey] at hcompleted
    all_goals omega
  have hcross' : s.stA.epoch ≤ r.state.completedEpoch + 1 := by
    have hold := hEpoch.epochA_le
    omega
  have hpositive : 0 < r.state.epoch :=
    hEpoch.keyPrefix.posB.trans_le htransition.1
  have hlags :
      (s.stA.epoch = r.state.epoch + 1 →
        r.state.controlPosition = ⟨false, 4⟩) ∧
      (r.state.epoch = s.stA.epoch + 1 →
        s.stA.controlPosition = ⟨false, 4⟩) := by
    rcases hstep with hsame | hadvance | hadvance
    · constructor
      · intro hpeer
        have hold := hB.2.1 (by omega)
        apply controlPosition_eq_false_four r.state
        · rw [hsame.2.1, hold]
        · simpa [hold] using hsame.2.2
      · intro hpeer
        exact hA.2.1 (by omega)
    · constructor
      · intro hpeer
        have hcompleted :
            r.state.completedEpoch + 1 = r.state.epoch := by
          cases hrstate : r.state <;>
            simp [hrstate, State.completedEpoch, State.epoch,
              State.controlPosition] at hadvance hpositive ⊢
          all_goals omega
        omega
      · intro hpeer
        exact hct2 hadvance.2.2.2.1 (by omega)
    · constructor
      · intro hpeer
        have hcompleted :
            r.state.completedEpoch + 1 = r.state.epoch := by
          cases hrstate : r.state <;>
            simp [hrstate, State.completedEpoch, State.epoch,
              State.controlPosition] at hadvance hpositive ⊢
          all_goals omega
        omega
      · intro hpeer
        omega
  rcases hkey : keyOpt with _ | ⟨tI, key⟩
  · simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp, stateTrun, hentry, hrecv, hkey,
      StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact ⟨hEpoch', hReports', htA, htB',
      fun party => by
        cases party
        · simpa [MessageControl] using
            And.intro htransition.2.2.2 (And.intro hlags.1 hmsgB)
        · simpa [MessageControl] using
            And.intro hA.1 (And.intro hlags.2 hA.2.2)⟩
  · simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp, stateTrun, hentry, hrecv, hkey,
      StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact ⟨hEpoch', hReports', htA, htB',
      fun party => by
        cases party
        · simpa [MessageControl] using
            And.intro htransition.2.2.2 (And.intro hlags.1 hmsgB)
        · simpa [MessageControl] using
            And.intro hA.1 (And.intro hlags.2 hA.2.2)⟩

end Correctness.Internal

/-- The pairs of a key generator's state and an encapsulator's state that can occur at the same
epoch. -/
def AllowedStatePair {P : Parameters ProbComp} {AuthState : Type} :
    State P AuthState → State P AuthState → Prop
  | .keysUnsampled .., .noHeaderReceived .. => True
  | .keysSampled .., .noHeaderReceived .. => True
  | .keysSampled .., .headerReceived .. => True
  | .keysSampled .., .ct1Sampled .. => True
  | .headerSent .., .ct1Sampled .. => True
  | .headerSent .., .ekReceivedCt1Sampled .. => True
  | .ct1Received .., .ct1Sampled .. => True
  | .ct1Received .., .ekReceivedCt1Sampled .. => True
  | .ct1Received .., .ct1Acknowledged .. => True
  | .ct1Received .., .ct2Sampled .. => True
  | .ekSentCt1Received .., .ct2Sampled .. => True
  | _, _ => False

/-- The pairs of party states that can occur together. At equal epochs the key generator and the
encapsulator form an `AllowedStatePair`. When the peer is one epoch ahead, the party is in
`ct2Sampled` and the peer is in `noHeaderReceived`. -/
def StatePairInv
    {P : Parameters ProbComp} {AuthState : Type}
    (s : GameState P AuthState) : Prop :=
  ∀ party : Bool,
    let st := if party then s.stA else s.stB
    let peer := if party then s.stB else s.stA
    (st.epoch = peer.epoch → st.controlPosition.isGenerator = true → AllowedStatePair st peer) ∧
    (peer.epoch = st.epoch + 1 →
      ∃ a enc b dec,
        st = .ct2Sampled st.epoch a enc ∧
        peer = .noHeaderReceived (st.epoch + 1) b dec)

end MLKEMBraid
