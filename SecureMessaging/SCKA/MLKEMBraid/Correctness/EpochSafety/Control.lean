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
every recorded message fits its sender's role and step (`MessageControl`). This module proves
that every send and receive oracle preserves `ControlInv`.
-/

open OracleSpec OracleComp
open SCKAScheme.sckaCorrectnessSpec

namespace MLKEMBraid

/-- A lower bound on the step of the sender's control position after it sends a message of this
type. -/
def MessageType.sendStep : MessageType → ℕ
  | .none | .ct1Ack => 0
  | .hdr => 1
  | .ek | .ct1 => 2
  | .ekCt1Ack => 3
  | .ct2 => 4

/-- `party` owns `msg` if it may send a message of that type and epoch: the generator of
`msg.epoch` sends `hdr`, `ek` and `ekCt1Ack`, the other party sends `ct1` and `ct2`, either party
sends empty messages, and no party sends `ct1Ack`. -/
def MessageOwner {Sym : Type} (party : Bool) (msg : Message Sym) : Prop :=
  match msg.type with
  | .none => True
  | .hdr | .ek | .ekCt1Ack => party = decide (msg.epoch % 2 = 1)
  | .ct1 | .ct2 => party ≠ decide (msg.epoch % 2 = 1)
  | .ct1Ack => False

/-- `MessageControl party st msg` holds if `msg` is well-formed, `party` owns it,
`msg.epoch ≤ st.epoch`, and, when `msg.epoch = st.epoch`, `st` is at least at step
`msg.type.sendStep`. -/
def MessageControl {P : Parameters ProbComp} {AuthState : Type}
    (party : Bool) (st : State P AuthState) (msg : Message P.Sym) : Prop :=
  msg.wellFormed = true ∧ msg.epoch ≤ st.epoch ∧
    (msg.epoch = st.epoch → msg.type.sendStep ≤ st.controlPosition.step) ∧
    MessageOwner party msg

/-- `PartyControl party s` holds if the state `st` of `party` is key-generating exactly when
`party` generates the key pair of `st.epoch`, `st` is in `ct2Sampled` when the peer is one epoch
ahead, and every message recorded by `party` satisfies `MessageControl` for `st`. -/
def PartyControl {P : Parameters ProbComp} {AuthState : Type}
    (party : Bool) (s : GameState P AuthState) : Prop :=
  let st := s.stateAt party
  let peer := s.stateAt (!party)
  let messages := s.messagesAt party
  st.controlPosition.isGenerator = decide (st.epoch % 2 = if party then 1 else 0) ∧
    (peer.epoch = st.epoch + 1 → st.controlPosition = ⟨false, 4⟩) ∧
    ∀ n msg tsnd, messages n = some (msg, tsnd) → MessageControl party st msg

/-- The control invariant of a game state: the epoch and report invariants, each party's current
game epoch at most its epoch minus one, and `PartyControl` for both parties. -/
structure ControlInv {P : Parameters ProbComp} {AuthState : Type}
    (s : GameState P AuthState) : Prop where
  /-- `EpochKnowledgeInv` holds. -/
  epochKnowledge : EpochKnowledgeInv s
  /-- Every recorded message is stored with the report `msg.epoch - 1`. -/
  recordedReport : RecordedReportInv s
  /-- A's current game epoch is at most A's epoch minus one. -/
  tcurA_le_sub_one : s.tcurA ≤ s.stA.epoch - 1
  /-- B's current game epoch is at most B's epoch minus one. -/
  tcurB_le_sub_one : s.tcurB ≤ s.stB.epoch - 1
  /-- `PartyControl` holds for both parties. -/
  roles : ∀ party : Bool, PartyControl party s

variable {P : Parameters ProbComp} {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)

/-- Each party's current game epoch is at most its epoch minus one. -/
theorem ControlInv.tcur_le_sub_one {s : GameState P AuthState} (hs : ControlInv s)
    (party : Bool) : s.tcurAt party ≤ (s.stateAt party).epoch - 1 := by
  cases party; exacts [hs.tcurB_le_sub_one, hs.tcurA_le_sub_one]

/-- Each party is key-generating exactly when it generates the key pair of its epoch. -/
theorem ControlInv.role {s : GameState P AuthState} (hs : ControlInv s) (party : Bool) :
    (s.stateAt party).controlPosition.isGenerator =
      decide ((s.stateAt party).epoch % 2 = if party then 1 else 0) := by
  exact (hs.roles party).1

/-- Each party's current game epoch is at most its epoch minus one, and the party has a key for
every epoch from `1` to its epoch minus one. -/
theorem ControlInv.send_prefix {s : GameState P AuthState} (hs : ControlInv s) (party : Bool) :
    s.tcurAt party ≤ (s.stateAt party).epoch - 1 ∧
      ∀ t, 0 < t → t ≤ (s.stateAt party).epoch - 1 → s.keysAt party t ≠ none := by
  exact ⟨hs.tcur_le_sub_one party, fun t h0 hle => (hs.epochKnowledge.keyPrefix.keys party t).2
    ⟨h0, hle.trans (s.stateAt party).epoch_sub_one_le_completedEpoch⟩⟩

/-- If `st` is key-generating exactly when `party` generates the key pair of `st.epoch`, a send
from `st` emits a message satisfying `MessageControl party` for the successor state. -/
theorem SendEdge.messageControl (party : Bool) {st : State P AuthState}
    {r : SendResult P AuthState} (hedge : SendEdge auth st r)
    (hrole : st.controlPosition.isGenerator = decide (st.epoch % 2 = if party then 1 else 0)) :
    MessageControl party r.state r.msg := by
  have hparity := Nat.mod_two_eq_zero_or_one st.epoch
  cases hedge <;>
    simp only [MessageControl, MessageOwner, MessageType.sendStep, Message.wellFormed,
      State.controlPosition, State.epoch, Option.isSome, Option.isNone, true_and]
      at hrole hparity ⊢ <;>
    rcases hparity with h | h <;> cases party <;> simp_all

/-- A send preserves the three conditions of `PartyControl` for the sender, with the sent message
recorded at any index `k`. -/
theorem partyControl_send (party : Bool) {st peer : State P AuthState}
    {messages : ℕ → Option (Message P.Sym × ℕ)} {r : SendResult P AuthState}
    (hedge : SendEdge auth st r)
    (hrole : st.controlPosition.isGenerator = decide (st.epoch % 2 = if party then 1 else 0))
    (hlag : peer.epoch = st.epoch + 1 → st.controlPosition = ⟨false, 4⟩)
    (hmsgs : ∀ n msg tsnd, messages n = some (msg, tsnd) → MessageControl party st msg)
    (k : ℕ) :
    r.state.controlPosition.isGenerator = decide (r.state.epoch % 2 = if party then 1 else 0) ∧
      (peer.epoch = r.state.epoch + 1 → r.state.controlPosition = ⟨false, 4⟩) ∧
      ∀ n msg tsnd, Function.update messages k (some (r.msg, r.sendingEpoch)) n = some (msg, tsnd) →
        MessageControl party r.state msg := by
  obtain ⟨hep, -⟩ := hedge.epoch_eq
  obtain ⟨hgen, hstep⟩ := hedge.controlPosition
  refine ⟨by rw [hgen, hrole, hep], fun hpeer => ?_, fun n msg tsnd hn => ?_⟩
  · have h := hlag (by omega)
    refine ControlPosition.ext (by rw [hgen, h]) (le_antisymm r.state.controlPosition_step_le ?_)
    rw [h] at hstep
    exact hstep
  · by_cases hnew : n = k
    · subst hnew
      rw [Function.update_self] at hn
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
      exact hedge.messageControl auth party hrole
    · rw [Function.update_of_ne hnew] at hn
      obtain ⟨hwf, hle, hcur, howner⟩ := hmsgs n msg tsnd hn
      exact ⟨hwf, by omega, fun h => (hcur (by omega)).trans hstep, howner⟩

/-- Accepting a message recorded by the peer preserves the `ct2Sampled` conditions of both parties
and the receiver's role and `MessageControl` conditions, and the receiver's new current game epoch
`max tcur (msg.epoch - 1)` is at most its new epoch minus one. -/
theorem partyControl_receive [DecidableEq P.Sym] (party : Bool) {st peer : State P AuthState}
    {messages : ℕ → Option (Message P.Sym × ℕ)} {msg : Message P.Sym}
    {r : RecvResult P AuthState} {tcur : ℕ}
    (hraw : receive P auth st msg = .ok r)
    (hrole : st.controlPosition.isGenerator = decide (st.epoch % 2 = if party then 1 else 0))
    (hroleP : peer.controlPosition.isGenerator =
      decide (peer.epoch % 2 = if party then 0 else 1))
    (hlag : peer.epoch = st.epoch + 1 → st.controlPosition = ⟨false, 4⟩)
    (hlagP : st.epoch = peer.epoch + 1 → peer.controlPosition = ⟨false, 4⟩)
    (hmsgs : ∀ n m t, messages n = some (m, t) → MessageControl party st m)
    (hdelivered : MessageControl (!party) peer msg)
    (hpos : 0 < st.epoch) (hcrossP : peer.epoch ≤ st.completedEpoch + 1)
    (htcur : tcur ≤ st.epoch - 1) :
    r.state.controlPosition.isGenerator = decide (r.state.epoch % 2 = if party then 1 else 0) ∧
      (peer.epoch = r.state.epoch + 1 → r.state.controlPosition = ⟨false, 4⟩) ∧
      (∀ n m t, messages n = some (m, t) → MessageControl party r.state m) ∧
      (r.state.epoch = peer.epoch + 1 → peer.controlPosition = ⟨false, 4⟩) ∧
      max tcur (msg.epoch - 1) ≤ r.state.epoch - 1 := by
  have hedge := ReceiveEdge.of_eq_ok auth hraw
  obtain ⟨hwf, hle, hstepP, howner⟩ := hdelivered
  obtain ⟨hepLe, hepLe'⟩ := hedge.epoch_le
  have hcomp := st.completedEpoch_le_epoch
  have hρ : (if party then 1 else 0 : ℕ) ≤ 1 := by cases party <;> simp
  have hρ' : (if party then 0 else 1 : ℕ) = 1 - if party then 1 else 0 := by cases party <;> simp
  -- The delivered message is at most at the receiver's new epoch: a message of the next epoch
  -- means the peer is ahead, so the receiver is in `ct2Sampled` and advances.
  have hmsgEpoch : msg.epoch ≤ r.state.epoch := by
    by_cases h : msg.epoch ≤ st.epoch
    · exact h.trans hepLe
    · have hnext : msg.epoch = st.epoch + 1 := by omega
      obtain ⟨a, enc, hst⟩ := st.eq_ct2Sampled_of_controlPosition (hlag (by omega))
      obtain ⟨e, he⟩ : ∃ e, st.epoch = e := ⟨_, rfl⟩
      rw [he] at hst
      subst hst
      simp only [State.epoch] at hnext
      rw [receive_ct2Sampled_of_epoch_succ auth hwf hnext] at hraw
      cases hraw
      simp only [State.epoch]
      omega
  rcases hedge.epoch_eq_or_succ with ⟨-, heq⟩ | hsucc
  · -- The receiver stays in its epoch: the role is unchanged and the step does not decrease.
    obtain ⟨hgen, hstep⟩ := hedge.controlPosition_of_epoch_eq heq
    refine ⟨by rw [hgen, hrole, heq], fun hpeer => ?_, fun n m t hm => ?_, fun hpeer => ?_, ?_⟩
    · have h := hlag (by omega)
      refine ControlPosition.ext (by rw [hgen, h]) (le_antisymm r.state.controlPosition_step_le ?_)
      rw [h] at hstep
      exact hstep
    · obtain ⟨hwf', hle', hcur, howner'⟩ := hmsgs n m t hm
      exact ⟨hwf', by omega, fun h => (hcur (by omega)).trans hstep, howner'⟩
    · exact hlagP (by omega)
    · omega
  · -- The receiver advances: its role flips, and its recorded messages are from earlier epochs.
    have hflip : ∀ b : Bool, b = decide (st.epoch % 2 = if party then 1 else 0) →
        (!b) = decide (r.state.epoch % 2 = if party then 1 else 0) := by
      intro b hb
      rw [hsucc]
      cases b
      · have : ¬ st.epoch % 2 = if party then 1 else 0 := of_decide_eq_false hb.symm
        exact (decide_eq_true (by omega)).symm
      · have : st.epoch % 2 = if party then 1 else 0 := of_decide_eq_true hb.symm
        exact (decide_eq_false (by omega)).symm
    refine ⟨?_, fun hpeer => absurd hpeer (by omega), fun n m t hm => ?_, fun hpeer => ?_, ?_⟩
    · have h := hflip _ hrole
      rcases hedge.advance (by omega) with ⟨hgenSt, -, a, hks⟩ | ⟨hgenSt, -, -, a, dec, hnh⟩
      · rw [hgenSt, hks] at h
        rw [hks]
        simpa [State.controlPosition] using h
      · rw [hgenSt, hnh] at h
        rw [hnh]
        simpa [State.controlPosition] using h
    · obtain ⟨hwf', hle', -, howner'⟩ := hmsgs n m t hm
      exact ⟨hwf', by omega, fun h => absurd h (by omega), howner'⟩
    · -- Only edge 5 can advance a party to its peer's epoch plus one; then the peer sent `ct₂`.
      rcases hedge.advance (by omega) with ⟨-, hmsgEp, -⟩ | ⟨hgenSt, hty, hmsgEp, -⟩
      · exact absurd hle (by omega)
      · have hstep4 := hstepP (by omega)
        rw [hty] at hstep4
        simp only [MessageType.sendStep] at hstep4
        have hgenP : peer.controlPosition.isGenerator = false := by
          rw [hroleP]
          have : st.epoch % 2 = if party then 1 else 0 :=
            of_decide_eq_true (hgenSt.symm.trans hrole).symm
          exact decide_eq_false (by omega)
        exact ControlPosition.ext hgenP (le_antisymm peer.controlPosition_step_le hstep4)
    · omega

variable [DecidableEq P.EpochKey] [DecidableEq P.Sym]
  (irl : P.kem.IncrementalRandLeak P.inc) (sampleInitKey : ProbComp InitKey)

/-- The send oracle of either party preserves `ControlInv`. -/
theorem oracleSend_preserves_controlInv (party : Bool) :
    QueryImpl.PreservesInv (oracleSend auth irl sampleInitKey party) ControlInv := by
  rintro t (s : GameState P AuthState) hs z hz
  cases t
  have hEpoch := oracleSend_preserves_epochKnowledgeInv auth irl sampleInitKey party
    () s hs.epochKnowledge z hz
  have hReports : RecordedReportInv z.2 := by
    cases party
    · exact correctnessImpl_preserves_recordedReportInv auth irl sampleInitKey
        (OSendB (Rho := Message P.Sym)) s hs.recordedReport z hz
    · exact correctnessImpl_preserves_recordedReportInv auth irl sampleInitKey
        (OSendA (Rho := Message P.Sym)) s hs.recordedReport z hz
  obtain ⟨r, hr, rfl⟩ := (mem_support_oracleSend_run_iff auth irl sampleInitKey s party z).mp hz
  have hedge := (mem_support_send_iff auth).mp hr
  obtain ⟨hrole, hlag, hmsg⟩ := hs.roles party
  have hPeer := hs.roles (!party)
  simp only [PartyControl, Bool.not_not] at hPeer
  obtain ⟨hroleP, hlagP, hmsgP⟩ := hPeer
  obtain ⟨hgen, hlag, hmsgs⟩ := partyControl_send auth party hedge hrole hlag hmsg
    (s.countAt party + 1)
  have hep := hedge.epoch_eq.1
  have ht : r.sendingEpoch ≤ r.state.epoch - 1 := by rw [hedge.sendingEpoch_eq, hep]
  have htP := hs.tcur_le_sub_one (!party)
  have hlagP' : r.state.epoch = (s.stateAt (!party)).epoch + 1 →
      (s.stateAt (!party)).controlPosition = ⟨false, 4⟩ := by rw [hep]; exact hlagP
  cases party <;> rcases hkey : r.outputKey with _ | ⟨tI, key⟩ <;>
    simp only [sendUpdate, SCKAScheme.sendAUpdate, SCKAScheme.sendBUpdate, hkey,
      Bool.false_eq_true, ↓reduceIte] at hEpoch hReports ⊢
  all_goals first
    | exact ⟨hEpoch, hReports, htP, ht, fun who => by
        cases who; exacts [⟨hgen, hlag, hmsgs⟩, ⟨hroleP, hlagP', hmsgP⟩]⟩
    | exact ⟨hEpoch, hReports, ht, htP, fun who => by
        cases who; exacts [⟨hroleP, hlagP', hmsgP⟩, ⟨hgen, hlag, hmsgs⟩]⟩

/-- The receive oracle of either party preserves `ControlInv`. -/
theorem oracleRecv_preserves_controlInv (party : Bool) :
    QueryImpl.PreservesInv (oracleRecv auth irl sampleInitKey party) ControlInv := by
  rintro n (s : GameState P AuthState) hs z hz
  have hEpoch := oracleRecv_preserves_epochKnowledgeInv auth irl sampleInitKey party
    n s hs.epochKnowledge z hz
  have hReports : RecordedReportInv z.2 := by
    cases party
    · exact correctnessImpl_preserves_recordedReportInv auth irl sampleInitKey
        (ORecvB (Rho := Message P.Sym) n) s hs.recordedReport z hz
    · exact correctnessImpl_preserves_recordedReportInv auth irl sampleInitKey
        (ORecvA (Rho := Message P.Sym) n) s hs.recordedReport z hz
  rcases oracleRecv_run_cases auth irl sampleInitKey party hz with
    ⟨-, rfl⟩ | ⟨msg, tsnd, err, -, -, rfl⟩ | ⟨msg, tsnd, r, hentry, hraw, rfl⟩
  · exact hs
  · exact ⟨hEpoch, hReports, hs.tcurA_le_sub_one, hs.tcurB_le_sub_one, hs.roles⟩
  obtain ⟨hrole, hlag, hmsg⟩ := hs.roles party
  have hPeer := hs.roles (!party)
  simp only [PartyControl, Bool.not_not] at hPeer
  obtain ⟨hroleP, hlagP, hmsgP⟩ := hPeer
  have hcrossP := hs.epochKnowledge.epoch_le (!party)
  simp only [Bool.not_not] at hcrossP
  obtain ⟨hgen, hlag, hmsgs, hlagP, ht⟩ := partyControl_receive auth party hraw hrole
    (by cases party <;> exact hroleP) hlag hlagP hmsg (hmsgP n msg tsnd hentry)
    (hs.epochKnowledge.keyPrefix.pos party) hcrossP (hs.tcur_le_sub_one party)
  have htP := hs.tcur_le_sub_one (!party)
  cases party <;> rcases hkey : r.outputKey with _ | ⟨tI, key⟩ <;>
    simp only [recvUpdate, SCKAScheme.recvAUpdate, SCKAScheme.recvBUpdate, hkey,
      Bool.false_eq_true, ↓reduceIte] at hEpoch hReports ⊢
  all_goals first
    | exact ⟨hEpoch, hReports, htP, ht, fun who => by
        cases who; exacts [⟨hgen, hlag, hmsgs⟩, ⟨hroleP, hlagP, hmsgP⟩]⟩
    | exact ⟨hEpoch, hReports, ht, htP, fun who => by
        cases who; exacts [⟨hroleP, hlagP, hmsgP⟩, ⟨hgen, hlag, hmsgs⟩]⟩

/-- Every oracle of the correctness game preserves `ControlInv`. -/
theorem correctnessImpl_preserves_controlInv :
    QueryImpl.PreservesInv (SCKAScheme.sckaCorrectnessImpl (scheme P auth irl sampleInitKey))
      ControlInv :=
  SCKAScheme.sckaCorrectnessImpl_preservesInv _
    (oracleSend_preserves_controlInv auth irl sampleInitKey true)
    (oracleSend_preserves_controlInv auth irl sampleInitKey false)
    (oracleRecv_preserves_controlInv auth irl sampleInitKey true)
    (oracleRecv_preserves_controlInv auth irl sampleInitKey false)

end MLKEMBraid
