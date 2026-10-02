/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Correctness.KeyPrefixes
import SecureMessaging.SCKA.MLKEMBraid.Correctness.MessageReports

/-!
# Epoch bounds in the Braid correctness game

`EpochKnowledgeInv` bounds each party's epoch by its peer's completed epoch plus one, the game's
current epochs `tcurA`, `tcurB` (the largest epoch reported by the party's sends and receives) by
the party's completed epoch, and the epoch of every recorded message by both completed epochs plus
one. Every oracle of the correctness game preserves it.
-/

open OracleSpec OracleComp
open SCKAScheme.sckaCorrectnessSpec

namespace MLKEMBraid

variable (P : Parameters ProbComp) {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)

/-- Every outcome of `send` keeps the party's epoch, records it in the message, and sends `ct2`
only after completing that epoch. -/
theorem send_epoch_fields_of_mem_support
    (st : State P AuthState)
    (r : SendResult P AuthState)
    (hr : r ∈ support (send P auth st)) :
    r.state.epoch = st.epoch ∧
      r.msg.epoch = st.epoch ∧
      (r.msg.type = .ct2 → r.msg.epoch ≤ st.completedEpoch) := by
  cases st
  case keysUnsampled =>
    simp only [send, mem_support_bind_iff] at hr
    obtain ⟨out, _, hr⟩ := hr
    rcases out with ⟨pk, sk⟩
    simp only [mem_support_pure_iff] at hr
    subst r
    simp [State.epoch]
  case headerReceived =>
    simp only [send, mem_support_bind_iff] at hr
    obtain ⟨out, _, hr⟩ := hr
    rcases out with ⟨encapsState, ct1, k⟩
    simp only [mem_support_pure_iff] at hr
    subst r
    simp [State.epoch]
  all_goals
    simp only [send, mem_support_pure_iff] at hr
    subst r
    simp [State.epoch, State.completedEpoch]

/-- If the state and the message have epoch at most `c + 1`, and a `ct2` message at most `c`,
a successful receive leaves the state epoch at most `c + 1`. -/
theorem receive_epoch_le_of_eq_ok
    [DecidableEq P.Sym]
    (st : State P AuthState) (msg : Message P.Sym)
    (r : RecvResult P AuthState) (c : ℕ)
    (hst : st.epoch ≤ c + 1)
    (hmsg : msg.epoch ≤ c + 1)
    (hct2 : msg.type = .ct2 → msg.epoch ≤ c)
    (hr : receive P auth st msg = .ok r) :
    r.state.epoch ≤ c + 1 := by
  cases hstate : st <;>
    simp only [hstate, State.epoch] at hst hr ⊢ <;>
    simp only [receive] at hr
  all_goals
    repeat' split at hr
  all_goals cases hr
  all_goals simp_all only
  all_goals first | omega | have := hct2 trivial; omega

private theorem send_completedEpoch_mono
    (st : State P AuthState) (hpos : 0 < st.epoch)
    (r : SendResult P AuthState)
    (hr : r ∈ support (send P auth st)) :
    st.completedEpoch ≤ r.state.completedEpoch := by
  have hstep := send_completedEpoch_of_mem_support P auth st hpos r hr
  cases hkey : r.outputKey <;> simp only [hkey] at hstep
  all_goals omega

private theorem receive_completedEpoch_mono
    [DecidableEq P.Sym]
    (st : State P AuthState) (hpos : 0 < st.epoch)
    (msg : Message P.Sym) (r : RecvResult P AuthState)
    (hr : receive P auth st msg = .ok r) :
    st.completedEpoch ≤ r.state.completedEpoch := by
  have hstep := receive_completedEpoch_of_eq_ok P auth st hpos msg r hr
  cases hkey : r.outputKey <;> simp only [hkey] at hstep
  all_goals omega

/-- Epoch bounds for both parties and for every recorded message. -/
structure EpochKnowledgeInv
    {P : Parameters ProbComp} {AuthState : Type}
    (s : GameState P AuthState) : Prop where
  keyPrefix : KeyPrefixInv s
  /-- A is at most one epoch past B's completed epoch. -/
  epochA_le : s.stA.epoch ≤ s.stB.completedEpoch + 1
  /-- B is at most one epoch past A's completed epoch. -/
  epochB_le : s.stB.epoch ≤ s.stA.completedEpoch + 1
  /-- `tcurA` is at most A's completed epoch. -/
  tcurA_le : s.tcurA ≤ s.stA.completedEpoch
  /-- `tcurB` is at most B's completed epoch. -/
  tcurB_le : s.tcurB ≤ s.stB.completedEpoch
  /-- Every message recorded from A is at most one epoch past both completed epochs, and a
  recorded `ct2` message comes from an epoch A has completed. -/
  msgA : ∀ (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ),
    s.msgA n = some (msg, tsnd) →
      msg.epoch ≤ s.stA.completedEpoch + 1 ∧
      msg.epoch ≤ s.stB.completedEpoch + 1 ∧
      (msg.type = .ct2 → msg.epoch ≤ s.stA.completedEpoch)
  /-- Every message recorded from B is at most one epoch past both completed epochs, and a
  recorded `ct2` message comes from an epoch B has completed. -/
  msgB : ∀ (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ),
    s.msgB n = some (msg, tsnd) →
      msg.epoch ≤ s.stB.completedEpoch + 1 ∧
      msg.epoch ≤ s.stA.completedEpoch + 1 ∧
      (msg.type = .ct2 → msg.epoch ≤ s.stB.completedEpoch)

theorem epochKnowledgeInv_initGameState
    (ik : InitKey) :
    EpochKnowledgeInv
      (SCKAScheme.initGameState
        (I := P.EpochKey) (Rho := Message P.Sym)
        (initA P auth ik) (initB P auth ik)) := by
  refine ⟨keyPrefixInv_initGameState P auth ik, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [SCKAScheme.initGameState, initA, initB, State.epoch, State.completedEpoch]

theorem correctnessImpl_preserves_epochKnowledgeInv
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (irl : P.kem.IncrementalRandLeak P.inc)
    (sampleInitKey : ProbComp InitKey) :
    QueryImpl.PreservesInv
      (SCKAScheme.sckaCorrectnessImpl
        (scheme P auth irl sampleInitKey))
      EpochKnowledgeInv := by
  let scka := scheme P auth irl sampleInitKey
  have hKeyPrefix := correctnessImpl_preserves_keyPrefixInv P auth irl sampleInitKey
  have hSendA : QueryImpl.PreservesInv
      (SCKAScheme.oracleSendA scka) EpochKnowledgeInv := by
    intro _ s hs z hz
    have hprefix' : KeyPrefixInv z.2 :=
      hKeyPrefix (OSendA (Rho := Message P.Sym)) s hs.keyPrefix z hz
    rcases hs with ⟨hprefix, hAB, hBA, htA, htB, hmsgA, hmsgB⟩
    rcases hprefix with ⟨hposA, _, _, _⟩
    simp only [SCKAScheme.oracleSendA, scheme, bind_pure_comp, liftM_map, bind_map_left, stateTrun,
      support_bind, Set.mem_iUnion, exists_prop, scka] at hz
    obtain ⟨r, hr, hz⟩ := hz
    let msgA' := Function.update s.msgA (s.nA + 1)
      (some (r.msg, r.sendingEpoch))
    have hfields := send_epoch_fields_of_mem_support P auth s.stA r hr
    have hmono := send_completedEpoch_mono P auth s.stA hposA r hr
    have hlocal := s.stA.epoch_sub_one_le_completedEpoch
    have hcrossA : r.state.epoch ≤ s.stB.completedEpoch + 1 := by
      omega
    have hcrossB : s.stB.epoch ≤ r.state.completedEpoch + 1 := by
      omega
    have htA' : r.sendingEpoch ≤ r.state.completedEpoch := by
      have hreport := send_report_eq_of_mem_support P auth s.stA r hr
      omega
    have hmsgA' : ∀ (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ),
        msgA' n = some (msg, tsnd) →
          msg.epoch ≤ r.state.completedEpoch + 1 ∧
          msg.epoch ≤ s.stB.completedEpoch + 1 ∧
          (msg.type = .ct2 → msg.epoch ≤ r.state.completedEpoch) := by
      intro n msg tsnd hn
      by_cases hnew : n = s.nA + 1
      · subst n
        simp only [msgA', Function.update_self, Option.some.injEq,
          Prod.mk.injEq] at hn
        obtain ⟨rfl, rfl⟩ := hn
        refine ⟨by omega, by omega, ?_⟩
        intro htype
        exact (hfields.2.2 htype).trans hmono
      · simp only [msgA', Function.update_of_ne hnew] at hn
        have hold := hmsgA n msg tsnd hn
        refine ⟨by omega, hold.2.1, ?_⟩
        intro htype
        exact (hold.2.2 htype).trans hmono
    have hmsgB' : ∀ (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ),
        s.msgB n = some (msg, tsnd) →
          msg.epoch ≤ s.stB.completedEpoch + 1 ∧
          msg.epoch ≤ r.state.completedEpoch + 1 ∧
          (msg.type = .ct2 → msg.epoch ≤ s.stB.completedEpoch) := by
      intro n msg tsnd hn
      have hold := hmsgB n msg tsnd hn
      exact ⟨hold.1, by omega, hold.2.2⟩
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩
    all_goals
      simp only [hkey, StateT.run_map, StateT.run_set, map_pure,
        support_pure, Set.mem_singleton_iff] at hz
      subst z
      exact ⟨hprefix', hcrossA, hcrossB, htA', htB, hmsgA', hmsgB'⟩
  have hSendB : QueryImpl.PreservesInv
      (SCKAScheme.oracleSendB scka) EpochKnowledgeInv := by
    intro _ s hs z hz
    have hprefix' : KeyPrefixInv z.2 :=
      hKeyPrefix (OSendB (Rho := Message P.Sym)) s hs.keyPrefix z hz
    rcases hs with ⟨hprefix, hAB, hBA, htA, htB, hmsgA, hmsgB⟩
    rcases hprefix with ⟨_, hposB, _, _⟩
    simp only [SCKAScheme.oracleSendB, scheme, bind_pure_comp, liftM_map, bind_map_left, stateTrun,
      support_bind, Set.mem_iUnion, exists_prop, scka] at hz
    obtain ⟨r, hr, hz⟩ := hz
    let msgB' := Function.update s.msgB (s.nB + 1)
      (some (r.msg, r.sendingEpoch))
    have hfields := send_epoch_fields_of_mem_support P auth s.stB r hr
    have hmono := send_completedEpoch_mono P auth s.stB hposB r hr
    have hlocal := s.stB.epoch_sub_one_le_completedEpoch
    have hcrossA : s.stA.epoch ≤ r.state.completedEpoch + 1 := by
      omega
    have hcrossB : r.state.epoch ≤ s.stA.completedEpoch + 1 := by
      omega
    have htB' : r.sendingEpoch ≤ r.state.completedEpoch := by
      have hreport := send_report_eq_of_mem_support P auth s.stB r hr
      omega
    have hmsgA' : ∀ (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ),
        s.msgA n = some (msg, tsnd) →
          msg.epoch ≤ s.stA.completedEpoch + 1 ∧
          msg.epoch ≤ r.state.completedEpoch + 1 ∧
          (msg.type = .ct2 → msg.epoch ≤ s.stA.completedEpoch) := by
      intro n msg tsnd hn
      have hold := hmsgA n msg tsnd hn
      exact ⟨hold.1, by omega, hold.2.2⟩
    have hmsgB' : ∀ (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ),
        msgB' n = some (msg, tsnd) →
          msg.epoch ≤ r.state.completedEpoch + 1 ∧
          msg.epoch ≤ s.stA.completedEpoch + 1 ∧
          (msg.type = .ct2 → msg.epoch ≤ r.state.completedEpoch) := by
      intro n msg tsnd hn
      by_cases hnew : n = s.nB + 1
      · subst n
        simp only [msgB', Function.update_self, Option.some.injEq,
          Prod.mk.injEq] at hn
        obtain ⟨rfl, rfl⟩ := hn
        refine ⟨by omega, by omega, ?_⟩
        intro htype
        exact (hfields.2.2 htype).trans hmono
      · simp only [msgB', Function.update_of_ne hnew] at hn
        have hold := hmsgB n msg tsnd hn
        refine ⟨by omega, hold.2.1, ?_⟩
        intro htype
        exact (hold.2.2 htype).trans hmono
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩
    all_goals
      simp only [hkey, StateT.run_map, StateT.run_set, map_pure,
        support_pure, Set.mem_singleton_iff] at hz
      subst z
      exact ⟨hprefix', hcrossA, hcrossB, htA, htB', hmsgA', hmsgB'⟩
  have hRecvA : QueryImpl.PreservesInv
      (SCKAScheme.oracleRecvA scka) EpochKnowledgeInv := by
    intro n s hs z hz
    have hprefix' : KeyPrefixInv z.2 :=
      hKeyPrefix (ORecvA (Rho := Message P.Sym) n) s hs.keyPrefix z hz
    rcases hs with ⟨hprefix, hAB, hBA, htA, htB, hmsgA, hmsgB⟩
    rcases hprefix with ⟨hposA, _, _, _⟩
    rcases hentry : s.msgB n with _ | ⟨msg, tsnd⟩
    · simp only [SCKAScheme.oracleRecvA, bind_pure_comp, stateTrun, hentry, support_pure] at hz
      subst z
      exact ⟨hprefix', hAB, hBA, htA, htB, hmsgA, hmsgB⟩
    rcases hrecv : recvSCKA P auth s.stA msg with
      _ | ⟨keyOpt, treport, stA'⟩
    · simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp, stateTrun, hentry, hrecv,
        StateT.run_map, map_pure, support_pure, scka] at hz
      subst z
      exact ⟨hprefix', hAB, hBA, htA, htB, hmsgA, hmsgB⟩
    obtain ⟨r, hraw, hout, hstate, hreport⟩ := recvSCKA_eq_some_iff.mp hrecv
    have hrecord := hmsgB n msg tsnd hentry
    have hrecvBound := receive_epoch_le_of_eq_ok P auth s.stA msg r
      s.stB.completedEpoch hAB hrecord.1 hrecord.2.2 hraw
    have hmonoRaw :=
      receive_completedEpoch_mono P auth s.stA hposA msg r hraw
    have hmono : s.stA.completedEpoch ≤ stA'.completedEpoch := by
      simpa only [← hstate] using hmonoRaw
    have hcrossA : stA'.epoch ≤ s.stB.completedEpoch + 1 := by
      simpa only [← hstate] using hrecvBound
    have hcrossB : s.stB.epoch ≤ stA'.completedEpoch + 1 := by
      omega
    have htReport : treport ≤ s.stA.completedEpoch := by
      omega
    have htA' : max s.tcurA treport ≤ stA'.completedEpoch :=
      ((Nat.max_le).2 ⟨htA, htReport⟩).trans hmono
    have hmsgA' : ∀ (i : ℕ) (oldMsg : Message P.Sym) (oldTsnd : ℕ),
        s.msgA i = some (oldMsg, oldTsnd) →
          oldMsg.epoch ≤ stA'.completedEpoch + 1 ∧
          oldMsg.epoch ≤ s.stB.completedEpoch + 1 ∧
          (oldMsg.type = .ct2 →
            oldMsg.epoch ≤ stA'.completedEpoch) := by
      intro i oldMsg oldTsnd hi
      have hold := hmsgA i oldMsg oldTsnd hi
      refine ⟨by omega, hold.2.1, ?_⟩
      intro htype
      exact (hold.2.2 htype).trans hmono
    have hmsgB' : ∀ (i : ℕ) (oldMsg : Message P.Sym) (oldTsnd : ℕ),
        s.msgB i = some (oldMsg, oldTsnd) →
          oldMsg.epoch ≤ s.stB.completedEpoch + 1 ∧
          oldMsg.epoch ≤ stA'.completedEpoch + 1 ∧
          (oldMsg.type = .ct2 →
            oldMsg.epoch ≤ s.stB.completedEpoch) := by
      intro i oldMsg oldTsnd hi
      have hold := hmsgB i oldMsg oldTsnd hi
      exact ⟨hold.1, by omega, hold.2.2⟩
    rcases hkey : keyOpt with _ | ⟨tI, key⟩
    · simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp, stateTrun, hentry, hrecv, hkey,
        StateT.run_map, map_pure, support_pure, scka] at hz
      subst z
      exact ⟨hprefix', hcrossA, hcrossB, htA', htB, hmsgA', hmsgB'⟩
    · simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp, stateTrun, hentry, hrecv, hkey,
        StateT.run_map, map_pure, support_pure, scka] at hz
      subst z
      exact ⟨hprefix', hcrossA, hcrossB, htA', htB, hmsgA', hmsgB'⟩
  have hRecvB : QueryImpl.PreservesInv
      (SCKAScheme.oracleRecvB scka) EpochKnowledgeInv := by
    intro n s hs z hz
    have hprefix' : KeyPrefixInv z.2 :=
      hKeyPrefix (ORecvB (Rho := Message P.Sym) n) s hs.keyPrefix z hz
    rcases hs with ⟨hprefix, hAB, hBA, htA, htB, hmsgA, hmsgB⟩
    rcases hprefix with ⟨_, hposB, _, _⟩
    rcases hentry : s.msgA n with _ | ⟨msg, tsnd⟩
    · simp only [SCKAScheme.oracleRecvB, bind_pure_comp, stateTrun, hentry, support_pure] at hz
      subst z
      exact ⟨hprefix', hAB, hBA, htA, htB, hmsgA, hmsgB⟩
    rcases hrecv : recvSCKA P auth s.stB msg with
      _ | ⟨keyOpt, treport, stB'⟩
    · simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp, stateTrun, hentry, hrecv,
        StateT.run_map, map_pure, support_pure, scka] at hz
      subst z
      exact ⟨hprefix', hAB, hBA, htA, htB, hmsgA, hmsgB⟩
    obtain ⟨r, hraw, hout, hstate, hreport⟩ := recvSCKA_eq_some_iff.mp hrecv
    have hrecord := hmsgA n msg tsnd hentry
    have hrecvBound := receive_epoch_le_of_eq_ok P auth s.stB msg r
      s.stA.completedEpoch hBA hrecord.1 hrecord.2.2 hraw
    have hmonoRaw :=
      receive_completedEpoch_mono P auth s.stB hposB msg r hraw
    have hmono : s.stB.completedEpoch ≤ stB'.completedEpoch := by
      simpa only [← hstate] using hmonoRaw
    have hcrossA : s.stA.epoch ≤ stB'.completedEpoch + 1 := by
      omega
    have hcrossB : stB'.epoch ≤ s.stA.completedEpoch + 1 := by
      simpa only [← hstate] using hrecvBound
    have htReport : treport ≤ s.stB.completedEpoch := by
      omega
    have htB' : max s.tcurB treport ≤ stB'.completedEpoch :=
      ((Nat.max_le).2 ⟨htB, htReport⟩).trans hmono
    have hmsgA' : ∀ (i : ℕ) (oldMsg : Message P.Sym) (oldTsnd : ℕ),
        s.msgA i = some (oldMsg, oldTsnd) →
          oldMsg.epoch ≤ s.stA.completedEpoch + 1 ∧
          oldMsg.epoch ≤ stB'.completedEpoch + 1 ∧
          (oldMsg.type = .ct2 →
            oldMsg.epoch ≤ s.stA.completedEpoch) := by
      intro i oldMsg oldTsnd hi
      have hold := hmsgA i oldMsg oldTsnd hi
      exact ⟨hold.1, by omega, hold.2.2⟩
    have hmsgB' : ∀ (i : ℕ) (oldMsg : Message P.Sym) (oldTsnd : ℕ),
        s.msgB i = some (oldMsg, oldTsnd) →
          oldMsg.epoch ≤ stB'.completedEpoch + 1 ∧
          oldMsg.epoch ≤ s.stA.completedEpoch + 1 ∧
          (oldMsg.type = .ct2 →
            oldMsg.epoch ≤ stB'.completedEpoch) := by
      intro i oldMsg oldTsnd hi
      have hold := hmsgB i oldMsg oldTsnd hi
      refine ⟨by omega, hold.2.1, ?_⟩
      intro htype
      exact (hold.2.2 htype).trans hmono
    rcases hkey : keyOpt with _ | ⟨tI, key⟩
    · simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp, stateTrun, hentry, hrecv, hkey,
        StateT.run_map, map_pure, support_pure, scka] at hz
      subst z
      exact ⟨hprefix', hcrossA, hcrossB, htA, htB', hmsgA', hmsgB'⟩
    · simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp, stateTrun, hentry, hrecv, hkey,
        StateT.run_map, map_pure, support_pure, scka] at hz
      subst z
      exact ⟨hprefix', hcrossA, hcrossB, htA, htB', hmsgA', hmsgB'⟩
  exact SCKAScheme.sckaCorrectnessImpl_preservesInv hSendA hSendB hRecvA hRecvB

end MLKEMBraid
