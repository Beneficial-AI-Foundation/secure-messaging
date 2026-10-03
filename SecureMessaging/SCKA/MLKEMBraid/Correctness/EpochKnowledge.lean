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
current epochs `tcurA` and `tcurB` by the party's completed epoch, and the epoch of every recorded
message by both completed epochs plus one; a recorded `ct₂` message belongs to an epoch its sender
has completed. Every oracle of the correctness game preserves it: a send keeps the sender's epoch
and stamps it on the message (`SendEdge.epoch_eq`), and a receive raises the epoch at most to the
bound of the delivered message (`ReceiveEdge.epoch_le_of_le`).
-/

open OracleSpec OracleComp
open SCKAScheme.sckaCorrectnessSpec

namespace MLKEMBraid

variable {P : Parameters ProbComp} {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)

/-- Epoch bounds for both parties and for every recorded message. -/
structure EpochKnowledgeInv {P : Parameters ProbComp} {AuthState : Type}
    (s : GameState P AuthState) : Prop where
  /-- Both epochs are positive and the key tables are prefixes. -/
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
  recorded `ct₂` message comes from an epoch A has completed. -/
  msgA : ∀ (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ),
    s.msgA n = some (msg, tsnd) →
      msg.epoch ≤ s.stA.completedEpoch + 1 ∧
      msg.epoch ≤ s.stB.completedEpoch + 1 ∧
      (msg.type = .ct2 → msg.epoch ≤ s.stA.completedEpoch)
  /-- Every message recorded from B is at most one epoch past both completed epochs, and a
  recorded `ct₂` message comes from an epoch B has completed. -/
  msgB : ∀ (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ),
    s.msgB n = some (msg, tsnd) →
      msg.epoch ≤ s.stB.completedEpoch + 1 ∧
      msg.epoch ≤ s.stA.completedEpoch + 1 ∧
      (msg.type = .ct2 → msg.epoch ≤ s.stB.completedEpoch)

/-- Each party's current game epoch is at most its completed epoch. -/
theorem EpochKnowledgeInv.tcur_le {s : GameState P AuthState} (hs : EpochKnowledgeInv s)
    (party : Bool) : s.tcurAt party ≤ (s.stateAt party).completedEpoch := by
  cases party; exacts [hs.tcurB_le, hs.tcurA_le]

/-- Each party is at most one epoch past its peer's completed epoch. -/
theorem EpochKnowledgeInv.epoch_le {s : GameState P AuthState} (hs : EpochKnowledgeInv s)
    (party : Bool) : (s.stateAt party).epoch ≤ (s.stateAt (!party)).completedEpoch + 1 := by
  cases party; exacts [hs.epochB_le, hs.epochA_le]

/-- A recorded message is at most one epoch past both completed epochs; a `ct₂` message comes
from an epoch its sender has completed. -/
theorem EpochKnowledgeInv.msgs {s : GameState P AuthState} (hs : EpochKnowledgeInv s)
    (party : Bool) (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ)
    (hentry : s.messagesAt party n = some (msg, tsnd)) :
    msg.epoch ≤ (s.stateAt party).completedEpoch + 1 ∧
      msg.epoch ≤ (s.stateAt (!party)).completedEpoch + 1 ∧
      (msg.type = .ct2 → msg.epoch ≤ (s.stateAt party).completedEpoch) := by
  cases party; exacts [hs.msgB n msg tsnd hentry, hs.msgA n msg tsnd hentry]

/-- The initial game state satisfies `EpochKnowledgeInv`. -/
theorem epochKnowledgeInv_initGameState (ik : InitKey) :
    EpochKnowledgeInv
      (SCKAScheme.initGameState (I := P.EpochKey) (Rho := Message P.Sym)
        (initA P auth ik) (initB P auth ik)) := by
  refine ⟨keyPrefixInv_initGameState auth ik, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [SCKAScheme.initGameState, initA, initB, State.epoch, State.completedEpoch]

/-- Every oracle of the correctness game preserves `EpochKnowledgeInv`. -/
theorem correctnessImpl_preserves_epochKnowledgeInv
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (irl : P.kem.IncrementalRandLeak P.inc) (sampleInitKey : ProbComp InitKey) :
    QueryImpl.PreservesInv
      (SCKAScheme.sckaCorrectnessImpl (scheme P auth irl sampleInitKey)) EpochKnowledgeInv := by
  have hKeyPrefix := correctnessImpl_preserves_keyPrefixInv auth irl sampleInitKey
  refine SCKAScheme.sckaCorrectnessImpl_preservesInv _ ?_ ?_ ?_ ?_
  -- A send keeps the sender's epoch, may complete an epoch, and records a message of its epoch.
  · intro _ s hs z hz
    have hprefix := hKeyPrefix (OSendA (Rho := Message P.Sym)) s hs.keyPrefix z hz
    obtain ⟨r, hr, rfl⟩ := (mem_support_oracleSendA_run_iff auth irl sampleInitKey s z).mp hz
    have hedge := (mem_support_send_iff auth).mp hr
    obtain ⟨hep, hmsgEp⟩ := hedge.epoch_eq
    have hmono := hedge.completedEpoch_mono hs.keyPrefix.posA
    have hlocal := s.stA.epoch_sub_one_le_completedEpoch
    have hreport := hedge.sendingEpoch_eq
    have hcrossA : r.state.epoch ≤ s.stB.completedEpoch + 1 := by have := hs.epochA_le; omega
    have hcrossB : s.stB.epoch ≤ r.state.completedEpoch + 1 := by have := hs.epochB_le; omega
    have htA : r.sendingEpoch ≤ r.state.completedEpoch := by omega
    have hmsgA : ∀ (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ),
        Function.update s.msgA (s.nA + 1) (some (r.msg, r.sendingEpoch)) n = some (msg, tsnd) →
          msg.epoch ≤ r.state.completedEpoch + 1 ∧ msg.epoch ≤ s.stB.completedEpoch + 1 ∧
            (msg.type = .ct2 → msg.epoch ≤ r.state.completedEpoch) := by
      intro n msg tsnd hn
      by_cases hnew : n = s.nA + 1
      · subst hnew
        rw [Function.update_self] at hn
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
        exact ⟨by omega, by omega, fun hty => (hedge.completedEpoch_of_ct2 hty).trans hmono⟩
      · rw [Function.update_of_ne hnew] at hn
        obtain ⟨h1, h2, h3⟩ := hs.msgA n msg tsnd hn
        exact ⟨by omega, h2, fun hty => (h3 hty).trans hmono⟩
    have hmsgB : ∀ (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ),
        s.msgB n = some (msg, tsnd) →
          msg.epoch ≤ s.stB.completedEpoch + 1 ∧ msg.epoch ≤ r.state.completedEpoch + 1 ∧
            (msg.type = .ct2 → msg.epoch ≤ s.stB.completedEpoch) := by
      intro n msg tsnd hn
      obtain ⟨h1, h2, h3⟩ := hs.msgB n msg tsnd hn
      exact ⟨h1, by omega, h3⟩
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩ <;>
      exact ⟨by rwa [hkey] at hprefix, hcrossA, hcrossB, htA, hs.tcurB_le, hmsgA, hmsgB⟩
  · intro _ s hs z hz
    have hprefix := hKeyPrefix (OSendB (Rho := Message P.Sym)) s hs.keyPrefix z hz
    obtain ⟨r, hr, rfl⟩ := (mem_support_oracleSendB_run_iff auth irl sampleInitKey s z).mp hz
    have hedge := (mem_support_send_iff auth).mp hr
    obtain ⟨hep, hmsgEp⟩ := hedge.epoch_eq
    have hmono := hedge.completedEpoch_mono hs.keyPrefix.posB
    have hlocal := s.stB.epoch_sub_one_le_completedEpoch
    have hreport := hedge.sendingEpoch_eq
    have hcrossA : s.stA.epoch ≤ r.state.completedEpoch + 1 := by have := hs.epochA_le; omega
    have hcrossB : r.state.epoch ≤ s.stA.completedEpoch + 1 := by have := hs.epochB_le; omega
    have htB : r.sendingEpoch ≤ r.state.completedEpoch := by omega
    have hmsgA : ∀ (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ),
        s.msgA n = some (msg, tsnd) →
          msg.epoch ≤ s.stA.completedEpoch + 1 ∧ msg.epoch ≤ r.state.completedEpoch + 1 ∧
            (msg.type = .ct2 → msg.epoch ≤ s.stA.completedEpoch) := by
      intro n msg tsnd hn
      obtain ⟨h1, h2, h3⟩ := hs.msgA n msg tsnd hn
      exact ⟨h1, by omega, h3⟩
    have hmsgB : ∀ (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ),
        Function.update s.msgB (s.nB + 1) (some (r.msg, r.sendingEpoch)) n = some (msg, tsnd) →
          msg.epoch ≤ r.state.completedEpoch + 1 ∧ msg.epoch ≤ s.stA.completedEpoch + 1 ∧
            (msg.type = .ct2 → msg.epoch ≤ r.state.completedEpoch) := by
      intro n msg tsnd hn
      by_cases hnew : n = s.nB + 1
      · subst hnew
        rw [Function.update_self] at hn
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
        exact ⟨by omega, by omega, fun hty => (hedge.completedEpoch_of_ct2 hty).trans hmono⟩
      · rw [Function.update_of_ne hnew] at hn
        obtain ⟨h1, h2, h3⟩ := hs.msgB n msg tsnd hn
        exact ⟨by omega, h2, fun hty => (h3 hty).trans hmono⟩
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩ <;>
      exact ⟨by rwa [hkey] at hprefix, hcrossA, hcrossB, hs.tcurA_le, htB, hmsgA, hmsgB⟩
  -- A receive raises the receiver's epoch at most to the bound of the delivered message.
  · intro n s hs z hz
    have hprefix := hKeyPrefix (ORecvA (Rho := Message P.Sym) n) s hs.keyPrefix z hz
    rcases oracleRecvA_run_cases auth irl sampleInitKey hz with
      ⟨-, rfl⟩ | ⟨msg, tsnd, err, -, -, rfl⟩ | ⟨msg, tsnd, r, hentry, hraw, rfl⟩
    · exact hs
    · exact ⟨hprefix, hs.epochA_le, hs.epochB_le, hs.tcurA_le, hs.tcurB_le, hs.msgA, hs.msgB⟩
    have hedge := ReceiveEdge.of_eq_ok auth hraw
    obtain ⟨h1, h2, h3⟩ := hs.msgB n msg tsnd hentry
    have hbound := hedge.epoch_le_of_le s.stB.completedEpoch hs.epochA_le h1 h3
    have hmono := hedge.completedEpoch_mono hs.keyPrefix.posA
    have hcrossB : s.stB.epoch ≤ r.state.completedEpoch + 1 := by have := hs.epochB_le; omega
    have htA : max s.tcurA (msg.epoch - 1) ≤ r.state.completedEpoch := by
      have := hs.tcurA_le
      omega
    have hmsgA : ∀ (i : ℕ) (m : Message P.Sym) (t : ℕ),
        s.msgA i = some (m, t) →
          m.epoch ≤ r.state.completedEpoch + 1 ∧ m.epoch ≤ s.stB.completedEpoch + 1 ∧
            (m.type = .ct2 → m.epoch ≤ r.state.completedEpoch) := by
      intro i m t hi
      obtain ⟨a, b, c⟩ := hs.msgA i m t hi
      exact ⟨by omega, b, fun hty => (c hty).trans hmono⟩
    have hmsgB : ∀ (i : ℕ) (m : Message P.Sym) (t : ℕ),
        s.msgB i = some (m, t) →
          m.epoch ≤ s.stB.completedEpoch + 1 ∧ m.epoch ≤ r.state.completedEpoch + 1 ∧
            (m.type = .ct2 → m.epoch ≤ s.stB.completedEpoch) := by
      intro i m t hi
      obtain ⟨a, b, c⟩ := hs.msgB i m t hi
      exact ⟨a, by omega, c⟩
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩ <;>
      exact ⟨by rwa [hkey] at hprefix, hbound, hcrossB, htA, hs.tcurB_le, hmsgA, hmsgB⟩
  · intro n s hs z hz
    have hprefix := hKeyPrefix (ORecvB (Rho := Message P.Sym) n) s hs.keyPrefix z hz
    rcases oracleRecvB_run_cases auth irl sampleInitKey hz with
      ⟨-, rfl⟩ | ⟨msg, tsnd, err, -, -, rfl⟩ | ⟨msg, tsnd, r, hentry, hraw, rfl⟩
    · exact hs
    · exact ⟨hprefix, hs.epochA_le, hs.epochB_le, hs.tcurA_le, hs.tcurB_le, hs.msgA, hs.msgB⟩
    have hedge := ReceiveEdge.of_eq_ok auth hraw
    obtain ⟨h1, h2, h3⟩ := hs.msgA n msg tsnd hentry
    have hbound := hedge.epoch_le_of_le s.stA.completedEpoch hs.epochB_le h1 h3
    have hmono := hedge.completedEpoch_mono hs.keyPrefix.posB
    have hcrossA : s.stA.epoch ≤ r.state.completedEpoch + 1 := by have := hs.epochA_le; omega
    have htB : max s.tcurB (msg.epoch - 1) ≤ r.state.completedEpoch := by
      have := hs.tcurB_le
      omega
    have hmsgA : ∀ (i : ℕ) (m : Message P.Sym) (t : ℕ),
        s.msgA i = some (m, t) →
          m.epoch ≤ s.stA.completedEpoch + 1 ∧ m.epoch ≤ r.state.completedEpoch + 1 ∧
            (m.type = .ct2 → m.epoch ≤ s.stA.completedEpoch) := by
      intro i m t hi
      obtain ⟨a, b, c⟩ := hs.msgA i m t hi
      exact ⟨a, by omega, c⟩
    have hmsgB : ∀ (i : ℕ) (m : Message P.Sym) (t : ℕ),
        s.msgB i = some (m, t) →
          m.epoch ≤ r.state.completedEpoch + 1 ∧ m.epoch ≤ s.stA.completedEpoch + 1 ∧
            (m.type = .ct2 → m.epoch ≤ r.state.completedEpoch) := by
      intro i m t hi
      obtain ⟨a, b, c⟩ := hs.msgB i m t hi
      exact ⟨by omega, b, fun hty => (c hty).trans hmono⟩
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩ <;>
      exact ⟨by rwa [hkey] at hprefix, hcrossA, hbound, hs.tcurA_le, htB, hmsgA, hmsgB⟩

end MLKEMBraid
