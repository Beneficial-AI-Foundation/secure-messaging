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
  /-- Epoch bounds on messages recorded by A, with the stronger bound for `ct₂`. -/
  msgA : ∀ (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ),
    s.msgA n = some (msg, tsnd) →
      msg.epoch ≤ s.stA.completedEpoch + 1 ∧
      msg.epoch ≤ s.stB.completedEpoch + 1 ∧
      (msg.type = .ct2 → msg.epoch ≤ s.stA.completedEpoch)
  /-- The corresponding message bounds for B. -/
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

variable [DecidableEq P.EpochKey] [DecidableEq P.Sym]
  (irl : P.kem.IncrementalRandLeak P.inc) (sampleInitKey : ProbComp InitKey)

/-- The send oracle of either party preserves `EpochKnowledgeInv`. -/
theorem oracleSend_preserves_epochKnowledgeInv (party : Bool) :
    QueryImpl.PreservesInv (oracleSend auth irl sampleInitKey party) EpochKnowledgeInv := by
  rintro _ (s : GameState P AuthState) hs z hz
  have hprefix : KeyPrefixInv z.2 := by
    cases party
    · exact correctnessImpl_preserves_keyPrefixInv auth irl sampleInitKey
        (OSendB (Rho := Message P.Sym)) s hs.keyPrefix z hz
    · exact correctnessImpl_preserves_keyPrefixInv auth irl sampleInitKey
        (OSendA (Rho := Message P.Sym)) s hs.keyPrefix z hz
  obtain ⟨r, hr, rfl⟩ := (mem_support_oracleSend_run_iff auth irl sampleInitKey s party z).mp hz
  have hedge := (mem_support_send_iff auth).mp hr
  obtain ⟨hep, hmsgEp⟩ := hedge.epoch_eq
  have hmono := hedge.completedEpoch_mono (hs.keyPrefix.pos party)
  have hlocal := (s.stateAt party).epoch_sub_one_le_completedEpoch
  have hreport := hedge.sendingEpoch_eq
  have hcross := hs.epoch_le party
  have hcrossP := hs.epoch_le (!party)
  simp only [Bool.not_not] at hcrossP
  have hmsgs : ∀ n msg tsnd,
      Function.update (s.messagesAt party) (s.countAt party + 1)
        (some (r.msg, r.sendingEpoch)) n = some (msg, tsnd) →
      msg.epoch ≤ r.state.completedEpoch + 1 ∧
        msg.epoch ≤ (s.stateAt (!party)).completedEpoch + 1 ∧
        (msg.type = .ct2 → msg.epoch ≤ r.state.completedEpoch) := by
    intro n msg tsnd hn
    by_cases hnew : n = s.countAt party + 1
    · subst n
      rw [Function.update_self] at hn
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
      exact ⟨by omega, by omega, fun hty => (hedge.completedEpoch_of_ct2 hty).trans hmono⟩
    · rw [Function.update_of_ne hnew] at hn
      obtain ⟨h1, h2, h3⟩ := hs.msgs party n msg tsnd hn
      exact ⟨by omega, h2, fun hty => (h3 hty).trans hmono⟩
  have hmsgsP : ∀ n msg tsnd, s.messagesAt (!party) n = some (msg, tsnd) →
      msg.epoch ≤ (s.stateAt (!party)).completedEpoch + 1 ∧
        msg.epoch ≤ r.state.completedEpoch + 1 ∧
        (msg.type = .ct2 → msg.epoch ≤ (s.stateAt (!party)).completedEpoch) := by
    intro n msg tsnd hn
    obtain ⟨h1, h2, h3⟩ := hs.msgs (!party) n msg tsnd hn
    simp only [Bool.not_not] at h2
    exact ⟨h1, by omega, h3⟩
  have htcurP := hs.tcur_le (!party)
  have hc : r.state.epoch ≤ (s.stateAt (!party)).completedEpoch + 1 := by omega
  have hcP : (s.stateAt (!party)).epoch ≤ r.state.completedEpoch + 1 := by omega
  have ht : r.sendingEpoch ≤ r.state.completedEpoch := by omega
  cases party <;> rcases hkey : r.outputKey with _ | ⟨tI, key⟩ <;>
    simp only [sendUpdate, SCKAScheme.sendAUpdate, SCKAScheme.sendBUpdate, hkey,
      Bool.false_eq_true, ↓reduceIte] at hprefix ⊢
  all_goals first
    | exact ⟨hprefix, hcP, hc, htcurP, ht, hmsgsP, hmsgs⟩
    | exact ⟨hprefix, hc, hcP, ht, htcurP, hmsgs, hmsgsP⟩

/-- The receive oracle of either party preserves `EpochKnowledgeInv`. -/
theorem oracleRecv_preserves_epochKnowledgeInv (party : Bool) :
    QueryImpl.PreservesInv (oracleRecv auth irl sampleInitKey party) EpochKnowledgeInv := by
  rintro n (s : GameState P AuthState) hs z hz
  have hprefix : KeyPrefixInv z.2 := by
    cases party
    · exact correctnessImpl_preserves_keyPrefixInv auth irl sampleInitKey
        (ORecvB (Rho := Message P.Sym) n) s hs.keyPrefix z hz
    · exact correctnessImpl_preserves_keyPrefixInv auth irl sampleInitKey
        (ORecvA (Rho := Message P.Sym) n) s hs.keyPrefix z hz
  rcases oracleRecv_run_cases auth irl sampleInitKey party hz with
    ⟨-, rfl⟩ | ⟨msg, tsnd, err, -, -, rfl⟩ | ⟨msg, tsnd, r, hentry, hraw, rfl⟩
  · exact hs
  · exact ⟨hprefix, hs.epochA_le, hs.epochB_le, hs.tcurA_le, hs.tcurB_le, hs.msgA, hs.msgB⟩
  have hedge := ReceiveEdge.of_eq_ok auth hraw
  obtain ⟨h1, h2, h3⟩ := hs.msgs (!party) n msg tsnd hentry
  have hbound := hedge.epoch_le_of_le _ (hs.epoch_le party) h1 h3
  have hmono := hedge.completedEpoch_mono (hs.keyPrefix.pos party)
  have hcrossP := hs.epoch_le (!party)
  have htcur := hs.tcur_le party
  have htcurP := hs.tcur_le (!party)
  simp only [Bool.not_not] at hcrossP h2
  have hcP : (s.stateAt (!party)).epoch ≤ r.state.completedEpoch + 1 := by omega
  have ht : max (s.tcurAt party) (msg.epoch - 1) ≤ r.state.completedEpoch := by omega
  have hmsgs : ∀ i m t, s.messagesAt party i = some (m, t) →
      m.epoch ≤ r.state.completedEpoch + 1 ∧
        m.epoch ≤ (s.stateAt (!party)).completedEpoch + 1 ∧
        (m.type = .ct2 → m.epoch ≤ r.state.completedEpoch) := by
    intro i m t hi
    obtain ⟨a, b, c⟩ := hs.msgs party i m t hi
    exact ⟨by omega, b, fun hty => (c hty).trans hmono⟩
  have hmsgsP : ∀ i m t, s.messagesAt (!party) i = some (m, t) →
      m.epoch ≤ (s.stateAt (!party)).completedEpoch + 1 ∧
        m.epoch ≤ r.state.completedEpoch + 1 ∧
        (m.type = .ct2 → m.epoch ≤ (s.stateAt (!party)).completedEpoch) := by
    intro i m t hi
    obtain ⟨a, b, c⟩ := hs.msgs (!party) i m t hi
    simp only [Bool.not_not] at b
    exact ⟨a, by omega, c⟩
  cases party <;> rcases hkey : r.outputKey with _ | ⟨tI, key⟩ <;>
    simp only [recvUpdate, SCKAScheme.recvAUpdate, SCKAScheme.recvBUpdate, hkey,
      Bool.false_eq_true, ↓reduceIte] at hprefix ⊢
  all_goals first
    | exact ⟨hprefix, hcP, hbound, htcurP, ht, hmsgsP, hmsgs⟩
    | exact ⟨hprefix, hbound, hcP, ht, htcurP, hmsgs, hmsgsP⟩

/-- Every oracle of the correctness game preserves `EpochKnowledgeInv`. -/
theorem correctnessImpl_preserves_epochKnowledgeInv :
    QueryImpl.PreservesInv
      (SCKAScheme.sckaCorrectnessImpl (scheme P auth irl sampleInitKey)) EpochKnowledgeInv :=
  SCKAScheme.sckaCorrectnessImpl_preservesInv _
    (oracleSend_preserves_epochKnowledgeInv auth irl sampleInitKey true)
    (oracleSend_preserves_epochKnowledgeInv auth irl sampleInitKey false)
    (oracleRecv_preserves_epochKnowledgeInv auth irl sampleInitKey true)
    (oracleRecv_preserves_epochKnowledgeInv auth irl sampleInitKey false)

end MLKEMBraid
