/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.MLKEMBraid.Correctness.KeyPrefixes

/-!
# Epoch bounds in the Braid correctness game

`EpochKnowledgeInv` bounds each party's epoch by its peer's completed epoch plus one, the game's
current epochs `tcurA`, `tcurB` (the largest epoch reported by the party's sends and receives) by
the party's completed epoch, and the epoch of every recorded message by both completed epochs plus
one. Every send edge preserves it, and so does every receive edge on a message recorded by the
peer.
-/

@[expose] public section

open OracleSpec OracleComp
open SCKAScheme.sckaCorrectnessSpec

namespace Braid

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

variable [DecidableEq P.EpochKey]

/-- A send edge from the state of `party` preserves `EpochKnowledgeInv`. -/
theorem epochKnowledgeInv_sendUpdate {s : GameState P AuthState} (hs : EpochKnowledgeInv s)
    (party : Bool) {r : SendResult P AuthState} (hedge : SendEdge auth (s.stateAt party) r) :
    EpochKnowledgeInv (sendUpdate s party r) := by
  have hprefix : KeyPrefixInv (sendUpdate s party r) :=
    keyPrefixInv_sendUpdate auth hs.keyPrefix party hedge
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

/-- A receive edge from the state of `party`, on the message recorded by the peer at index `n`,
preserves `EpochKnowledgeInv`. -/
theorem epochKnowledgeInv_recvUpdate {s : GameState P AuthState}
    (hs : EpochKnowledgeInv s) (party : Bool) {n : ℕ} {msg : Message P.Sym} {tsnd : ℕ}
    {r : RecvResult P AuthState} (hentry : s.messagesAt (!party) n = some (msg, tsnd))
    (hedge : ReceiveEdge auth (s.stateAt party) msg r) :
    EpochKnowledgeInv (recvUpdate s party tsnd r (msg.epoch - 1)) := by
  have hprefix : KeyPrefixInv (recvUpdate s party tsnd r (msg.epoch - 1)) :=
    keyPrefixInv_recvUpdate auth hs.keyPrefix party hedge tsnd (msg.epoch - 1)
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

end Braid
