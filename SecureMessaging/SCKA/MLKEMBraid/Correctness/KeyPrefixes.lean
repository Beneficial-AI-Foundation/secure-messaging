/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.MLKEMBraid.Correctness.Oracles

/-!
# Key prefixes in the Braid correctness game

`State.completedEpoch` is the last epoch whose key a party has computed. A send or a successful
receive either keeps it, or outputs the key of the next epoch and completes that epoch.
`KeyPrefixInv` states that both epochs are positive and that each party has output keys for
exactly the epochs from `1` through its completed epoch. Every send edge and every receive edge of
either party preserves it.
-/

@[expose] public section

open OracleSpec OracleComp

namespace Braid

variable {P : Parameters ProbComp} {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)

/-- Both epochs are positive, and each party has output keys for exactly the epochs from `1`
through its completed epoch. -/
structure KeyPrefixInv {P : Parameters ProbComp} {AuthState : Type}
    (s : GameState P AuthState) : Prop where
  /-- A's epoch is positive. -/
  posA : 0 < s.stA.epoch
  /-- B's epoch is positive. -/
  posB : 0 < s.stB.epoch
  /-- A has keys for exactly the epochs from `1` through its completed epoch. -/
  prefixA : ∀ t : ℕ, s.keyA t ≠ none ↔ 0 < t ∧ t ≤ s.stA.completedEpoch
  /-- B has keys for exactly the epochs from `1` through its completed epoch. -/
  prefixB : ∀ t : ℕ, s.keyB t ≠ none ↔ 0 < t ∧ t ≤ s.stB.completedEpoch

/-- Each party's epoch is positive. -/
theorem KeyPrefixInv.pos {s : GameState P AuthState} (hs : KeyPrefixInv s) (party : Bool) :
    0 < (s.stateAt party).epoch := by
  cases party; exacts [hs.posB, hs.posA]

/-- Each party has keys for exactly the positive epochs through its completed epoch. -/
theorem KeyPrefixInv.keys {s : GameState P AuthState} (hs : KeyPrefixInv s) (party : Bool)
    (t : ℕ) : s.keysAt party t ≠ none ↔ 0 < t ∧ t ≤ (s.stateAt party).completedEpoch := by
  cases party; exacts [hs.prefixB t, hs.prefixA t]

/-- The initial game state satisfies `KeyPrefixInv`: both parties are at epoch `1` and have
output no key. -/
theorem keyPrefixInv_initGameState (ik : InitKey) :
    KeyPrefixInv
      (SCKAScheme.initGameState (I := P.EpochKey) (Rho := Message P.Sym)
        (initA P auth ik) (initB P auth ik)) := by
  constructor <;> simp [SCKAScheme.initGameState, initA, initB,
    State.epoch, State.completedEpoch]
  all_goals omega

variable [DecidableEq P.EpochKey]

/-- A send edge from the state of `party` preserves `KeyPrefixInv`: the sender's completed epoch and
key table change together. -/
theorem keyPrefixInv_sendUpdate {s : GameState P AuthState} (hs : KeyPrefixInv s) (party : Bool)
    {r : SendResult P AuthState} (hedge : SendEdge auth (s.stateAt party) r) :
    KeyPrefixInv (sendUpdate s party r) := by
  have hpos : 0 < r.state.epoch := hedge.epoch_eq.1 ▸ hs.pos party
  have hstep := hedge.completedEpoch (hs.pos party)
  cases party
  · simp only [GameState.stateAt, Bool.false_eq_true, ↓reduceIte] at hstep
    simp only [sendUpdate, Bool.false_eq_true, ↓reduceIte]
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩ <;> simp only [hkey] at hstep
    · refine ⟨hs.posA, hpos, hs.prefixA, ?_⟩
      simpa [SCKAScheme.sendBUpdate, hstep] using hs.prefixB
    · refine ⟨hs.posA, hpos, hs.prefixA, ?_⟩
      simpa [SCKAScheme.sendBUpdate, hstep.1, hstep.2] using
        SCKAScheme.update_succ_ne_none_iff hs.prefixB key
  · simp only [GameState.stateAt, ↓reduceIte] at hstep
    simp only [sendUpdate, ↓reduceIte]
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩ <;> simp only [hkey] at hstep
    · refine ⟨hpos, hs.posB, ?_, hs.prefixB⟩
      simpa [SCKAScheme.sendAUpdate, hstep] using hs.prefixA
    · refine ⟨hpos, hs.posB, ?_, hs.prefixB⟩
      simpa [SCKAScheme.sendAUpdate, hstep.1, hstep.2] using
        SCKAScheme.update_succ_ne_none_iff hs.prefixA key

/-- A receive edge from the state of `party` preserves `KeyPrefixInv`, for any stored report `tsnd`
and receive report `trcv`. -/
theorem keyPrefixInv_recvUpdate {s : GameState P AuthState}
    (hs : KeyPrefixInv s) (party : Bool) {msg : Message P.Sym} {r : RecvResult P AuthState}
    (hedge : ReceiveEdge auth (s.stateAt party) msg r) (tsnd trcv : ℕ) :
    KeyPrefixInv (recvUpdate s party tsnd r trcv) := by
  have hstep := hedge.completedEpoch (hs.pos party)
  cases party
  · simp only [GameState.stateAt, Bool.false_eq_true, ↓reduceIte] at hstep
    simp only [recvUpdate, Bool.false_eq_true, ↓reduceIte]
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩ <;> simp only [hkey] at hstep
    · refine ⟨hs.posA, hstep.1, hs.prefixA, ?_⟩
      simpa [SCKAScheme.recvBUpdate, hstep.2] using hs.prefixB
    · refine ⟨hs.posA, hstep.1, hs.prefixA, ?_⟩
      simpa [SCKAScheme.recvBUpdate, hstep.2.1, hstep.2.2] using
        SCKAScheme.update_succ_ne_none_iff hs.prefixB key
  · simp only [GameState.stateAt, ↓reduceIte] at hstep
    simp only [recvUpdate, ↓reduceIte]
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩ <;> simp only [hkey] at hstep
    · refine ⟨hstep.1, hs.posB, ?_, hs.prefixB⟩
      simpa [SCKAScheme.recvAUpdate, hstep.2] using hs.prefixA
    · refine ⟨hstep.1, hs.posB, ?_, hs.prefixB⟩
      simpa [SCKAScheme.recvAUpdate, hstep.2.1, hstep.2.2] using
        SCKAScheme.update_succ_ne_none_iff hs.prefixA key

end Braid
