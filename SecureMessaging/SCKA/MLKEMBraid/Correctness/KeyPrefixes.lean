/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Correctness.Oracles

/-!
# Key prefixes in the Braid correctness game

`State.completedEpoch` is the last epoch whose key a party has computed. A send or a successful
receive either keeps it, or outputs the key of the next epoch and completes that epoch.
`KeyPrefixInv` states that both epochs are positive and that each party has output keys for
exactly the epochs from `1` through its completed epoch. Every oracle of the correctness game
preserves it.
-/

open OracleSpec OracleComp

namespace MLKEMBraid

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

/-- Every oracle of the correctness game preserves `KeyPrefixInv`. -/
theorem correctnessImpl_preserves_keyPrefixInv
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (irl : P.kem.IncrementalRandLeak P.inc) (sampleInitKey : ProbComp InitKey) :
    QueryImpl.PreservesInv
      (SCKAScheme.sckaCorrectnessImpl (scheme P auth irl sampleInitKey)) KeyPrefixInv := by
  refine SCKAScheme.sckaCorrectnessImpl_preservesInv _ ?_ ?_ ?_ ?_
  -- Sends: the sender's completed epoch and key table change together.
  · intro _ s hs z hz
    obtain ⟨r, hr, rfl⟩ := (mem_support_oracleSendA_run_iff auth irl sampleInitKey s z).mp hz
    have hedge := (mem_support_send_iff auth).mp hr
    have hpos : 0 < r.state.epoch := hedge.epoch_eq.1 ▸ hs.posA
    have hstep := hedge.completedEpoch hs.posA
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩ <;> simp only [hkey] at hstep
    · refine ⟨hpos, hs.posB, ?_, hs.prefixB⟩
      simpa [SCKAScheme.sendAUpdate, hstep] using hs.prefixA
    · refine ⟨hpos, hs.posB, ?_, hs.prefixB⟩
      simpa [SCKAScheme.sendAUpdate, hstep.1, hstep.2] using
        SCKAScheme.update_succ_ne_none_iff hs.prefixA key
  · intro _ s hs z hz
    obtain ⟨r, hr, rfl⟩ := (mem_support_oracleSendB_run_iff auth irl sampleInitKey s z).mp hz
    have hedge := (mem_support_send_iff auth).mp hr
    have hpos : 0 < r.state.epoch := hedge.epoch_eq.1 ▸ hs.posB
    have hstep := hedge.completedEpoch hs.posB
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩ <;> simp only [hkey] at hstep
    · refine ⟨hs.posA, hpos, hs.prefixA, ?_⟩
      simpa [SCKAScheme.sendBUpdate, hstep] using hs.prefixB
    · refine ⟨hs.posA, hpos, hs.prefixA, ?_⟩
      simpa [SCKAScheme.sendBUpdate, hstep.1, hstep.2] using
        SCKAScheme.update_succ_ne_none_iff hs.prefixB key
  -- Receives: a missing record or a refusal leaves both tables unchanged.
  · intro n s hs z hz
    rcases oracleRecvA_run_cases auth irl sampleInitKey hz with
      ⟨-, rfl⟩ | ⟨msg, tsnd, err, -, -, rfl⟩ | ⟨msg, tsnd, r, -, hraw, rfl⟩
    · exact hs
    · exact ⟨hs.posA, hs.posB, hs.prefixA, hs.prefixB⟩
    have hstep := (ReceiveEdge.of_eq_ok auth hraw).completedEpoch hs.posA
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩ <;> simp only [hkey] at hstep
    · refine ⟨hstep.1, hs.posB, ?_, hs.prefixB⟩
      simpa [SCKAScheme.recvAUpdate, hstep.2] using hs.prefixA
    · refine ⟨hstep.1, hs.posB, ?_, hs.prefixB⟩
      simpa [SCKAScheme.recvAUpdate, hstep.2.1, hstep.2.2] using
        SCKAScheme.update_succ_ne_none_iff hs.prefixA key
  · intro n s hs z hz
    rcases oracleRecvB_run_cases auth irl sampleInitKey hz with
      ⟨-, rfl⟩ | ⟨msg, tsnd, err, -, -, rfl⟩ | ⟨msg, tsnd, r, -, hraw, rfl⟩
    · exact hs
    · exact ⟨hs.posA, hs.posB, hs.prefixA, hs.prefixB⟩
    have hstep := (ReceiveEdge.of_eq_ok auth hraw).completedEpoch hs.posB
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩ <;> simp only [hkey] at hstep
    · refine ⟨hs.posA, hstep.1, hs.prefixA, ?_⟩
      simpa [SCKAScheme.recvBUpdate, hstep.2] using hs.prefixB
    · refine ⟨hs.posA, hstep.1, hs.prefixA, ?_⟩
      simpa [SCKAScheme.recvBUpdate, hstep.2.1, hstep.2.2] using
        SCKAScheme.update_succ_ne_none_iff hs.prefixB key

end MLKEMBraid
