/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Correctness
import SecureMessaging.SCKA.MLKEMBraid.Construction
import ToVCVio.Control.StateT

/-!
# Key prefixes in the Braid correctness game

`State.completedEpoch` is the last epoch whose key a party has computed. A send or a successful
receive either keeps it, or outputs the key of the next epoch and completes that epoch.
`KeyPrefixInv` states that both epochs are positive and that each party has output keys for
exactly the epochs from `1` through its completed epoch. Every oracle of the correctness game
preserves it.
-/

open OracleSpec OracleComp

universe u

namespace MLKEMBraid

variable (P : Parameters ProbComp) {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)

/-- The last epoch whose key the party has computed. An encapsulating state from `ct1Sampled` on
has finished its own epoch; every other state has finished only the previous one. -/
def State.completedEpoch
    {m : Type → Type u} [Monad m]
    {P : Parameters m} {AuthState : Type} :
    State P AuthState → ℕ
  | .ct1Sampled e .. => e
  | .ekReceivedCt1Sampled e .. => e
  | .ct1Acknowledged e .. => e
  | .ct2Sampled e .. => e
  | st => st.epoch - 1

/-- A party's completed epoch is at most its epoch. -/
theorem State.completedEpoch_le_epoch
    {m : Type → Type u} [Monad m] {P : Parameters m} {AuthState : Type}
    (st : State P AuthState) :
    st.completedEpoch ≤ st.epoch := by
  cases st <;> simp [State.completedEpoch, State.epoch]

/-- A party has completed at least the epoch before its own. -/
theorem State.epoch_sub_one_le_completedEpoch
    {m : Type → Type u} [Monad m] {P : Parameters m} {AuthState : Type}
    (st : State P AuthState) :
    st.epoch - 1 ≤ st.completedEpoch := by
  cases st <;> simp [State.completedEpoch, State.epoch]

theorem send_completedEpoch_of_mem_support
    (st : State P AuthState)
    (hpos : 0 < st.epoch)
    (r : SendResult P AuthState)
    (hr : r ∈ support (send P auth st)) :
    0 < r.state.epoch ∧
      (match r.outputKey with
       | none => r.state.completedEpoch = st.completedEpoch
       | some (tI, _) =>
           tI = st.completedEpoch + 1 ∧
             r.state.completedEpoch = tI) := by
  cases st
  case keysUnsampled =>
    simp only [send, mem_support_bind_iff] at hr
    obtain ⟨out, _, hr⟩ := hr
    rcases out with ⟨pk, sk⟩
    simp only [mem_support_pure_iff] at hr
    subst r
    simpa [State.epoch, State.completedEpoch] using hpos
  case headerReceived =>
    simp only [send, mem_support_bind_iff] at hr
    obtain ⟨out, _, hr⟩ := hr
    rcases out with ⟨encapsState, ct1, k⟩
    simp only [mem_support_pure_iff] at hr
    subst r
    simp only [State.epoch] at hpos
    simp only [State.epoch, State.completedEpoch, and_true]
    omega
  all_goals
    simp only [send, mem_support_pure_iff] at hr
    subst r
    simpa [State.epoch, State.completedEpoch] using hpos

theorem receive_completedEpoch_of_eq_ok
    [DecidableEq P.Sym]
    (st : State P AuthState)
    (hpos : 0 < st.epoch)
    (msg : Message P.Sym)
    (r : RecvResult P AuthState)
    (hr : receive P auth st msg = .ok r) :
    0 < r.state.epoch ∧
      (match r.outputKey with
       | none => r.state.completedEpoch = st.completedEpoch
       | some (tI, _) =>
           tI = st.completedEpoch + 1 ∧
             r.state.completedEpoch = tI) := by
  cases hst : st <;>
    simp only [hst, State.epoch] at hpos hr ⊢ <;>
    simp only [receive] at hr
  all_goals
    repeat' split at hr
  all_goals cases hr
  all_goals simp only [State.epoch, State.completedEpoch, and_true]
  all_goals repeat' apply And.intro
  all_goals omega

/-- `recvSCKA` accepts `msg` exactly when `receive` succeeds. It then returns the output key and
the successor state of `receive` and reports `msg.epoch - 1`. -/
theorem recvSCKA_eq_some_iff
    {P : Parameters ProbComp} [DecidableEq P.Sym]
    {InitKey AuthState : Type}
    {auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac}
    {st : State P AuthState} {msg : Message P.Sym}
    {keyOpt : Option (ℕ × P.EpochKey)} {treport : ℕ} {st' : State P AuthState} :
    recvSCKA P auth st msg = some (keyOpt, treport, st') ↔
      ∃ r, receive P auth st msg = .ok r ∧
        r.outputKey = keyOpt ∧ r.state = st' ∧ treport = msg.epoch - 1 := by
  cases hraw : receive P auth st msg with
  | error err => simp [recvSCKA, hraw]
  | ok r =>
      simp only [recvSCKA, hraw, Option.some.injEq, Prod.mk.injEq, Except.ok.injEq,
        exists_eq_left']
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h3, h2.symm⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h3.symm, h2⟩

/-- The state of the SCKA correctness game run on two Braid parties. -/
abbrev GameState (P : Parameters ProbComp) (AuthState : Type) : Type :=
  SCKAScheme.GameState (State P AuthState) (State P AuthState) P.EpochKey (Message P.Sym)

/-- Both epochs are positive, and each party has output keys for exactly the epochs from `1`
through its completed epoch. -/
structure KeyPrefixInv
    {P : Parameters ProbComp} {AuthState : Type}
    (s : GameState P AuthState) : Prop where
  /-- A's epoch is positive. -/
  posA : 0 < s.stA.epoch
  /-- B's epoch is positive. -/
  posB : 0 < s.stB.epoch
  /-- A has keys for exactly the epochs from `1` through its completed epoch. -/
  prefixA : ∀ t : ℕ, s.keyA t ≠ none ↔ 0 < t ∧ t ≤ s.stA.completedEpoch
  /-- B has keys for exactly the epochs from `1` through its completed epoch. -/
  prefixB : ∀ t : ℕ, s.keyB t ≠ none ↔ 0 < t ∧ t ≤ s.stB.completedEpoch

theorem keyPrefixInv_initGameState
    (ik : InitKey) :
    KeyPrefixInv
      (SCKAScheme.initGameState
        (I := P.EpochKey) (Rho := Message P.Sym)
        (initA P auth ik) (initB P auth ik)) := by
  constructor <;> simp [SCKAScheme.initGameState, initA, initB,
    State.epoch, State.completedEpoch]
  all_goals omega

theorem correctnessImpl_preserves_keyPrefixInv
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (irl : P.kem.IncrementalRandLeak P.inc)
    (sampleInitKey : ProbComp InitKey) :
    QueryImpl.PreservesInv
      (SCKAScheme.sckaCorrectnessImpl
        (scheme P auth irl sampleInitKey))
      KeyPrefixInv := by
  let scka := scheme P auth irl sampleInitKey
  have hSendA : QueryImpl.PreservesInv
      (SCKAScheme.oracleSendA scka) KeyPrefixInv := by
    intro _ s hs z hz
    rcases hs with ⟨hposA, hposB, hkeyA, hkeyB⟩
    simp only [SCKAScheme.oracleSendA, scheme, bind_pure_comp, liftM_map, bind_map_left, stateTrun,
      support_bind, Set.mem_iUnion, exists_prop, scka] at hz
    obtain ⟨r, hr, hz⟩ := hz
    have hstep := send_completedEpoch_of_mem_support P auth s.stA hposA r hr
    cases hkey : r.outputKey with
    | none =>
        simp only [hkey, StateT.run_map, StateT.run_set, map_pure,
          support_pure, Set.mem_singleton_iff] at hz
        subst z
        rw [hkey] at hstep
        refine ⟨hstep.1, hposB, ?_, hkeyB⟩
        simpa [hstep.2] using hkeyA
    | some keyPair =>
        rcases keyPair with ⟨tI, key⟩
        let keyA' := Function.update s.keyA tI (some key)
        simp only [hkey, StateT.run_map, StateT.run_set, map_pure,
          support_pure, Set.mem_singleton_iff] at hz
        subst z
        simp only [hkey] at hstep
        obtain ⟨hposA', htI, hboundary⟩ := hstep
        refine ⟨hposA', hposB, ?_, hkeyB⟩
        simpa [keyA', htI, hboundary] using
          SCKAScheme.update_succ_ne_none_iff hkeyA key
  have hSendB : QueryImpl.PreservesInv
      (SCKAScheme.oracleSendB scka) KeyPrefixInv := by
    intro _ s hs z hz
    rcases hs with ⟨hposA, hposB, hkeyA, hkeyB⟩
    simp only [SCKAScheme.oracleSendB, scheme, bind_pure_comp, liftM_map, bind_map_left, stateTrun,
      support_bind, Set.mem_iUnion, exists_prop, scka] at hz
    obtain ⟨r, hr, hz⟩ := hz
    have hstep := send_completedEpoch_of_mem_support P auth s.stB hposB r hr
    cases hkey : r.outputKey with
    | none =>
        simp only [hkey, StateT.run_map, StateT.run_set, map_pure,
          support_pure, Set.mem_singleton_iff] at hz
        subst z
        rw [hkey] at hstep
        refine ⟨hposA, hstep.1, hkeyA, ?_⟩
        simpa [hstep.2] using hkeyB
    | some keyPair =>
        rcases keyPair with ⟨tI, key⟩
        let keyB' := Function.update s.keyB tI (some key)
        simp only [hkey, StateT.run_map, StateT.run_set, map_pure,
          support_pure, Set.mem_singleton_iff] at hz
        subst z
        simp only [hkey] at hstep
        obtain ⟨hposB', htI, hboundary⟩ := hstep
        refine ⟨hposA, hposB', hkeyA, ?_⟩
        simpa [keyB', htI, hboundary] using
          SCKAScheme.update_succ_ne_none_iff hkeyB key
  have hRecvA : QueryImpl.PreservesInv
      (SCKAScheme.oracleRecvA scka) KeyPrefixInv := by
    intro n s hs z hz
    rcases hs with ⟨hposA, hposB, hkeyA, hkeyB⟩
    rcases hentry : s.msgB n with _ | ⟨msg, tsnd⟩
    · simp only [SCKAScheme.oracleRecvA, bind_pure_comp, stateTrun, hentry, support_pure,
        Set.mem_singleton_iff] at hz
      subst z
      exact ⟨hposA, hposB, hkeyA, hkeyB⟩
    rcases hrecv : recvSCKA P auth s.stA msg with
      _ | ⟨keyOpt, trcv, stA'⟩
    · simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp, stateTrun, hentry, hrecv,
        StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff, scka] at hz
      subst z
      exact ⟨hposA, hposB, hkeyA, hkeyB⟩
    obtain ⟨r, hraw, hout, hstate, -⟩ := recvSCKA_eq_some_iff.mp hrecv
    have hstep := receive_completedEpoch_of_eq_ok P auth s.stA hposA msg r hraw
    rcases hkey : keyOpt with _ | ⟨tI, key⟩
    · simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp, stateTrun, hentry, hrecv, hkey,
        StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff, scka] at hz
      subst z
      rw [hout, hkey] at hstep
      refine ⟨?_, hposB, ?_, hkeyB⟩
      · simpa only [← hstate] using hstep.1
      · have hboundary : stA'.completedEpoch = s.stA.completedEpoch := by
          simpa only [← hstate] using hstep.2
        simpa [hboundary] using hkeyA
    · let keyA' := Function.update s.keyA tI (some key)
      simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp, stateTrun, hentry, hrecv, hkey,
        StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff, scka] at hz
      subst z
      rw [hout, hkey] at hstep
      obtain ⟨hposA', htI, hboundary⟩ := hstep
      refine ⟨?_, hposB, ?_, hkeyB⟩
      · simpa only [← hstate] using hposA'
      · have hboundary' : stA'.completedEpoch = tI := by
          simpa only [← hstate] using hboundary
        simpa [keyA', htI, hboundary'] using
          SCKAScheme.update_succ_ne_none_iff hkeyA key
  have hRecvB : QueryImpl.PreservesInv
      (SCKAScheme.oracleRecvB scka) KeyPrefixInv := by
    intro n s hs z hz
    rcases hs with ⟨hposA, hposB, hkeyA, hkeyB⟩
    rcases hentry : s.msgA n with _ | ⟨msg, tsnd⟩
    · simp only [SCKAScheme.oracleRecvB, bind_pure_comp, stateTrun, hentry, support_pure,
        Set.mem_singleton_iff] at hz
      subst z
      exact ⟨hposA, hposB, hkeyA, hkeyB⟩
    rcases hrecv : recvSCKA P auth s.stB msg with
      _ | ⟨keyOpt, trcv, stB'⟩
    · simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp, stateTrun, hentry, hrecv,
        StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff, scka] at hz
      subst z
      exact ⟨hposA, hposB, hkeyA, hkeyB⟩
    obtain ⟨r, hraw, hout, hstate, -⟩ := recvSCKA_eq_some_iff.mp hrecv
    have hstep := receive_completedEpoch_of_eq_ok P auth s.stB hposB msg r hraw
    rcases hkey : keyOpt with _ | ⟨tI, key⟩
    · simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp, stateTrun, hentry, hrecv, hkey,
        StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff, scka] at hz
      subst z
      rw [hout, hkey] at hstep
      refine ⟨hposA, ?_, hkeyA, ?_⟩
      · simpa only [← hstate] using hstep.1
      · have hboundary : stB'.completedEpoch = s.stB.completedEpoch := by
          simpa only [← hstate] using hstep.2
        simpa [hboundary] using hkeyB
    · let keyB' := Function.update s.keyB tI (some key)
      simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp, stateTrun, hentry, hrecv, hkey,
        StateT.run_map, map_pure, support_pure, Set.mem_singleton_iff, scka] at hz
      subst z
      rw [hout, hkey] at hstep
      obtain ⟨hposB', htI, hboundary⟩ := hstep
      refine ⟨hposA, ?_, hkeyA, ?_⟩
      · simpa only [← hstate] using hposB'
      · have hboundary' : stB'.completedEpoch = tI := by
          simpa only [← hstate] using hboundary
        simpa [keyB', htI, hboundary'] using
          SCKAScheme.update_succ_ne_none_iff hkeyB key
  exact SCKAScheme.sckaCorrectnessImpl_preservesInv hSendA hSendB hRecvA hRecvB

end MLKEMBraid
