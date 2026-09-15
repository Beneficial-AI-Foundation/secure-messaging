import SecureMessaging.SCKA.MLKEMBraid.Construction

open OracleSpec OracleComp

universe u

namespace MLKEMBraid

def State.completedEpoch
    {m : Type → Type u} [Monad m]
    {P : Parameters m} {AuthState : Type} :
    State P AuthState → ℕ
  | .ct1Sampled e .. => e
  | .ekReceivedCt1Sampled e .. => e
  | .ct1Acknowledged e .. => e
  | .ct2Sampled e .. => e
  | st => st.epoch - 1

theorem send_completedEpoch_of_mem_support
    (P : Parameters ProbComp)
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
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
    (P : Parameters ProbComp) [DecidableEq P.Sym]
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
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

private theorem update_prefix
    {α : Type}
    (key : ℕ → Option α) (c : ℕ)
    (hkey : ∀ t, key t ≠ none ↔ 0 < t ∧ t ≤ c)
    (k : α) :
    ∀ t, Function.update key (c + 1) (some k) t ≠ none ↔
      0 < t ∧ t ≤ c + 1 := by
  intro t
  by_cases ht : t = c + 1
  · subst t
    rw [Function.update_self]
    simp
  · rw [Function.update_of_ne ht, hkey t]
    omega

private theorem next_none
    {α : Type}
    (key : ℕ → Option α) (c : ℕ)
    (hkey : ∀ t, key t ≠ none ↔ 0 < t ∧ t ≤ c) :
    key (c + 1) = none := by
  by_contra hne
  have hinterval := (hkey (c + 1)).1 hne
  omega

private theorem receive_parts
    {P : Parameters ProbComp} [DecidableEq P.Sym]
    {InitKey AuthState : Type}
    {auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac}
    (st : State P AuthState) (msg : Message P.Sym)
    (keyOpt : Option (ℕ × P.EpochKey)) (treport : ℕ)
    (st' : State P AuthState)
    (hrecv : recvSCKA P auth st msg = some (keyOpt, treport, st')) :
    ∃ r, receive P auth st msg = .ok r ∧
      r.outputKey = keyOpt ∧ r.state = st' := by
  cases hraw : receive P auth st msg with
  | error err => simp [recvSCKA, hraw] at hrecv
  | ok r =>
      have hparts :
          r.outputKey = keyOpt ∧
            msg.epoch - 1 = treport ∧ r.state = st' := by
        simpa [recvSCKA, hraw] using hrecv
      exact ⟨r, rfl, hparts.1, hparts.2.2⟩

def KeyPrefixInv
    {P : Parameters ProbComp} {AuthState : Type}
    (s : SCKAScheme.GameState
      (State P AuthState) (State P AuthState)
      P.EpochKey (Message P.Sym)) : Prop :=
  0 < s.stA.epoch ∧
    0 < s.stB.epoch ∧
    (∀ t : ℕ,
      s.keyA t ≠ none ↔
        0 < t ∧ t ≤ s.stA.completedEpoch) ∧
    (∀ t : ℕ,
      s.keyB t ≠ none ↔
        0 < t ∧ t ≤ s.stB.completedEpoch)

theorem keyPrefixInv_initGameState
    (P : Parameters ProbComp)
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (ik : InitKey) :
    KeyPrefixInv
      (SCKAScheme.initGameState
        (I := P.EpochKey) (Rho := Message P.Sym)
        (initA P auth ik) (initB P auth ik)) := by
  simp [KeyPrefixInv, SCKAScheme.initGameState, initA, initB,
    State.epoch, State.completedEpoch]
  omega

theorem correctnessImpl_preserves_keyPrefixInv
    (P : Parameters ProbComp)
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc)
    (sampleInitKey : ProbComp InitKey) :
    QueryImpl.PreservesInv
      (SCKAScheme.sckaCorrectnessImpl
        (scheme P auth irl sampleInitKey))
      KeyPrefixInv := by
  let scka := scheme P auth irl sampleInitKey
  have hUnif : QueryImpl.PreservesInv
      (SCKAScheme.oracleUnif
        (State P AuthState) (State P AuthState) P.EpochKey (Message P.Sym))
      KeyPrefixInv := by
    intro t s hs z hz
    have hz' : ∃ y : unifSpec.Range t, (y, s) = z := by
      simpa [SCKAScheme.oracleUnif] using hz
    rcases hz' with ⟨_, rfl⟩
    exact hs
  have hSendA : QueryImpl.PreservesInv
      (SCKAScheme.oracleSendA scka) KeyPrefixInv := by
    intro _ s hs z hz
    rcases hs with ⟨hposA, hposB, hkeyA, hkeyB⟩
    rw [SCKAScheme.oracleSendA, StateT.run_bind, StateT.run_get] at hz
    simp only [scheme, bind_pure_comp, liftM_map, bind_map_left,
      StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind,
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
          update_prefix s.keyA s.stA.completedEpoch hkeyA key
  have hSendB : QueryImpl.PreservesInv
      (SCKAScheme.oracleSendB scka) KeyPrefixInv := by
    intro _ s hs z hz
    rcases hs with ⟨hposA, hposB, hkeyA, hkeyB⟩
    rw [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get] at hz
    simp only [scheme, bind_pure_comp, liftM_map, bind_map_left,
      StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind,
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
          update_prefix s.keyB s.stB.completedEpoch hkeyB key
  have hRecvA : QueryImpl.PreservesInv
      (SCKAScheme.oracleRecvA scka) KeyPrefixInv := by
    intro n s hs z hz
    rcases hs with ⟨hposA, hposB, hkeyA, hkeyB⟩
    rcases hentry : s.msgB n with _ | ⟨msg, tsnd⟩
    · simp only [SCKAScheme.oracleRecvA, bind_pure_comp, StateT.run_bind,
        StateT.run_get, pure_bind, hentry, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst z
      exact ⟨hposA, hposB, hkeyA, hkeyB⟩
    rcases hrecv : recvSCKA P auth s.stA msg with
      _ | ⟨keyOpt, trcv, stA'⟩
    · simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp,
        StateT.run_bind, StateT.run_get, pure_bind, hentry, hrecv,
        StateT.run_map, StateT.run_set, map_pure, support_pure,
        Set.mem_singleton_iff, scka] at hz
      subst z
      exact ⟨hposA, hposB, hkeyA, hkeyB⟩
    obtain ⟨r, hraw, hout, hstate⟩ :=
      receive_parts s.stA msg keyOpt trcv stA' hrecv
    have hstep := receive_completedEpoch_of_eq_ok P auth s.stA hposA msg r hraw
    rcases hkey : keyOpt with _ | ⟨tI, key⟩
    · simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp,
        StateT.run_bind, StateT.run_get, pure_bind, hentry, hrecv, hkey,
        StateT.run_map, StateT.run_set, map_pure, support_pure,
        Set.mem_singleton_iff, scka] at hz
      subst z
      rw [hout, hkey] at hstep
      refine ⟨?_, hposB, ?_, hkeyB⟩
      · simpa only [← hstate] using hstep.1
      · have hboundary : stA'.completedEpoch = s.stA.completedEpoch := by
          simpa only [← hstate] using hstep.2
        simpa [hboundary] using hkeyA
    · let keyA' := Function.update s.keyA tI (some key)
      simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp,
        StateT.run_bind, StateT.run_get, pure_bind, hentry, hrecv, hkey,
        StateT.run_map, StateT.run_set, map_pure, support_pure,
        Set.mem_singleton_iff, scka] at hz
      subst z
      rw [hout, hkey] at hstep
      obtain ⟨hposA', htI, hboundary⟩ := hstep
      refine ⟨?_, hposB, ?_, hkeyB⟩
      · simpa only [← hstate] using hposA'
      · have hboundary' : stA'.completedEpoch = tI := by
          simpa only [← hstate] using hboundary
        simpa [keyA', htI, hboundary'] using
          update_prefix s.keyA s.stA.completedEpoch hkeyA key
  have hRecvB : QueryImpl.PreservesInv
      (SCKAScheme.oracleRecvB scka) KeyPrefixInv := by
    intro n s hs z hz
    rcases hs with ⟨hposA, hposB, hkeyA, hkeyB⟩
    rcases hentry : s.msgA n with _ | ⟨msg, tsnd⟩
    · simp only [SCKAScheme.oracleRecvB, bind_pure_comp, StateT.run_bind,
        StateT.run_get, pure_bind, hentry, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst z
      exact ⟨hposA, hposB, hkeyA, hkeyB⟩
    rcases hrecv : recvSCKA P auth s.stB msg with
      _ | ⟨keyOpt, trcv, stB'⟩
    · simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp,
        StateT.run_bind, StateT.run_get, pure_bind, hentry, hrecv,
        StateT.run_map, StateT.run_set, map_pure, support_pure,
        Set.mem_singleton_iff, scka] at hz
      subst z
      exact ⟨hposA, hposB, hkeyA, hkeyB⟩
    obtain ⟨r, hraw, hout, hstate⟩ :=
      receive_parts s.stB msg keyOpt trcv stB' hrecv
    have hstep := receive_completedEpoch_of_eq_ok P auth s.stB hposB msg r hraw
    rcases hkey : keyOpt with _ | ⟨tI, key⟩
    · simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp,
        StateT.run_bind, StateT.run_get, pure_bind, hentry, hrecv, hkey,
        StateT.run_map, StateT.run_set, map_pure, support_pure,
        Set.mem_singleton_iff, scka] at hz
      subst z
      rw [hout, hkey] at hstep
      refine ⟨hposA, ?_, hkeyA, ?_⟩
      · simpa only [← hstate] using hstep.1
      · have hboundary : stB'.completedEpoch = s.stB.completedEpoch := by
          simpa only [← hstate] using hstep.2
        simpa [hboundary] using hkeyB
    · let keyB' := Function.update s.keyB tI (some key)
      simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp,
        StateT.run_bind, StateT.run_get, pure_bind, hentry, hrecv, hkey,
        StateT.run_map, StateT.run_set, map_pure, support_pure,
        Set.mem_singleton_iff, scka] at hz
      subst z
      rw [hout, hkey] at hstep
      obtain ⟨hposB', htI, hboundary⟩ := hstep
      refine ⟨hposA, ?_, hkeyA, ?_⟩
      · simpa only [← hstate] using hposB'
      · have hboundary' : stB'.completedEpoch = tI := by
          simpa only [← hstate] using hboundary
        simpa [keyB', htI, hboundary'] using
          update_prefix s.keyB s.stB.completedEpoch hkeyB key
  intro t s hs z hz
  match t with
  | SCKAScheme.sckaCorrectnessSpec.OUnif n =>
      simpa [SCKAScheme.sckaCorrectnessImpl, scka] using hUnif n s hs z hz
  | SCKAScheme.sckaCorrectnessSpec.OSendA =>
      simpa [SCKAScheme.sckaCorrectnessImpl, scka] using hSendA () s hs z hz
  | SCKAScheme.sckaCorrectnessSpec.OSendB =>
      simpa [SCKAScheme.sckaCorrectnessImpl, scka] using hSendB () s hs z hz
  | SCKAScheme.sckaCorrectnessSpec.ORecvA n =>
      simpa [SCKAScheme.sckaCorrectnessImpl, scka] using hRecvA n s hs z hz
  | SCKAScheme.sckaCorrectnessSpec.ORecvB n =>
      simpa [SCKAScheme.sckaCorrectnessImpl, scka] using hRecvB n s hs z hz

theorem correctness_run_key_prefixes
    (P : Parameters ProbComp)
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc)
    (sampleInitKey : ProbComp InitKey)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message P.Sym)) :
    let scka := scheme P auth irl sampleInitKey
    (∀ z ∈ support (do
      let ik ← scka.initKeyGen
      let stA ← scka.initA ik
      let stB ← scka.initB ik
      (simulateQ (SCKAScheme.sckaCorrectnessImpl scka) adv).run
        (SCKAScheme.initGameState stA stB)),
      KeyPrefixInv z.2) ∧
    (∀ (s : SCKAScheme.GameState
        (State P AuthState) (State P AuthState)
        P.EpochKey (Message P.Sym)),
      KeyPrefixInv s →
        (∀ (tsnd tI : ℕ) (msg : Message P.Sym)
          (s' : SCKAScheme.GameState
            (State P AuthState) (State P AuthState)
            P.EpochKey (Message P.Sym)),
          (some (tsnd, some tI, msg), s') ∈
            support ((SCKAScheme.oracleSendA scka ()).run s) →
          s.keyA tI = none) ∧
        (∀ (tsnd tI : ℕ) (msg : Message P.Sym)
          (s' : SCKAScheme.GameState
            (State P AuthState) (State P AuthState)
            P.EpochKey (Message P.Sym)),
          (some (tsnd, some tI, msg), s') ∈
            support ((SCKAScheme.oracleSendB scka ()).run s) →
          s.keyB tI = none) ∧
        (∀ (n trcv tI : ℕ)
          (s' : SCKAScheme.GameState
            (State P AuthState) (State P AuthState)
            P.EpochKey (Message P.Sym)),
          (some (trcv, some tI), s') ∈
            support ((SCKAScheme.oracleRecvA scka n).run s) →
          s.keyA tI = none) ∧
        (∀ (n trcv tI : ℕ)
          (s' : SCKAScheme.GameState
            (State P AuthState) (State P AuthState)
            P.EpochKey (Message P.Sym)),
          (some (trcv, some tI), s') ∈
            support ((SCKAScheme.oracleRecvB scka n).run s) →
          s.keyB tI = none)) := by
  dsimp only
  constructor
  · intro z hz
    rw [mem_support_bind_iff] at hz
    obtain ⟨ik, _, hz⟩ := hz
    rw [mem_support_bind_iff] at hz
    obtain ⟨stA, hstA, hz⟩ := hz
    rw [mem_support_bind_iff] at hz
    obtain ⟨stB, hstB, hz⟩ := hz
    have hstA' : stA = initA P auth ik := by
      simpa [scheme, mem_support_pure_iff] using hstA
    have hstB' : stB = initB P auth ik := by
      simpa [scheme, mem_support_pure_iff] using hstB
    subst stA
    subst stB
    exact OracleComp.simulateQ_run_preservesInv
      (impl := SCKAScheme.sckaCorrectnessImpl
        (scheme P auth irl sampleInitKey))
      (Inv := KeyPrefixInv)
      (correctnessImpl_preserves_keyPrefixInv P auth irl sampleInitKey)
      adv
      (SCKAScheme.initGameState (initA P auth ik) (initB P auth ik))
      (keyPrefixInv_initGameState P auth ik)
      z
      hz
  · intro s hs
    rcases hs with ⟨hposA, hposB, hkeyA, hkeyB⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro tsnd tI msg s' hz
      rw [SCKAScheme.oracleSendA, StateT.run_bind, StateT.run_get] at hz
      simp only [scheme, bind_pure_comp, liftM_map, bind_map_left,
        StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind,
        support_bind, Set.mem_iUnion, exists_prop] at hz
      obtain ⟨r, hr, hz⟩ := hz
      cases hkey : r.outputKey with
      | none =>
          simp only [hkey, StateT.run_map, StateT.run_set, map_pure,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
            Option.some.injEq] at hz
          cases hz.1.2.1
      | some keyPair =>
          rcases keyPair with ⟨tJ, key⟩
          simp only [hkey, StateT.run_map, StateT.run_set, map_pure,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
            Option.some.injEq] at hz
          have hstep :=
            send_completedEpoch_of_mem_support P auth s.stA hposA r hr
          simp only [hkey] at hstep
          obtain ⟨_, htJ, _⟩ := hstep
          rw [hz.1.2.1]
          simpa [htJ] using
            next_none s.keyA s.stA.completedEpoch hkeyA
    · intro tsnd tI msg s' hz
      rw [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get] at hz
      simp only [scheme, bind_pure_comp, liftM_map, bind_map_left,
        StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind,
        support_bind, Set.mem_iUnion, exists_prop] at hz
      obtain ⟨r, hr, hz⟩ := hz
      cases hkey : r.outputKey with
      | none =>
          simp only [hkey, StateT.run_map, StateT.run_set, map_pure,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
            Option.some.injEq] at hz
          cases hz.1.2.1
      | some keyPair =>
          rcases keyPair with ⟨tJ, key⟩
          simp only [hkey, StateT.run_map, StateT.run_set, map_pure,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
            Option.some.injEq] at hz
          have hstep :=
            send_completedEpoch_of_mem_support P auth s.stB hposB r hr
          simp only [hkey] at hstep
          obtain ⟨_, htJ, _⟩ := hstep
          rw [hz.1.2.1]
          simpa [htJ] using
            next_none s.keyB s.stB.completedEpoch hkeyB
    · intro n trcv tI s' hz
      rcases hentry : s.msgB n with _ | ⟨msg, tsnd⟩
      · simp only [SCKAScheme.oracleRecvA, bind_pure_comp, StateT.run_bind,
          StateT.run_get, pure_bind, hentry, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq] at hz
        cases hz.1
      rcases hrecv : recvSCKA P auth s.stA msg with
        _ | ⟨keyOpt, treport, stA'⟩
      · simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp,
          StateT.run_bind, StateT.run_get, pure_bind, hentry, hrecv,
          StateT.run_map, StateT.run_set, map_pure, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq] at hz
        cases hz.1
      obtain ⟨r, hraw, hrawKey, _⟩ :=
        receive_parts s.stA msg keyOpt treport stA' hrecv
      rcases hkey : keyOpt with _ | ⟨tJ, key⟩
      · simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp,
          StateT.run_bind, StateT.run_get, pure_bind, hentry, hrecv, hkey,
          StateT.run_map, StateT.run_set, map_pure, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq,
          Option.some_ne_none, and_false, false_and] at hz
      · simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp,
          StateT.run_bind, StateT.run_get, pure_bind, hentry, hrecv, hkey,
          StateT.run_map, StateT.run_set, map_pure, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hz
        have hstep :=
          receive_completedEpoch_of_eq_ok P auth s.stA hposA msg r hraw
        simp only [hrawKey, hkey] at hstep
        obtain ⟨_, htJ, _⟩ := hstep
        rw [hz.1.2]
        simpa [htJ] using
          next_none s.keyA s.stA.completedEpoch hkeyA
    · intro n trcv tI s' hz
      rcases hentry : s.msgA n with _ | ⟨msg, tsnd⟩
      · simp only [SCKAScheme.oracleRecvB, bind_pure_comp, StateT.run_bind,
          StateT.run_get, pure_bind, hentry, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq] at hz
        cases hz.1
      rcases hrecv : recvSCKA P auth s.stB msg with
        _ | ⟨keyOpt, treport, stB'⟩
      · simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp,
          StateT.run_bind, StateT.run_get, pure_bind, hentry, hrecv,
          StateT.run_map, StateT.run_set, map_pure, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq] at hz
        cases hz.1
      obtain ⟨r, hraw, hrawKey, _⟩ :=
        receive_parts s.stB msg keyOpt treport stB' hrecv
      rcases hkey : keyOpt with _ | ⟨tJ, key⟩
      · simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp,
          StateT.run_bind, StateT.run_get, pure_bind, hentry, hrecv, hkey,
          StateT.run_map, StateT.run_set, map_pure, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq,
          Option.some_ne_none, and_false, false_and] at hz
      · simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp,
          StateT.run_bind, StateT.run_get, pure_bind, hentry, hrecv, hkey,
          StateT.run_map, StateT.run_set, map_pure, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hz
        have hstep :=
          receive_completedEpoch_of_eq_ok P auth s.stB hposB msg r hraw
        simp only [hrawKey, hkey] at hstep
        obtain ⟨_, htJ, _⟩ := hstep
        rw [hz.1.2]
        simpa [htJ] using
          next_none s.keyB s.stB.completedEpoch hkeyB

end MLKEMBraid
