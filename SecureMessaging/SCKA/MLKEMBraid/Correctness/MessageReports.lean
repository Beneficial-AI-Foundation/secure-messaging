import SecureMessaging.SCKA.MLKEMBraid.Construction

open OracleSpec OracleComp

namespace MLKEMBraid

theorem send_report_eq_of_mem_support
    (P : Parameters ProbComp)
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : State P AuthState)
    (r : SendResult P AuthState)
    (hr : r ∈ support (send P auth st)) :
    r.sendingEpoch = r.msg.epoch - 1 := by
  cases st
  case keysUnsampled =>
    simp only [send, mem_support_bind_iff] at hr
    obtain ⟨out, _, hr⟩ := hr
    rcases out with ⟨pk, sk⟩
    simp only [mem_support_pure_iff] at hr
    subst r
    rfl
  case headerReceived =>
    simp only [send, mem_support_bind_iff] at hr
    obtain ⟨out, _, hr⟩ := hr
    rcases out with ⟨encapsState, ct1, k⟩
    simp only [mem_support_pure_iff] at hr
    subst r
    rfl
  all_goals
    simp only [send, mem_support_pure_iff] at hr
    subst r
    rfl

def RecordedReportInv {StA StB I Sym : Type}
    (s : SCKAScheme.GameState StA StB I (Message Sym)) : Prop :=
  (∀ (n : ℕ) (msg : Message Sym) (tsnd : ℕ),
    s.msgA n = some (msg, tsnd) → tsnd = msg.epoch - 1) ∧
  (∀ (n : ℕ) (msg : Message Sym) (tsnd : ℕ),
    s.msgB n = some (msg, tsnd) → tsnd = msg.epoch - 1)

theorem recordedReportInv_initGameState
    {StA StB I Sym : Type}
    (stA : StA) (stB : StB) :
    RecordedReportInv
      (SCKAScheme.initGameState (I := I) (Rho := Message Sym) stA stB) := by
  constructor <;> intro n msg tsnd h <;>
    simp [SCKAScheme.initGameState] at h

theorem correctnessImpl_preserves_recordedReportInv
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
      RecordedReportInv := by
  let scka := scheme P auth irl sampleInitKey
  have hUnif : QueryImpl.PreservesInv
      (SCKAScheme.oracleUnif
        (State P AuthState) (State P AuthState) P.EpochKey (Message P.Sym))
      RecordedReportInv := by
    intro t s hs z hz
    have hz' : ∃ y : unifSpec.Range t, (y, s) = z := by
      simpa [SCKAScheme.oracleUnif] using hz
    rcases hz' with ⟨_, rfl⟩
    exact hs
  have hSendA : QueryImpl.PreservesInv
      (SCKAScheme.oracleSendA scka) RecordedReportInv := by
    intro _ s hs z hz
    have hrecord (r : SendResult P AuthState)
        (hr : r ∈ support (send P auth s.stA)) :
        RecordedReportInv
          {s with
            msgA := Function.update s.msgA (s.nA + 1)
              (some (r.msg, r.sendingEpoch))} := by
      constructor
      · intro n msg tsnd hn
        by_cases hnew : n = s.nA + 1
        · subst n
          simp only [Function.update, ↓reduceDIte, Option.some.injEq,
            Prod.mk.injEq] at hn
          obtain ⟨rfl, rfl⟩ := hn
          exact send_report_eq_of_mem_support P auth s.stA r hr
        · simp only [Function.update, hnew, ↓reduceDIte] at hn
          exact hs.1 n msg tsnd hn
      · exact hs.2
    rw [SCKAScheme.oracleSendA, StateT.run_bind, StateT.run_get] at hz
    simp only [scheme, bind_pure_comp, liftM_map, bind_map_left,
      StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind,
      support_bind, Set.mem_iUnion, exists_prop, scka] at hz
    obtain ⟨r, hr, hz⟩ := hz
    cases hkey : r.outputKey with
    | none =>
        simp [hkey, StateT.run_map, StateT.run_set] at hz
        subst z
        simpa [RecordedReportInv] using hrecord r hr
    | some keyPair =>
        rcases keyPair with ⟨tI, key⟩
        simp [hkey, StateT.run_map, StateT.run_set] at hz
        subst z
        simpa [RecordedReportInv] using hrecord r hr
  have hSendB : QueryImpl.PreservesInv
      (SCKAScheme.oracleSendB scka) RecordedReportInv := by
    intro _ s hs z hz
    have hrecord (r : SendResult P AuthState)
        (hr : r ∈ support (send P auth s.stB)) :
        RecordedReportInv
          {s with
            msgB := Function.update s.msgB (s.nB + 1)
              (some (r.msg, r.sendingEpoch))} := by
      constructor
      · exact hs.1
      · intro n msg tsnd hn
        by_cases hnew : n = s.nB + 1
        · subst n
          simp only [Function.update, ↓reduceDIte, Option.some.injEq,
            Prod.mk.injEq] at hn
          obtain ⟨rfl, rfl⟩ := hn
          exact send_report_eq_of_mem_support P auth s.stB r hr
        · simp only [Function.update, hnew, ↓reduceDIte] at hn
          exact hs.2 n msg tsnd hn
    rw [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get] at hz
    simp only [scheme, bind_pure_comp, liftM_map, bind_map_left,
      StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind,
      support_bind, Set.mem_iUnion, exists_prop, scka] at hz
    obtain ⟨r, hr, hz⟩ := hz
    cases hkey : r.outputKey with
    | none =>
        simp [hkey, StateT.run_map, StateT.run_set] at hz
        subst z
        simpa [RecordedReportInv] using hrecord r hr
    | some keyPair =>
        rcases keyPair with ⟨tI, key⟩
        simp [hkey, StateT.run_map, StateT.run_set] at hz
        subst z
        simpa [RecordedReportInv] using hrecord r hr
  have hRecvA : QueryImpl.PreservesInv
      (SCKAScheme.oracleRecvA scka) RecordedReportInv := by
    intro n s hs z hz
    rcases hentry : s.msgB n with _ | ⟨msg, tsnd⟩
    · have hz' : z = (none, s) := by
        simpa [SCKAScheme.oracleRecvA, hentry, StateT.run_bind,
          StateT.run_get, pure_bind] using hz
      subst z
      exact hs
    rcases hrecv : recvSCKA P auth s.stA msg with
      _ | ⟨keyOpt, trcv, stA'⟩
    · have hz' : z = (none, {s with correct := false}) := by
        simpa [SCKAScheme.oracleRecvA, scka, scheme, hentry, hrecv,
          StateT.run_bind, StateT.run_get, pure_bind] using hz
      subst z
      simpa [RecordedReportInv] using hs
    rcases hkey : keyOpt with _ | ⟨tI, key⟩
    · have hz' : z =
          (some (trcv, none),
            {s with
              stA := stA'
              tcurA := max s.tcurA trcv
              correct := s.correct && (trcv == tsnd) &&
                (List.range (max s.tcurA trcv + 1)).all
                  (fun t => t = 0 || (s.keyA t).isSome)}) := by
        simpa [SCKAScheme.oracleRecvA, scka, scheme, hentry, hrecv,
          hkey, StateT.run_bind, StateT.run_get, pure_bind] using hz
      subst z
      simpa [RecordedReportInv] using hs
    let keyA' := Function.update s.keyA tI (some key)
    have hz' : z =
        (some (trcv, some tI),
          {s with
            stA := stA'
            tcurA := max s.tcurA trcv
            keyA := keyA'
            correct := s.correct && (trcv == tsnd) &&
              (s.keyA tI).isNone &&
              ((s.keyB tI).isNone || s.keyB tI == some key) &&
              (List.range (max s.tcurA trcv + 1)).all
                (fun t => t = 0 || (keyA' t).isSome)}) := by
      simpa [SCKAScheme.oracleRecvA, scka, scheme, hentry, hrecv,
        hkey, keyA', StateT.run_bind, StateT.run_get, pure_bind] using hz
    subst z
    simpa [RecordedReportInv] using hs
  have hRecvB : QueryImpl.PreservesInv
      (SCKAScheme.oracleRecvB scka) RecordedReportInv := by
    intro n s hs z hz
    rcases hentry : s.msgA n with _ | ⟨msg, tsnd⟩
    · have hz' : z = (none, s) := by
        simpa [SCKAScheme.oracleRecvB, hentry, StateT.run_bind,
          StateT.run_get, pure_bind] using hz
      subst z
      exact hs
    rcases hrecv : recvSCKA P auth s.stB msg with
      _ | ⟨keyOpt, trcv, stB'⟩
    · have hz' : z = (none, {s with correct := false}) := by
        simpa [SCKAScheme.oracleRecvB, scka, scheme, hentry, hrecv,
          StateT.run_bind, StateT.run_get, pure_bind] using hz
      subst z
      simpa [RecordedReportInv] using hs
    rcases hkey : keyOpt with _ | ⟨tI, key⟩
    · have hz' : z =
          (some (trcv, none),
            {s with
              stB := stB'
              tcurB := max s.tcurB trcv
              correct := s.correct && (trcv == tsnd) &&
                (List.range (max s.tcurB trcv + 1)).all
                  (fun t => t = 0 || (s.keyB t).isSome)}) := by
        simpa [SCKAScheme.oracleRecvB, scka, scheme, hentry, hrecv,
          hkey, StateT.run_bind, StateT.run_get, pure_bind] using hz
      subst z
      simpa [RecordedReportInv] using hs
    let keyB' := Function.update s.keyB tI (some key)
    have hz' : z =
        (some (trcv, some tI),
          {s with
            stB := stB'
            tcurB := max s.tcurB trcv
            keyB := keyB'
            correct := s.correct && (trcv == tsnd) &&
              (s.keyB tI).isNone &&
              ((s.keyA tI).isNone || s.keyA tI == some key) &&
              (List.range (max s.tcurB trcv + 1)).all
                (fun t => t = 0 || (keyB' t).isSome)}) := by
      simpa [SCKAScheme.oracleRecvB, scka, scheme, hentry, hrecv,
        hkey, keyB', StateT.run_bind, StateT.run_get, pure_bind] using hz
    subst z
    simpa [RecordedReportInv] using hs
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

theorem correctness_run_recorded_reports
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
      RecordedReportInv z.2) ∧
    (∀ (s : SCKAScheme.GameState
        (State P AuthState) (State P AuthState)
        P.EpochKey (Message P.Sym)),
      RecordedReportInv s →
        (∀ (n trcv : ℕ) (tI : Option ℕ)
          (s' : SCKAScheme.GameState
            (State P AuthState) (State P AuthState)
            P.EpochKey (Message P.Sym)),
          (some (trcv, tI), s') ∈
            support ((SCKAScheme.oracleRecvA scka n).run s) →
          ∃ msg, s.msgB n = some (msg, trcv)) ∧
        (∀ (n trcv : ℕ) (tI : Option ℕ)
          (s' : SCKAScheme.GameState
            (State P AuthState) (State P AuthState)
            P.EpochKey (Message P.Sym)),
          (some (trcv, tI), s') ∈
            support ((SCKAScheme.oracleRecvB scka n).run s) →
          ∃ msg, s.msgA n = some (msg, trcv))) := by
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
      (Inv := RecordedReportInv)
      (correctnessImpl_preserves_recordedReportInv P auth irl sampleInitKey)
      adv
      (SCKAScheme.initGameState (initA P auth ik) (initB P auth ik))
      (recordedReportInv_initGameState (I := P.EpochKey)
        (initA P auth ik) (initB P auth ik))
      z
      hz
  · intro s hs
    have recvSCKA_report_eq
        (st : State P AuthState) (msg : Message P.Sym)
        (keyOpt : Option (ℕ × P.EpochKey)) (treport : ℕ)
        (st' : State P AuthState)
        (hrecv : recvSCKA P auth st msg =
          some (keyOpt, treport, st')) :
        treport = msg.epoch - 1 := by
      cases hraw : receive P auth st msg with
      | error err => simp [recvSCKA, hraw] at hrecv
      | ok r =>
          have hparts :
              r.outputKey = keyOpt ∧
                msg.epoch - 1 = treport ∧ r.state = st' := by
            simpa [recvSCKA, hraw] using hrecv
          exact hparts.2.1.symm
    constructor
    · intro n trcv tI s' hz
      rcases hentry : s.msgB n with _ | ⟨msg, tsnd⟩
      · simp [SCKAScheme.oracleRecvA, hentry, StateT.run_bind,
          StateT.run_get, pure_bind] at hz
      rcases hrecv : recvSCKA P auth s.stA msg with
        _ | ⟨keyOpt, treport, stA'⟩
      · simp [SCKAScheme.oracleRecvA, scheme, hentry, hrecv,
          StateT.run_bind, StateT.run_get, StateT.run_map,
          StateT.run_set, pure_bind] at hz
      have htreport :=
        recvSCKA_report_eq s.stA msg keyOpt treport stA' hrecv
      have htrcv : trcv = treport := by
        have hout :
            some (trcv, tI) ∈
              support (Prod.fst <$> ((SCKAScheme.oracleRecvA
                (scheme P auth irl sampleInitKey) n).run s)) := by
          rw [support_map]
          exact ⟨(some (trcv, tI), s'), hz, rfl⟩
        have houtput :
            some (trcv, tI) =
              some (treport, keyOpt.map Prod.fst) := by
          cases hkey : keyOpt <;>
            simpa [SCKAScheme.oracleRecvA, scheme, hentry, hrecv, hkey,
              StateT.run_bind, StateT.run_get, StateT.run_map,
              StateT.run_set, pure_bind] using hout
        exact congrArg Prod.fst (Option.some.inj houtput)
      refine ⟨msg, ?_⟩
      congr 2
      exact (hs.2 n msg tsnd hentry).trans
        (htreport.symm.trans htrcv.symm)
    · intro n trcv tI s' hz
      rcases hentry : s.msgA n with _ | ⟨msg, tsnd⟩
      · simp [SCKAScheme.oracleRecvB, hentry, StateT.run_bind,
          StateT.run_get, pure_bind] at hz
      rcases hrecv : recvSCKA P auth s.stB msg with
        _ | ⟨keyOpt, treport, stB'⟩
      · simp [SCKAScheme.oracleRecvB, scheme, hentry, hrecv,
          StateT.run_bind, StateT.run_get, StateT.run_map,
          StateT.run_set, pure_bind] at hz
      have htreport :=
        recvSCKA_report_eq s.stB msg keyOpt treport stB' hrecv
      have htrcv : trcv = treport := by
        have hout :
            some (trcv, tI) ∈
              support (Prod.fst <$> ((SCKAScheme.oracleRecvB
                (scheme P auth irl sampleInitKey) n).run s)) := by
          rw [support_map]
          exact ⟨(some (trcv, tI), s'), hz, rfl⟩
        have houtput :
            some (trcv, tI) =
              some (treport, keyOpt.map Prod.fst) := by
          cases hkey : keyOpt <;>
            simpa [SCKAScheme.oracleRecvB, scheme, hentry, hrecv, hkey,
              StateT.run_bind, StateT.run_get, StateT.run_map,
              StateT.run_set, pure_bind] using hout
        exact congrArg Prod.fst (Option.some.inj houtput)
      refine ⟨msg, ?_⟩
      congr 2
      exact (hs.1 n msg tsnd hentry).trans
        (htreport.symm.trans htrcv.symm)

end MLKEMBraid
