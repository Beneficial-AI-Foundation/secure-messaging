import SecureMessaging.SCKA.MLKEMBraid.Correctness.KeyPrefixes
import SecureMessaging.SCKA.MLKEMBraid.Correctness.MessageReports

open OracleSpec OracleComp

namespace MLKEMBraid

/-- A supported send preserves the negotiation epoch, records it in the message,
and sends `Ct2` only after completing that epoch. -/
theorem send_epoch_fields_of_mem_support
    (P : Parameters ProbComp)
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
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

/-- A successful receive preserves the peer-relative negotiation-epoch bound. -/
theorem receive_epoch_le_of_eq_ok
    (P : Parameters ProbComp) [DecidableEq P.Sym]
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
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

private theorem state_epoch_le_completedEpoch_add_one
    {P : Parameters ProbComp} {AuthState : Type}
    (st : State P AuthState) :
    st.epoch ≤ st.completedEpoch + 1 := by
  cases st <;> simp [State.epoch, State.completedEpoch] <;> omega

private theorem send_completedEpoch_mono
    (P : Parameters ProbComp)
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : State P AuthState) (hpos : 0 < st.epoch)
    (r : SendResult P AuthState)
    (hr : r ∈ support (send P auth st)) :
    st.completedEpoch ≤ r.state.completedEpoch := by
  have hstep := send_completedEpoch_of_mem_support P auth st hpos r hr
  cases hkey : r.outputKey <;> simp only [hkey] at hstep
  all_goals omega

private theorem receive_completedEpoch_mono
    (P : Parameters ProbComp) [DecidableEq P.Sym]
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (st : State P AuthState) (hpos : 0 < st.epoch)
    (msg : Message P.Sym) (r : RecvResult P AuthState)
    (hr : receive P auth st msg = .ok r) :
    st.completedEpoch ≤ r.state.completedEpoch := by
  have hstep := receive_completedEpoch_of_eq_ok P auth st hpos msg r hr
  cases hkey : r.outputKey <;> simp only [hkey] at hstep
  all_goals omega

private theorem recvSCKA_parts
    {P : Parameters ProbComp} [DecidableEq P.Sym]
    {InitKey AuthState : Type}
    {auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac}
    (st : State P AuthState) (msg : Message P.Sym)
    (keyOpt : Option (ℕ × P.EpochKey)) (treport : ℕ)
    (st' : State P AuthState)
    (hrecv : recvSCKA P auth st msg = some (keyOpt, treport, st')) :
    ∃ r, receive P auth st msg = .ok r ∧
      r.outputKey = keyOpt ∧ r.state = st' ∧
      treport = msg.epoch - 1 := by
  cases hraw : receive P auth st msg with
  | error err => simp [recvSCKA, hraw] at hrecv
  | ok r =>
      have hparts :
          r.outputKey = keyOpt ∧
            msg.epoch - 1 = treport ∧ r.state = st' := by
        simpa [recvSCKA, hraw] using hrecv
      exact ⟨r, rfl, hparts.1, hparts.2.2, hparts.2.1.symm⟩

private theorem keyPrefix_all
    {α : Type} (key : ℕ → Option α) (c tcur : ℕ)
    (hkey : ∀ t, key t ≠ none ↔ 0 < t ∧ t ≤ c)
    (htcur : tcur ≤ c) :
    (List.range (tcur + 1)).all
      (fun t => t = 0 || (key t).isSome) = true := by
  rw [List.all_eq_true]
  intro t ht
  have htle : t ≤ tcur := by simpa using List.mem_range.mp ht
  by_cases ht0 : t = 0
  · simp [ht0]
  have hne := (hkey t).2 ⟨Nat.pos_of_ne_zero ht0, htle.trans htcur⟩
  have his : (key t).isSome := Option.isSome_iff_ne_none.mpr hne
  simp [ht0, his]

def EpochKnowledgeInv
    {P : Parameters ProbComp} {AuthState : Type}
    (s : SCKAScheme.GameState
      (State P AuthState) (State P AuthState)
      P.EpochKey (Message P.Sym)) : Prop :=
  KeyPrefixInv s ∧
    s.stA.epoch ≤ s.stB.completedEpoch + 1 ∧
    s.stB.epoch ≤ s.stA.completedEpoch + 1 ∧
    s.tcurA ≤ s.stA.completedEpoch ∧
    s.tcurB ≤ s.stB.completedEpoch ∧
    (∀ (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ),
      s.msgA n = some (msg, tsnd) →
        msg.epoch ≤ s.stA.completedEpoch + 1 ∧
        msg.epoch ≤ s.stB.completedEpoch + 1 ∧
        (msg.type = .ct2 → msg.epoch ≤ s.stA.completedEpoch)) ∧
    (∀ (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ),
      s.msgB n = some (msg, tsnd) →
        msg.epoch ≤ s.stB.completedEpoch + 1 ∧
        msg.epoch ≤ s.stA.completedEpoch + 1 ∧
        (msg.type = .ct2 → msg.epoch ≤ s.stB.completedEpoch))

theorem epochKnowledgeInv_initGameState
    (P : Parameters ProbComp)
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (ik : InitKey) :
    EpochKnowledgeInv
      (SCKAScheme.initGameState
        (I := P.EpochKey) (Rho := Message P.Sym)
        (initA P auth ik) (initB P auth ik)) := by
  refine ⟨keyPrefixInv_initGameState P auth ik, ?_⟩
  simp [SCKAScheme.initGameState, initA, initB,
    State.epoch, State.completedEpoch]

theorem correctnessImpl_preserves_epochKnowledgeInv
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
      EpochKnowledgeInv := by
  let scka := scheme P auth irl sampleInitKey
  have hUnif : QueryImpl.PreservesInv
      (SCKAScheme.oracleUnif
        (State P AuthState) (State P AuthState) P.EpochKey
        (Message P.Sym)) EpochKnowledgeInv := by
    intro n s hs z hz
    have hz' : ∃ y : unifSpec.Range n, (y, s) = z := by
      simpa [SCKAScheme.oracleUnif] using hz
    rcases hz' with ⟨_, rfl⟩
    exact hs
  have hSendA
      (_ : Unit)
      (s : SCKAScheme.GameState
        (State P AuthState) (State P AuthState)
        P.EpochKey (Message P.Sym))
      (hs : EpochKnowledgeInv s)
      (z : Option (ℕ × Option ℕ × Message P.Sym) ×
        SCKAScheme.GameState
          (State P AuthState) (State P AuthState)
          P.EpochKey (Message P.Sym))
      (hz : z ∈ support ((SCKAScheme.oracleSendA scka ()).run s))
      (hprefix' : KeyPrefixInv z.2) :
      EpochKnowledgeInv z.2 := by
    rcases hs with ⟨hprefix, hAB, hBA, htA, htB, hmsgA, hmsgB⟩
    rcases hprefix with ⟨hposA, _, _, _⟩
    rw [SCKAScheme.oracleSendA, StateT.run_bind, StateT.run_get] at hz
    simp only [scheme, bind_pure_comp, liftM_map, bind_map_left,
      StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind,
      support_bind, Set.mem_iUnion, exists_prop, scka] at hz
    obtain ⟨r, hr, hz⟩ := hz
    let msgA' := Function.update s.msgA (s.nA + 1)
      (some (r.msg, r.sendingEpoch))
    have hfields := send_epoch_fields_of_mem_support P auth s.stA r hr
    have hmono := send_completedEpoch_mono P auth s.stA hposA r hr
    have hlocal := state_epoch_le_completedEpoch_add_one s.stA
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
    cases hkey : r.outputKey with
    | none =>
        simp only [hkey, StateT.run_map, StateT.run_set, map_pure,
          support_pure, Set.mem_singleton_iff] at hz
        subst z
        exact ⟨hprefix', hcrossA, hcrossB, htA', htB, hmsgA', hmsgB'⟩
    | some keyPair =>
        rcases keyPair with ⟨tI, key⟩
        simp only [hkey, StateT.run_map, StateT.run_set, map_pure,
          support_pure, Set.mem_singleton_iff] at hz
        subst z
        exact ⟨hprefix', hcrossA, hcrossB, htA', htB, hmsgA', hmsgB'⟩
  have hSendB
      (_ : Unit)
      (s : SCKAScheme.GameState
        (State P AuthState) (State P AuthState)
        P.EpochKey (Message P.Sym))
      (hs : EpochKnowledgeInv s)
      (z : Option (ℕ × Option ℕ × Message P.Sym) ×
        SCKAScheme.GameState
          (State P AuthState) (State P AuthState)
          P.EpochKey (Message P.Sym))
      (hz : z ∈ support ((SCKAScheme.oracleSendB scka ()).run s))
      (hprefix' : KeyPrefixInv z.2) :
      EpochKnowledgeInv z.2 := by
    rcases hs with ⟨hprefix, hAB, hBA, htA, htB, hmsgA, hmsgB⟩
    rcases hprefix with ⟨_, hposB, _, _⟩
    rw [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get] at hz
    simp only [scheme, bind_pure_comp, liftM_map, bind_map_left,
      StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind,
      support_bind, Set.mem_iUnion, exists_prop, scka] at hz
    obtain ⟨r, hr, hz⟩ := hz
    let msgB' := Function.update s.msgB (s.nB + 1)
      (some (r.msg, r.sendingEpoch))
    have hfields := send_epoch_fields_of_mem_support P auth s.stB r hr
    have hmono := send_completedEpoch_mono P auth s.stB hposB r hr
    have hlocal := state_epoch_le_completedEpoch_add_one s.stB
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
    cases hkey : r.outputKey with
    | none =>
        simp only [hkey, StateT.run_map, StateT.run_set, map_pure,
          support_pure, Set.mem_singleton_iff] at hz
        subst z
        exact ⟨hprefix', hcrossA, hcrossB, htA, htB', hmsgA', hmsgB'⟩
    | some keyPair =>
        rcases keyPair with ⟨tI, key⟩
        simp only [hkey, StateT.run_map, StateT.run_set, map_pure,
          support_pure, Set.mem_singleton_iff] at hz
        subst z
        exact ⟨hprefix', hcrossA, hcrossB, htA, htB', hmsgA', hmsgB'⟩
  have hRecvA
      (n : ℕ)
      (s : SCKAScheme.GameState
        (State P AuthState) (State P AuthState)
        P.EpochKey (Message P.Sym))
      (hs : EpochKnowledgeInv s)
      (z : Option (ℕ × Option ℕ) ×
        SCKAScheme.GameState
          (State P AuthState) (State P AuthState)
          P.EpochKey (Message P.Sym))
      (hz : z ∈ support ((SCKAScheme.oracleRecvA scka n).run s))
      (hprefix' : KeyPrefixInv z.2) :
      EpochKnowledgeInv z.2 := by
    rcases hs with ⟨hprefix, hAB, hBA, htA, htB, hmsgA, hmsgB⟩
    rcases hprefix with ⟨hposA, _, _, _⟩
    rcases hentry : s.msgB n with _ | ⟨msg, tsnd⟩
    · simp only [SCKAScheme.oracleRecvA, bind_pure_comp,
        StateT.run_bind, StateT.run_get, pure_bind, hentry,
        StateT.run_pure, support_pure] at hz
      subst z
      exact ⟨hprefix', hAB, hBA, htA, htB, hmsgA, hmsgB⟩
    rcases hrecv : recvSCKA P auth s.stA msg with
      _ | ⟨keyOpt, treport, stA'⟩
    · simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp,
        StateT.run_bind, StateT.run_get, pure_bind, hentry, hrecv,
        StateT.run_map, StateT.run_set, map_pure, support_pure,
        scka] at hz
      subst z
      exact ⟨hprefix', hAB, hBA, htA, htB, hmsgA, hmsgB⟩
    obtain ⟨r, hraw, hout, hstate, hreport⟩ :=
      recvSCKA_parts s.stA msg keyOpt treport stA' hrecv
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
    · simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp,
        StateT.run_bind, StateT.run_get, pure_bind, hentry, hrecv, hkey,
        StateT.run_map, StateT.run_set, map_pure, support_pure,
        scka] at hz
      subst z
      exact ⟨hprefix', hcrossA, hcrossB, htA', htB, hmsgA', hmsgB'⟩
    · simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp,
        StateT.run_bind, StateT.run_get, pure_bind, hentry, hrecv, hkey,
        StateT.run_map, StateT.run_set, map_pure, support_pure,
        scka] at hz
      subst z
      exact ⟨hprefix', hcrossA, hcrossB, htA', htB, hmsgA', hmsgB'⟩
  have hRecvB
      (n : ℕ)
      (s : SCKAScheme.GameState
        (State P AuthState) (State P AuthState)
        P.EpochKey (Message P.Sym))
      (hs : EpochKnowledgeInv s)
      (z : Option (ℕ × Option ℕ) ×
        SCKAScheme.GameState
          (State P AuthState) (State P AuthState)
          P.EpochKey (Message P.Sym))
      (hz : z ∈ support ((SCKAScheme.oracleRecvB scka n).run s))
      (hprefix' : KeyPrefixInv z.2) :
      EpochKnowledgeInv z.2 := by
    rcases hs with ⟨hprefix, hAB, hBA, htA, htB, hmsgA, hmsgB⟩
    rcases hprefix with ⟨_, hposB, _, _⟩
    rcases hentry : s.msgA n with _ | ⟨msg, tsnd⟩
    · simp only [SCKAScheme.oracleRecvB, bind_pure_comp,
        StateT.run_bind, StateT.run_get, pure_bind, hentry,
        StateT.run_pure, support_pure] at hz
      subst z
      exact ⟨hprefix', hAB, hBA, htA, htB, hmsgA, hmsgB⟩
    rcases hrecv : recvSCKA P auth s.stB msg with
      _ | ⟨keyOpt, treport, stB'⟩
    · simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp,
        StateT.run_bind, StateT.run_get, pure_bind, hentry, hrecv,
        StateT.run_map, StateT.run_set, map_pure, support_pure,
        scka] at hz
      subst z
      exact ⟨hprefix', hAB, hBA, htA, htB, hmsgA, hmsgB⟩
    obtain ⟨r, hraw, hout, hstate, hreport⟩ :=
      recvSCKA_parts s.stB msg keyOpt treport stB' hrecv
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
    · simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp,
        StateT.run_bind, StateT.run_get, pure_bind, hentry, hrecv, hkey,
        StateT.run_map, StateT.run_set, map_pure, support_pure,
        scka] at hz
      subst z
      exact ⟨hprefix', hcrossA, hcrossB, htA, htB', hmsgA', hmsgB'⟩
    · simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp,
        StateT.run_bind, StateT.run_get, pure_bind, hentry, hrecv, hkey,
        StateT.run_map, StateT.run_set, map_pure, support_pure,
        scka] at hz
      subst z
      exact ⟨hprefix', hcrossA, hcrossB, htA, htB', hmsgA', hmsgB'⟩
  intro t s hs z hz
  have hprefix' : KeyPrefixInv z.2 :=
    correctnessImpl_preserves_keyPrefixInv P auth irl sampleInitKey
      t s hs.1 z hz
  match t with
  | SCKAScheme.sckaCorrectnessSpec.OUnif n =>
      simpa [SCKAScheme.sckaCorrectnessImpl, scka] using
        hUnif n s hs z hz
  | SCKAScheme.sckaCorrectnessSpec.OSendA =>
      simpa [SCKAScheme.sckaCorrectnessImpl, scka] using
        hSendA () s hs z hz hprefix'
  | SCKAScheme.sckaCorrectnessSpec.OSendB =>
      simpa [SCKAScheme.sckaCorrectnessImpl, scka] using
        hSendB () s hs z hz hprefix'
  | SCKAScheme.sckaCorrectnessSpec.ORecvA n =>
      simpa [SCKAScheme.sckaCorrectnessImpl, scka] using
        hRecvA n s hs z hz hprefix'
  | SCKAScheme.sckaCorrectnessSpec.ORecvB n =>
      simpa [SCKAScheme.sckaCorrectnessImpl, scka] using
        hRecvB n s hs z hz hprefix'

theorem correctness_run_known_prefix
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
      EpochKnowledgeInv z.2 ∧
        (List.range (z.2.tcurA + 1)).all
          (fun t => t = 0 || (z.2.keyA t).isSome) = true ∧
        (List.range (z.2.tcurB + 1)).all
          (fun t => t = 0 || (z.2.keyB t).isSome) = true) ∧
    (∀ (s : SCKAScheme.GameState
        (State P AuthState) (State P AuthState)
        P.EpochKey (Message P.Sym)),
      EpochKnowledgeInv s →
        ∀ t z,
          z ∈ support
            (((SCKAScheme.sckaCorrectnessImpl scka) t).run s) →
          (List.range (z.2.tcurA + 1)).all
            (fun t => t = 0 || (z.2.keyA t).isSome) = true ∧
          (List.range (z.2.tcurB + 1)).all
            (fun t => t = 0 || (z.2.keyB t).isSome) = true) := by
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
    have hinv := OracleComp.simulateQ_run_preservesInv
      (impl := SCKAScheme.sckaCorrectnessImpl
        (scheme P auth irl sampleInitKey))
      (Inv := EpochKnowledgeInv)
      (correctnessImpl_preserves_epochKnowledgeInv P auth irl sampleInitKey)
      adv
      (SCKAScheme.initGameState (initA P auth ik) (initB P auth ik))
      (epochKnowledgeInv_initGameState P auth ik)
      z
      hz
    rcases hinv with
      ⟨⟨hposA, hposB, hkeyA, hkeyB⟩, hAB, hBA, htA, htB, hmsgA, hmsgB⟩
    exact ⟨⟨⟨hposA, hposB, hkeyA, hkeyB⟩,
        hAB, hBA, htA, htB, hmsgA, hmsgB⟩,
      keyPrefix_all z.2.keyA z.2.stA.completedEpoch z.2.tcurA hkeyA htA,
      keyPrefix_all z.2.keyB z.2.stB.completedEpoch z.2.tcurB hkeyB htB⟩
  · intro s hs t z hz
    have hinv := correctnessImpl_preserves_epochKnowledgeInv
      P auth irl sampleInitKey t s hs z hz
    rcases hinv with ⟨⟨_, _, hkeyA, hkeyB⟩, _, _, htA, htB, _, _⟩
    exact ⟨
      keyPrefix_all z.2.keyA z.2.stA.completedEpoch z.2.tcurA hkeyA htA,
      keyPrefix_all z.2.keyB z.2.stB.completedEpoch z.2.tcurB hkeyB htB⟩

end MLKEMBraid
