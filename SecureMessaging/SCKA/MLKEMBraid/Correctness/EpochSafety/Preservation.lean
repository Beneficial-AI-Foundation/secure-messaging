import SecureMessaging.SCKA.MLKEMBraid.Correctness.EpochSafety.Generator
import SecureMessaging.SCKA.MLKEMBraid.Correctness.EpochSafety.Encapsulator

open OracleSpec OracleComp
open ErasureCodePayload.Streaming
open SCKAScheme.sckaCorrectnessSpec

namespace MLKEMBraid

open EpochSafetyInternal

private theorem send_preserves_statePairInv
    (P : Parameters ProbComp)
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (s : SCKAScheme.GameState
      (State P AuthState) (State P AuthState)
      P.EpochKey (Message P.Sym))
    (hs : StatePairInv s)
    (party : Bool)
    (r : SendResult P AuthState)
    (hr : r ∈ support
      (send P auth (if party then s.stA else s.stB))) :
    StatePairInv
      (if party then { s with stA := r.state }
       else { s with stB := r.state }) := by
  have preserveA
      (s : SCKAScheme.GameState
        (State P AuthState) (State P AuthState)
        P.EpochKey (Message P.Sym))
      (hs : StatePairInv s)
      (r : SendResult P AuthState)
      (hr : r ∈ support (send P auth s.stA)) :
      StatePairInv {s with stA := r.state} := by
    cases ha : s.stA
    case keysUnsampled =>
      simp only [ha, send, mem_support_bind_iff] at hr
      obtain ⟨⟨pk, sk⟩, _, hr⟩ := hr
      simp only [mem_support_pure_iff] at hr
      subst r
      cases hb : s.stB <;>
        simp [StatePairInv, ha, hb, State.epoch,
          State.controlPosition] at hs ⊢ <;>
        aesop
    case headerReceived e a header ekDecoder =>
      simp only [ha, send, mem_support_bind_iff] at hr
      obtain ⟨⟨encapsState, ct1, key⟩, _, hr⟩ := hr
      simp only [mem_support_pure_iff] at hr
      subst r
      simp only [StatePairInv]
      intro side
      cases side
      · have hold := hs false
        simp only [Bool.false_eq_true, ↓reduceIte] at hold ⊢
        rw [ha] at hold
        constructor
        · intro hepoch hrole
          have hallowed := hold.1 hepoch hrole
          cases hb : s.stB <;> simp only [hb] at hallowed
          all_goals exact hallowed
        · intro hlag
          rcases hold.2 hlag with ⟨a', enc, b, dec, _, hpeer⟩
          cases hpeer
      · have hold := hs true
        simp only [if_true] at hold ⊢
        rw [ha] at hold
        constructor
        · intro _ hrole
          simp [State.controlPosition] at hrole
        · intro hlag
          rcases hold.2 hlag with ⟨a', enc, b, dec, hst, _⟩
          cases hst
    case ct2Sampled e a enc =>
      simp only [ha, send, mem_support_pure_iff] at hr
      subst r
      simp only [StatePairInv]
      intro side
      cases side
      · have hold := hs false
        simp only [Bool.false_eq_true, ↓reduceIte] at hold ⊢
        rw [ha] at hold
        constructor
        · intro hepoch hrole
          have hallowed := hold.1 hepoch hrole
          cases hb : s.stB <;> simp only [hb] at hallowed
          all_goals exact hallowed
        · intro hlag
          rcases hold.2 hlag with ⟨a', enc', b, dec, _, hpeer⟩
          cases hpeer
      · have hold := hs true
        simp only [if_true] at hold ⊢
        rw [ha] at hold
        constructor
        · intro _ hrole
          simp [State.controlPosition] at hrole
        · intro hlag
          rcases hold.2 hlag with ⟨_, _, b, dec, _, hpeer⟩
          exact ⟨a, enc.nextChunk.2, b, dec, rfl, hpeer⟩
    case noHeaderReceived =>
      simp only [ha, send, mem_support_pure_iff] at hr
      subst r
      rw [← ha]
      exact hs
    all_goals
      simp only [ha, send, mem_support_pure_iff] at hr
      subst r
      simp only [StatePairInv]
      intro side
      cases side
      · have hold := hs false
        simp only [Bool.false_eq_true, ↓reduceIte] at hold ⊢
        rw [ha] at hold
        constructor
        · intro hepoch hrole
          have hallowed := hold.1 hepoch hrole
          cases hb : s.stB <;> simp only [hb] at hallowed
          all_goals exact hallowed
        · intro hlag
          rcases hold.2 hlag with ⟨a', enc, b, dec, _, hpeer⟩
          cases hpeer
      · have hold := hs true
        simp only [if_true] at hold ⊢
        rw [ha] at hold
        constructor
        · intro hepoch hrole
          have hallowed := hold.1 hepoch hrole
          cases hb : s.stB <;> simp only [hb] at hallowed
          all_goals exact hallowed
        · intro hlag
          rcases hold.2 hlag with ⟨a', enc, b, dec, hst, _⟩
          cases hst
  cases party
  · let swapped : SCKAScheme.GameState
        (State P AuthState) (State P AuthState)
        P.EpochKey (Message P.Sym) :=
      { s with stA := s.stB, stB := s.stA }
    have hswapped : StatePairInv swapped := by
      simp only [StatePairInv] at hs ⊢
      intro side
      cases side
      · exact hs true
      · exact hs false
    have hout := preserveA swapped hswapped r (by exact hr)
    simp only [StatePairInv] at hout ⊢
    intro side
    cases side
    · exact hout true
    · exact hout false
  · exact preserveA s hs r (by simpa using hr)

theorem correctnessImpl_preserves_statePairInv
    (P : Parameters ProbComp)
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc)
    (sampleInitKey : ProbComp InitKey) :
    QueryImpl.PreservesInv
      (SCKAScheme.sckaCorrectnessImpl (scheme P auth irl sampleInitKey))
      (fun s => ControlInv s ∧ StatePairInv s) := by
  let scka := scheme P auth irl sampleInitKey
  -- Control preservation is already checked per query. The state pair is preserved by the
  -- retained send theorem for raw send support and by the role theorems for the successful
  -- receive of the recorded message; refusals, missing messages, and uniform queries leave
  -- both protocol states unchanged.
  have hUnif : QueryImpl.PreservesInv
      (SCKAScheme.oracleUnif
        (State P AuthState) (State P AuthState) P.EpochKey
        (Message P.Sym)) (fun s => ControlInv s ∧ StatePairInv s) := by
    intro n s hs z hz
    have hz' : ∃ y : unifSpec.Range n, (y, s) = z := by
      simpa [SCKAScheme.oracleUnif] using hz
    rcases hz' with ⟨_, rfl⟩
    exact hs
  have hSendA : QueryImpl.PreservesInv
      (SCKAScheme.oracleSendA (scheme P auth irl sampleInitKey))
      (fun s => ControlInv s ∧ StatePairInv s) := by
    intro t s hs z hz
    cases t
    refine ⟨oracleSendA_preserves_controlInv P auth irl sampleInitKey () s hs.1 z hz, ?_⟩
    rw [SCKAScheme.oracleSendA, StateT.run_bind, StateT.run_get] at hz
    simp only [scheme, bind_pure_comp, liftM_map, bind_map_left,
      StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind,
      support_bind, Set.mem_iUnion, exists_prop] at hz
    obtain ⟨r, hr, hz⟩ := hz
    have hpair := send_preserves_statePairInv P auth s hs.2 true r hr
    simp only [if_true] at hpair
    cases hkey : r.outputKey with
    | none =>
        simp only [hkey, StateT.run_map, StateT.run_set, map_pure,
          support_pure, Set.mem_singleton_iff] at hz
        subst z
        exact hpair
    | some keyPair =>
        rcases keyPair with ⟨tI, key⟩
        simp only [hkey, StateT.run_map, StateT.run_set, map_pure,
          support_pure, Set.mem_singleton_iff] at hz
        subst z
        exact hpair
  have hSendB : QueryImpl.PreservesInv
      (SCKAScheme.oracleSendB (scheme P auth irl sampleInitKey))
      (fun s => ControlInv s ∧ StatePairInv s) := by
    intro t s hs z hz
    cases t
    refine ⟨oracleSendB_preserves_controlInv P auth irl sampleInitKey () s hs.1 z hz, ?_⟩
    rw [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get] at hz
    simp only [scheme, bind_pure_comp, liftM_map, bind_map_left,
      StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind,
      support_bind, Set.mem_iUnion, exists_prop] at hz
    obtain ⟨r, hr, hz⟩ := hz
    have hpair := send_preserves_statePairInv P auth s hs.2 false r hr
    simp only [Bool.false_eq_true, ↓reduceIte] at hpair
    cases hkey : r.outputKey with
    | none =>
        simp only [hkey, StateT.run_map, StateT.run_set, map_pure,
          support_pure, Set.mem_singleton_iff] at hz
        subst z
        exact hpair
    | some keyPair =>
        rcases keyPair with ⟨tI, key⟩
        simp only [hkey, StateT.run_map, StateT.run_set, map_pure,
          support_pure, Set.mem_singleton_iff] at hz
        subst z
        exact hpair
  have hRecvA : QueryImpl.PreservesInv
      (SCKAScheme.oracleRecvA (scheme P auth irl sampleInitKey))
      (fun s => ControlInv s ∧ StatePairInv s) := by
    intro n s hs z hz
    refine ⟨oracleRecvA_preserves_controlInv P auth irl sampleInitKey n s hs.1 z hz, ?_⟩
    rcases hentry : s.msgB n with _ | ⟨msg, tsnd⟩
    · simp only [SCKAScheme.oracleRecvA, bind_pure_comp,
        StateT.run_bind, StateT.run_get, pure_bind, hentry,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst z
      exact hs.2
    rcases hrecv : recvSCKA P auth s.stA msg with _ | ⟨keyOpt, treport, stA'⟩
    · simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp,
        StateT.run_bind, StateT.run_get, pure_bind, hentry, hrecv,
        StateT.run_map, StateT.run_set, map_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst z
      exact hs.2
    obtain ⟨r, hraw, -, hstate, -⟩ :
        ∃ r, receive P auth s.stA msg = .ok r ∧
          r.outputKey = keyOpt ∧ r.state = stA' ∧
          treport = msg.epoch - 1 := by
      cases hreceive : receive P auth s.stA msg with
      | error err => simp [recvSCKA, hreceive] at hrecv
      | ok r =>
          have hparts :
              r.outputKey = keyOpt ∧ msg.epoch - 1 = treport ∧
                r.state = stA' := by
            simpa [recvSCKA, hreceive] using hrecv
          exact ⟨r, rfl, hparts.1, hparts.2.2, hparts.2.1.symm⟩
    subst stA'
    have hpair : StatePairInv { s with stA := r.state } := by
      cases hrole : s.stA.controlPosition.1
      · exact receive_encapsulator_preserves_statePairInv P auth s hs true
          n msg tsnd hentry hrole r hraw
      · exact receive_generator_preserves_statePairInv P auth s hs true
          n msg tsnd hentry hrole r hraw
    rcases hkey : keyOpt with _ | ⟨tI, key⟩
    · simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp,
        StateT.run_bind, StateT.run_get, pure_bind, hentry, hrecv, hkey,
        StateT.run_map, StateT.run_set, map_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst z
      exact hpair
    · simp only [SCKAScheme.oracleRecvA, scheme, bind_pure_comp,
        StateT.run_bind, StateT.run_get, pure_bind, hentry, hrecv, hkey,
        StateT.run_map, StateT.run_set, map_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst z
      exact hpair
  have hRecvB : QueryImpl.PreservesInv
      (SCKAScheme.oracleRecvB (scheme P auth irl sampleInitKey))
      (fun s => ControlInv s ∧ StatePairInv s) := by
    intro n s hs z hz
    refine ⟨oracleRecvB_preserves_controlInv P auth irl sampleInitKey n s hs.1 z hz, ?_⟩
    rcases hentry : s.msgA n with _ | ⟨msg, tsnd⟩
    · simp only [SCKAScheme.oracleRecvB, bind_pure_comp,
        StateT.run_bind, StateT.run_get, pure_bind, hentry,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst z
      exact hs.2
    rcases hrecv : recvSCKA P auth s.stB msg with _ | ⟨keyOpt, treport, stB'⟩
    · simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp,
        StateT.run_bind, StateT.run_get, pure_bind, hentry, hrecv,
        StateT.run_map, StateT.run_set, map_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst z
      exact hs.2
    obtain ⟨r, hraw, -, hstate, -⟩ :
        ∃ r, receive P auth s.stB msg = .ok r ∧
          r.outputKey = keyOpt ∧ r.state = stB' ∧
          treport = msg.epoch - 1 := by
      cases hreceive : receive P auth s.stB msg with
      | error err => simp [recvSCKA, hreceive] at hrecv
      | ok r =>
          have hparts :
              r.outputKey = keyOpt ∧ msg.epoch - 1 = treport ∧
                r.state = stB' := by
            simpa [recvSCKA, hreceive] using hrecv
          exact ⟨r, rfl, hparts.1, hparts.2.2, hparts.2.1.symm⟩
    subst stB'
    have hpair : StatePairInv { s with stB := r.state } := by
      cases hrole : s.stB.controlPosition.1
      · exact receive_encapsulator_preserves_statePairInv P auth s hs false
          n msg tsnd hentry hrole r hraw
      · exact receive_generator_preserves_statePairInv P auth s hs false
          n msg tsnd hentry hrole r hraw
    rcases hkey : keyOpt with _ | ⟨tI, key⟩
    · simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp,
        StateT.run_bind, StateT.run_get, pure_bind, hentry, hrecv, hkey,
        StateT.run_map, StateT.run_set, map_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst z
      exact hpair
    · simp only [SCKAScheme.oracleRecvB, scheme, bind_pure_comp,
        StateT.run_bind, StateT.run_get, pure_bind, hentry, hrecv, hkey,
        StateT.run_map, StateT.run_set, map_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst z
      exact hpair
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

end MLKEMBraid
