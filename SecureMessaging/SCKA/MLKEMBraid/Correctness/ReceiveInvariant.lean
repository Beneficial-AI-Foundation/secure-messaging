/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.MLKEMBraid.Correctness.RecordedPayload

/-!
# Receives preserve the correctness invariant

A receive edge of a party on a message recorded by its peer keeps `TranscriptInv D` for the same
transcript, for every condition `D`, when the receiver's epoch reaches the message epoch, its new
state agrees with the transcript, and every output key is the peer's recorded key and the
transcript key of a recorded encapsulation satisfying `D` (`transcriptInv_recvUpdate`). A Braid
receive whose output key agrees with the peer's recorded key meets these conditions; a refusal or
a key disagreement clears the correctness flag. Thus the receive oracles preserve
`CorrectnessInv`.
-/

@[expose] public section

open OracleSpec OracleComp
open ErasureCodePayload.Streaming
open SCKAScheme.sckaCorrectnessSpec

namespace Braid

variable {P : Parameters ProbComp} {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
  {D : ℕ → P.PK → P.SK → P.inc.St → P.inc.C₁ → P.K → Prop}

/-- A receive edge from the state of `party` keeps `TranscriptInv D` for the same transcript in
the successor `recvSuccessor s party r trcv`, provided that the receiver's new state agrees with
the transcript, that every output key is the transcript key of a recorded encapsulation satisfying
`D`, and that the successor satisfies the control and pair invariants. -/
private theorem transcriptInv_recvSuccessor {ik : InitKey} {T : ℕ → EpochTranscript P}
    {s : GameState P AuthState} (hT : TranscriptInv auth D ik T s) (party : Bool)
    {msg : Message P.Sym} {r : RecvResult P AuthState}
    (hedge : ReceiveEdge auth (s.stateAt party) msg r)
    (hLocalNew : LocalPayloadInv auth ik T r.state)
    (hkeyFact : ∀ t key, r.outputKey = some (t, key) → ∃ es ct1 k,
      (T t).encaps1 = some (es, ct1, k) ∧ key = P.kdfOK k t ∧
      ∀ pk sk, (T t).keypair = some (pk, sk) → D t pk sk es ct1 k)
    (trcv : ℕ) :
    let s' := recvSuccessor s party r trcv
    (ControlInv s' ∧ StatePairInv s') → TranscriptInv auth D ik T s' := by
  dsimp only
  -- The receiver keeps its local payload invariant, never lowers its epoch or completed
  -- epoch, and outputs only the transcript key of its next completed epoch.
  have hmono : (s.stateAt party).epoch ≤ r.state.epoch := hedge.epoch_le.1
  have hpos := hT.control.epochKnowledge.keyPrefix.pos party
  have hcompMono := hedge.completedEpoch_mono hpos
  have hstep := (hedge.completedEpoch hpos).2
  have hcomp : (r.outputKey = none ∧
        r.state.completedEpoch = (s.stateAt party).completedEpoch) ∨
      ∃ t key, r.outputKey = some (t, key) ∧
        t = (s.stateAt party).completedEpoch + 1 ∧
        r.state.completedEpoch = t := by
    cases hkey : r.outputKey with
    | none =>
        simp only [hkey] at hstep
        exact Or.inl ⟨rfl, hstep⟩
    | some out =>
        rcases out with ⟨t, key⟩
        simp only [hkey] at hstep
        exact Or.inr ⟨t, key, rfl, hstep⟩
  let s' := recvSuccessor s party r trcv
  have hmonos (who : Bool) : (s.stateAt who).epoch ≤ (s'.stateAt who).epoch ∧
      (s.stateAt who).completedEpoch ≤ (s'.stateAt who).completedEpoch := by
    dsimp only [s']
    simp only [stateAt_recvSuccessor]
    by_cases hwho : who = party
    · subst who; simpa only [↓reduceIte] using And.intro hmono hcompMono
    · simp only [ite_eq_right hwho]; exact ⟨le_rfl, le_rfl⟩
  have hLocal (who : Bool) : LocalPayloadInv auth ik T (s'.stateAt who) := by
    dsimp only [s']
    rw [stateAt_recvSuccessor]
    split_ifs with hwho
    · exact hLocalNew
    · exact hT.local auth who
  have hKeys (who : Bool) (e : ℕ) :
      s'.keysAt who e = if 0 < e ∧ e ≤ (s'.stateAt who).completedEpoch then
        (T e).encaps1.map (fun (_, _, key) => P.kdfOK key e) else none := by
    have hK : s.keysAt who e = if 0 < e ∧ e ≤ (s.stateAt who).completedEpoch then
        (T e).encaps1.map (fun (_, _, key) => P.kdfOK key e) else none := hT.keys who e
    dsimp only [s']
    rw [keysAt_recvSuccessor, stateAt_recvSuccessor]
    by_cases hwho : who = party
    · subst who
      simp only [↓reduceIte]
      rcases hcomp with ⟨hnone, hceq⟩ | ⟨t, key, hkey, ht, hceq⟩
      · rw [hnone, hceq]
        exact hK
      · simp only [hkey, hceq]
        by_cases het : e = t
        · subst het
          obtain ⟨es', ct1', k', hc', hk', -⟩ := hkeyFact e key hkey
          rw [Function.update_self, ite_eq_left ⟨by omega, le_refl e⟩, hc']
          exact congrArg some hk'
        · rw [Function.update_of_ne het, hK]
          by_cases h1 : 0 < e ∧ e ≤ (s.stateAt party).completedEpoch
          · rw [ite_eq_left h1, ite_eq_left (by omega)]
          · rw [ite_eq_right h1, ite_eq_right (by omega)]
    · simpa only [ite_eq_right hwho] using hK
  rintro ⟨hC', hP'⟩
  refine ⟨by simpa only [correct_recvSuccessor] using hT.correct, hC', hP',
    hT.keypair_zero, hT.encaps_zero, ?_, ?_, hLocal true, hLocal false, ?_, hKeys⟩
  · intro e pk sk hk
    obtain ⟨h0, hle⟩ := hT.keypair e pk sk hk
    refine ⟨h0, ?_⟩
    rw [← GameState.stateAt_generator] at hle ⊢
    exact hle.trans (hmonos _).1
  · intro e encapsState ct1 key hc
    obtain ⟨h0, hle, pk, sk, hkp, hdec⟩ := hT.encaps e encapsState ct1 key hc
    refine ⟨h0, ?_, pk, sk, hkp, fun hle' => ?_⟩
    · rw [← GameState.stateAt_encapsulator] at hle ⊢
      exact hle.trans (hmonos _).2
    · rw [← GameState.stateAt_generator] at hdec hle'
      rw [stateAt_recvSuccessor] at hle'
      by_cases howner : decide (e % 2 = 1) = party
      · rw [ite_eq_left howner] at hle'
        rw [howner] at hdec
        rcases hcomp with ⟨-, hceq⟩ | ⟨t, k', hkey, ht, hceq⟩
        · exact hdec (hceq ▸ hle')
        · by_cases het : e = t
          · subst het
            obtain ⟨es', ct1', k'', hc', -, hD⟩ := hkeyFact e k' hkey
            rw [hc] at hc'
            cases hc'
            exact hD pk sk hkp
          · exact hdec (by omega)
      · rw [ite_eq_right howner] at hle'
        exact hdec hle'
  · intro who n' msg' tsnd' hmsg'
    apply hT.messages who n' msg' tsnd'
    exact (congrFun (messagesAt_recvSuccessor s party who r trcv) n').symm.trans hmsg'

variable [DecidableEq P.EpochKey]

/-- Under `ControlInv` with a true flag, a receive edge on a message recorded by the peer whose
output keys are the peer's recorded keys keeps the flag true. -/
private theorem recvUpdate_correct_of_peer_key {s : GameState P AuthState}
    (hC : ControlInv s) (hc : s.correct = true) (party : Bool)
    {n : ℕ} {msg : Message P.Sym} {tsnd : ℕ} {r : RecvResult P AuthState}
    (hentry : s.messagesAt (!party) n = some (msg, tsnd))
    (hedge : ReceiveEdge auth (s.stateAt party) msg r)
    (hkey : ∀ e key, r.outputKey = some (e, key) → s.keysAt (!party) e = some key) :
    (recvUpdate s party tsnd r (msg.epoch - 1)).correct = true := by
  have hrep := hC.recordedReport.report (!party) n msg tsnd hentry
  have hbound := (hC.epochKnowledge.msgs (!party) n msg tsnd hentry).2.1
  simp only [Bool.not_not] at hbound
  have htcur := hC.epochKnowledge.tcur_le party
  have hprefix := hC.epochKnowledge.keyPrefix.keys party
  have hmax : max (s.tcurAt party) (msg.epoch - 1) ≤ (s.stateAt party).completedEpoch := by omega
  have hknown := SCKAScheme.knownPrefix_eq_true
    fun t h0 hle => (hprefix t).2 ⟨h0, hle.trans hmax⟩
  rw [recvUpdate_correct]
  rcases hk : r.outputKey with _ | ⟨tI, key⟩
  · simp only [Bool.and_eq_true]
    exact ⟨⟨hc, by simp [hrep]⟩, hknown⟩
  · have hpos := hC.epochKnowledge.keyPrefix.pos party
    have hstep := (hedge.completedEpoch hpos).2
    simp only [hk] at hstep
    obtain ⟨htI, -⟩ := hstep
    have hnone : s.keysAt party tI = none := by
      by_contra hne
      have := ((hprefix tI).1 hne).2
      omega
    have hpeer := hkey tI key hk
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨hc, by simp [hrep]⟩, by simp [hnone]⟩, by simp [hpeer]⟩,
      SCKAScheme.knownPrefix_update_some hknown tI key⟩

/-- A receive edge of `party` on the message recorded by its peer at index `n` keeps
`TranscriptInv D` for the same transcript, provided that the receiver's epoch reaches the message
epoch, its new state agrees with the transcript, and every output key is the peer's recorded key
and the transcript key of a recorded encapsulation satisfying `D`. -/
theorem transcriptInv_recvUpdate {ik : InitKey} {T : ℕ → EpochTranscript P}
    {s : GameState P AuthState} (hT : TranscriptInv auth D ik T s) (party : Bool)
    {n : ℕ} {msg : Message P.Sym} {tsnd : ℕ} {r : RecvResult P AuthState}
    (hentry : s.messagesAt (!party) n = some (msg, tsnd))
    (hedge : ReceiveEdge auth (s.stateAt party) msg r)
    (hmsgEpoch : msg.epoch ≤ r.state.epoch)
    (hLocalNew : LocalPayloadInv auth ik T r.state)
    (hkeys : ∀ t key, r.outputKey = some (t, key) → s.keysAt (!party) t = some key ∧
      ∃ es ct1 k, (T t).encaps1 = some (es, ct1, k) ∧ key = P.kdfOK k t ∧
      ∀ pk sk, (T t).keypair = some (pk, sk) → D t pk sk es ct1 k) :
    TranscriptInv auth D ik T (recvUpdate s party tsnd r (msg.epoch - 1)) := by
  have hCP := controlInv_statePairInv_recvUpdate auth ⟨hT.control, hT.statePair⟩ party hentry
    hedge hmsgEpoch
  have hc := recvUpdate_correct_of_peer_key auth hT.control hT.correct party hentry hedge
    (fun t key h => (hkeys t key h).1)
  rw [recvUpdate_eq_successor_of_correct s party tsnd r (msg.epoch - 1) hT.correct hc] at hCP ⊢
  exact transcriptInv_recvSuccessor auth hT party hedge hLocalNew
    (fun t key h => (hkeys t key h).2) (msg.epoch - 1) hCP

variable (irl : P.kem.IncrementalRandLeak P.inc) (sampleInitKey : ProbComp InitKey)

/-- A receive whose successor has a true correctness flag keeps the game state consistent with the
same transcript. -/
theorem oracleRecv_preserves_transcriptConsistent
    (hHdrSound : P.decHdr.Sound P.ecpHdr)
    (hEkSound : P.decEk.Sound P.ecpEk)
    (hCt1Sound : P.decCt1.Sound P.ecpCt1)
    (hCt2Sound : P.decCt2.Sound P.ecpCt2)
    {ik : InitKey} {T : ℕ → EpochTranscript P} {s : GameState P AuthState}
    (hT : TranscriptConsistent auth ik T s) (party : Bool) (n : ℕ)
    (z : Option (ℕ × Option ℕ) × GameState P AuthState)
    (hz : z ∈ support
      ((oracleRecv auth irl sampleInitKey party n).run s))
    (hzc : z.2.correct = true) :
    TranscriptConsistent auth ik T z.2 := by
  have hCPz : ControlInv z.2 ∧ StatePairInv z.2 := by
    cases party
    · exact correctnessImpl_preserves_controlInv_statePairInv auth irl sampleInitKey
        (ORecvB (Rho := Message P.Sym) n) s ⟨hT.control, hT.statePair⟩ z hz
    · exact correctnessImpl_preserves_controlInv_statePairInv auth irl sampleInitKey
        (ORecvA (Rho := Message P.Sym) n) s ⟨hT.control, hT.statePair⟩ z hz
  rcases oracleRecv_run_cases auth irl sampleInitKey party hz with
    ⟨-, rfl⟩ | ⟨msg, tsnd, err, -, -, rfl⟩ | ⟨msg, tsnd, r, hentry, hraw, rfl⟩
  · exact hT
  · cases hzc
  have hagree : ∀ e key, r.outputKey = some (e, key) → s.keysAt (!party) e = some key := by
    intro e key hkey
    obtain ⟨-, -, _, _, _, _, _, -, -, -, hpeer⟩ :=
      receive_recorded_output auth hCt2Sound hT party n msg tsnd hentry r hraw e key hkey
    rw [recvUpdate_correct, hkey] at hzc
    simp only [Bool.and_eq_true, Bool.or_eq_true] at hzc
    obtain ⟨⟨-, hcons⟩, -⟩ := hzc
    rcases hcons with hnone | hbeq
    · simp [hpeer] at hnone
    · exact beq_iff_eq.mp hbeq
  have hLocalNew : LocalPayloadInv auth ik T r.state :=
    (receive_recorded_payload auth hHdrSound hEkSound hCt1Sound hCt2Sound hT
      party n msg tsnd hentry).1 r hraw hagree
  have hkeyFact : ∀ t key, r.outputKey = some (t, key) → ∃ es ct1 k,
      (T t).encaps1 = some (es, ct1, k) ∧ key = P.kdfOK k t ∧
      ∀ pk sk, (T t).keypair = some (pk, sk) →
        decapsEpochKey t pk sk es ct1 = some (P.kdfOK k t) := by
    intro t key hout
    obtain ⟨-, -, pk, sk, encapsState, ct1, k, hkp, hc, hdec, hpeer⟩ :=
      receive_recorded_output auth hCt2Sound hT party n msg tsnd hentry r hraw t key hout
    have hkey : key = P.kdfOK k t := Option.some.inj ((hagree t key hout).symm.trans hpeer)
    subst hkey
    refine ⟨encapsState, ct1, k, hc, rfl, fun pk' sk' hkp' => ?_⟩
    rw [hkp] at hkp'
    cases hkp'
    exact hdec
  rw [recvUpdate_eq_successor_of_correct s party tsnd r (msg.epoch - 1) hT.correct hzc] at hCPz ⊢
  exact transcriptInv_recvSuccessor auth hT party (ReceiveEdge.of_eq_ok auth hraw) hLocalNew
    hkeyFact (msg.epoch - 1) hCPz

/-- With sound stream decoders, either party's receive preserves `CorrectnessInv`. -/
theorem oracleRecv_preserves_correctnessInv
    (hHdrSound : P.decHdr.Sound P.ecpHdr)
    (hEkSound : P.decEk.Sound P.ecpEk)
    (hCt1Sound : P.decCt1.Sound P.ecpCt1)
    (hCt2Sound : P.decCt2.Sound P.ecpCt2)
    (ik : InitKey) (party : Bool) :
    QueryImpl.PreservesInv
      (oracleRecv auth irl sampleInitKey party)
      (CorrectnessInv auth ik) := by
  intro n s hs z hz
  cases hzc : z.2.correct
  · exact Or.inl hzc
  rcases hs with hsf | ⟨T, hT⟩
  · rcases oracleRecv_run_cases auth irl sampleInitKey party hz with
      ⟨-, rfl⟩ | ⟨msg, tsnd, err, -, -, rfl⟩ | ⟨msg, tsnd, r, -, -, rfl⟩
    · simp [hsf] at hzc
    · cases hzc
    · rw [recvUpdate_correct] at hzc
      rcases hkey : r.outputKey with _ | ⟨e, key⟩ <;> simp [hkey, hsf] at hzc
  · exact Or.inr ⟨T, oracleRecv_preserves_transcriptConsistent auth irl sampleInitKey
      hHdrSound hEkSound hCt1Sound hCt2Sound hT party n z hz hzc⟩

end Braid
