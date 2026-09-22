import SecureMessaging.SCKA.MLKEMBraid.Correctness.EpochSafety.Preservation

open OracleSpec OracleComp
open ErasureCodePayload.Streaming
open SCKAScheme.sckaCorrectnessSpec

namespace MLKEMBraid

structure EpochTranscript (P : Parameters ProbComp) where
  keypair : Option (P.PK × P.SK)
  encaps1 : Option (P.inc.St × P.inc.C₁ × P.K)

def transcriptAuth
    (P : Parameters ProbComp)
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (ik : InitKey) (T : ℕ → EpochTranscript P) : ℕ → AuthState
  | 0 => auth.init ik 1
  | e + 1 =>
      match (T (e + 1)).encaps1 with
      | none => transcriptAuth P auth ik T e
      | some c => auth.update (transcriptAuth P auth ik T e)
          (e + 1) (P.kdfOK c.2.2 (e + 1))

def LocalPayloadInv
    (P : Parameters ProbComp)
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (ik : InitKey) (T : ℕ → EpochTranscript P)
    (st : State P AuthState) : Prop :=
  let encOK := fun {M : Type} (ecp : ErasureCodePayload M P.Sym)
      (payload : M) (enc : EncoderState M P.Sym) =>
      enc.ecp = ecp ∧ enc.payload = payload
  let decOK := fun {M : Type} (ecp : ErasureCodePayload M P.Sym)
      (payload : M) (dec : DecoderState M P.Sym) =>
      dec.ecp = ecp ∧ ∃ I : Finset (Fin ecp.ec.N),
        dec.chunks = ErasureCodePayload.payloadChunks ecp payload I
  match st with
  | .keysUnsampled e a =>
      a = transcriptAuth P auth ik T (e - 1) ∧
        (T e).keypair = none ∧ (T e).encaps1 = none
  | .keysSampled e a sk vec enc =>
      a = transcriptAuth P auth ik T (e - 1) ∧
        ∃ pk, (T e).keypair = some (pk, sk) ∧
          vec = P.inc.toVector pk ∧
          encOK P.ecpHdr
            (P.inc.toHeader pk,
              auth.macHeader (transcriptAuth P auth ik T (e - 1))
                e (P.inc.toHeader pk)) enc
  | .headerSent e a sk dec enc =>
      a = transcriptAuth P auth ik T (e - 1) ∧
        ∃ pk c, (T e).keypair = some (pk, sk) ∧
          (T e).encaps1 = some c ∧
          decOK P.ecpCt1 c.2.1 dec ∧ encOK P.ecpEk (P.inc.toVector pk) enc
  | .ct1Received e a sk ct1 enc =>
      a = transcriptAuth P auth ik T (e - 1) ∧
        ∃ pk c, (T e).keypair = some (pk, sk) ∧
          (T e).encaps1 = some c ∧ ct1 = c.2.1 ∧
          encOK P.ecpEk (P.inc.toVector pk) enc
  | .ekSentCt1Received e a sk ct1 dec =>
      a = transcriptAuth P auth ik T (e - 1) ∧
        ∃ pk c, (T e).keypair = some (pk, sk) ∧
          (T e).encaps1 = some c ∧ ct1 = c.2.1 ∧
          let ct2 := P.hEnc2.encaps2Det c.1
            (P.inc.toHeader pk) (P.inc.toVector pk)
          decOK P.ecpCt2
            (ct2, auth.macCiphertext (transcriptAuth P auth ik T e)
              e (c.2.1, ct2)) dec
  | .noHeaderReceived e a dec =>
      a = transcriptAuth P auth ik T (e - 1) ∧
        match (T e).keypair with
        | none => dec = DecoderState.empty P.ecpHdr
        | some kp => decOK P.ecpHdr
            (P.inc.toHeader kp.1,
              auth.macHeader (transcriptAuth P auth ik T (e - 1))
                e (P.inc.toHeader kp.1)) dec
  | .headerReceived e a hdr dec =>
      a = transcriptAuth P auth ik T (e - 1) ∧
        (T e).encaps1 = none ∧
        ∃ kp, (T e).keypair = some kp ∧
          hdr = P.inc.toHeader kp.1 ∧ dec = DecoderState.empty P.ecpEk
  | .ct1Sampled e a hdr encapsState ct1 enc dec =>
      a = transcriptAuth P auth ik T e ∧
        ∃ kp key, (T e).keypair = some kp ∧
          (T e).encaps1 = some (encapsState, ct1, key) ∧
          hdr = P.inc.toHeader kp.1 ∧
          encOK P.ecpCt1 ct1 enc ∧ decOK P.ecpEk (P.inc.toVector kp.1) dec
  | .ekReceivedCt1Sampled e a encapsState ct1 hdr vec enc =>
      a = transcriptAuth P auth ik T e ∧
        ∃ kp key, (T e).keypair = some kp ∧
          (T e).encaps1 = some (encapsState, ct1, key) ∧
          hdr = P.inc.toHeader kp.1 ∧
          vec = P.inc.toVector kp.1 ∧ encOK P.ecpCt1 ct1 enc
  | .ct1Acknowledged e a hdr encapsState ct1 dec =>
      a = transcriptAuth P auth ik T e ∧
        ∃ kp key, (T e).keypair = some kp ∧
          (T e).encaps1 = some (encapsState, ct1, key) ∧
          hdr = P.inc.toHeader kp.1 ∧ decOK P.ecpEk (P.inc.toVector kp.1) dec
  | .ct2Sampled e a enc =>
      a = transcriptAuth P auth ik T e ∧
        ∃ kp c, (T e).keypair = some kp ∧ (T e).encaps1 = some c ∧
          let ct2 := P.hEnc2.encaps2Det c.1
            (P.inc.toHeader kp.1) (P.inc.toVector kp.1)
          encOK P.ecpCt2
            (ct2, auth.macCiphertext (transcriptAuth P auth ik T e)
              e (c.2.1, ct2)) enc

def MessagePayloadInv
    (P : Parameters ProbComp)
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (ik : InitKey) (T : ℕ → EpochTranscript P)
    (msg : Message P.Sym) : Prop :=
  match msg.type with
  | .none => msg.data = none
  | .hdr =>
      ∃ kp i, (T msg.epoch).keypair = some kp ∧
        msg.data = some (P.ecpHdr.encode
          (P.inc.toHeader kp.1,
            auth.macHeader (transcriptAuth P auth ik T (msg.epoch - 1))
              msg.epoch (P.inc.toHeader kp.1)) i)
  | .ek | .ekCt1Ack =>
      ∃ kp i, (T msg.epoch).keypair = some kp ∧
        msg.data = some (P.ecpEk.encode (P.inc.toVector kp.1) i)
  | .ct1 =>
      ∃ c i, (T msg.epoch).encaps1 = some c ∧
        msg.data = some (P.ecpCt1.encode c.2.1 i)
  | .ct2 =>
      ∃ kp c i, (T msg.epoch).keypair = some kp ∧
        (T msg.epoch).encaps1 = some c ∧
        let ct2 := P.hEnc2.encaps2Det c.1
          (P.inc.toHeader kp.1) (P.inc.toVector kp.1)
        msg.data = some (P.ecpCt2.encode
          (ct2, auth.macCiphertext (transcriptAuth P auth ik T msg.epoch)
            msg.epoch (c.2.1, ct2)) i)
  | .ct1Ack => False

def TranscriptConsistent
    (P : Parameters ProbComp)
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (ik : InitKey) (T : ℕ → EpochTranscript P)
    (s : SCKAScheme.GameState
      (State P AuthState) (State P AuthState)
      P.EpochKey (Message P.Sym)) : Prop :=
  s.correct = true ∧ ControlInv s ∧ StatePairInv s ∧
    (T 0).keypair = none ∧ (T 0).encaps1 = none ∧
    (∀ e pk sk, (T e).keypair = some (pk, sk) →
      0 < e ∧
        e ≤ (if e % 2 = 1 then s.stA else s.stB).epoch ∧
        (pk, sk) ∈ support P.kem.keygen) ∧
    (∀ e encapsState ct1 key,
      (T e).encaps1 = some (encapsState, ct1, key) →
      0 < e ∧
        e ≤ (if e % 2 = 1 then s.stB else s.stA).completedEpoch ∧
        ∃ pk sk, (T e).keypair = some (pk, sk) ∧
          (encapsState, ct1, key) ∈
            support (P.inc.encaps1 (P.inc.toHeader pk)) ∧
          (e ≤ (if e % 2 = 1 then s.stA else s.stB).completedEpoch →
            (P.hDet.decapsDet sk
              (P.inc.splitC.symm (ct1,
                P.hEnc2.encaps2Det encapsState
                  (P.inc.toHeader pk) (P.inc.toVector pk)))).map
                (fun k => P.kdfOK k e) = some (P.kdfOK key e))) ∧
    LocalPayloadInv P auth ik T s.stA ∧
    LocalPayloadInv P auth ik T s.stB ∧
    (∀ (party : Bool) n msg tsnd,
      (if party then s.msgA else s.msgB) n = some (msg, tsnd) →
        MessagePayloadInv P auth ik T msg) ∧
    (∀ (party : Bool) e,
      (if party then s.keyA else s.keyB) e =
        if 0 < e ∧ e ≤ (if party then s.stA else s.stB).completedEpoch then
          (T e).encaps1.map (fun c => P.kdfOK c.2.2 e)
        else none)

def CorrectnessInv
    (P : Parameters ProbComp)
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (ik : InitKey)
    (s : SCKAScheme.GameState
      (State P AuthState) (State P AuthState)
      P.EpochKey (Message P.Sym)) : Prop :=
  s.correct = false ∨
    ∃ T : ℕ → EpochTranscript P, TranscriptConsistent P auth ik T s

theorem transcriptConsistent_init
    (P : Parameters ProbComp)
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (ik : InitKey) :
    TranscriptConsistent P auth ik
      (fun _ => { keypair := none, encaps1 := none })
      (SCKAScheme.initGameState (initA P auth ik) (initB P auth ik)) := by
  have hControl : ControlInv
      (SCKAScheme.initGameState (I := P.EpochKey) (Rho := Message P.Sym)
        (initA P auth ik) (initB P auth ik)) := by
    refine ⟨epochKnowledgeInv_initGameState P auth ik,
      recordedReportInv_initGameState (initA P auth ik) (initB P auth ik),
      ?_, ?_, ?_⟩
    · simp [SCKAScheme.initGameState, initA, State.epoch]
    · simp [SCKAScheme.initGameState, initB, State.epoch]
    · intro party
      cases party <;>
        simp [SCKAScheme.initGameState, initA, initB,
          State.controlPosition, State.epoch]
  simp only [TranscriptConsistent]
  refine ⟨rfl, hControl, ?_, True.intro, True.intro, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro party
    cases party <;>
      simp [SCKAScheme.initGameState, initA, initB,
        State.controlPosition, State.epoch]
  · simp
  · simp
  · simp [LocalPayloadInv, SCKAScheme.initGameState, initA,
      transcriptAuth]
  · simp [LocalPayloadInv, SCKAScheme.initGameState, initB,
      transcriptAuth]
  · simp [SCKAScheme.initGameState]
  · intro party e
    cases party <;>
      simp [SCKAScheme.initGameState, initA, initB,
        State.completedEpoch, State.epoch]

theorem transcript_send_lifecycle
    (P : Parameters ProbComp)
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (ik : InitKey) (T : ℕ → EpochTranscript P)
    (s : SCKAScheme.GameState
      (State P AuthState) (State P AuthState)
      P.EpochKey (Message P.Sym))
    (hT : TranscriptConsistent P auth ik T s) :
    (∀ (party : Bool) e a,
      (if party then s.stA else s.stB) = .keysUnsampled e a →
        ∃ b dec,
          (if party then s.stB else s.stA) = .noHeaderReceived e b dec) ∧
    (∀ (party : Bool) e a hdr dec,
      (if party then s.stA else s.stB) = .headerReceived e a hdr dec →
        ∃ pk sk b enc,
          (T e).keypair = some (pk, sk) ∧
          (if party then s.stB else s.stA) =
            .keysSampled e b sk (P.inc.toVector pk) enc ∧
          hdr = P.inc.toHeader pk) := by
  rcases hT with
    ⟨_, hControl, hPair, _, _, _, _, hLocalA, hLocalB, _, _⟩
  have hEpoch := hControl.1
  simp only [EpochKnowledgeInv] at hEpoch
  have hPrefix := hEpoch.1
  simp only [KeyPrefixInv] at hPrefix
  have hPosA := hPrefix.1
  have hPosB := hPrefix.2.1
  have hCrossA := hEpoch.2.1
  have hCrossB := hEpoch.2.2.1
  have hCompletedA : s.stA.completedEpoch ≤ s.stA.epoch := by
    cases s.stA <;> simp [State.completedEpoch, State.epoch]
  have hCompletedB : s.stB.completedEpoch ≤ s.stB.epoch := by
    cases s.stB <;> simp [State.completedEpoch, State.epoch]
  have hPairA := hPair true
  have hPairB := hPair false
  have hRoleA := (hControl.2.2.2.2 true).1
  have hRoleB := (hControl.2.2.2.2 false).1
  simp only [if_true] at hPairA hRoleA
  simp only [Bool.false_eq_true, ↓reduceIte] at hPairB hRoleB
  constructor
  · intro party e a hst
    cases party
    · change s.stB = .keysUnsampled e a at hst
      change ∃ b dec, s.stA = .noHeaderReceived e b dec
      have hUpper : s.stA.epoch ≤ e := by
        have h := hCrossA
        rw [hst] at h
        simp only [State.completedEpoch, State.epoch] at h
        have he : 0 < e := by
          simpa [hst, State.epoch] using hPosB
        have heq : e - 1 + 1 = e := by omega
        simpa only [State.epoch, heq] using h
      have hLower : e ≤ s.stA.epoch + 1 := by
        have h := hCrossB
        rw [hst] at h
        simp only [State.epoch] at h
        omega
      have hNotLag : ¬ e = s.stA.epoch + 1 := by
        intro hLag
        have hLag' : s.stB.epoch = s.stA.epoch + 1 := by
          rw [hst]
          exact hLag
        rcases hPairA.2 hLag' with ⟨a', enc, b, dec, _, hPeer⟩
        rw [hst] at hPeer
        cases hPeer
      have hEqual : s.stA.epoch = e := by omega
      have hSame : s.stB.epoch = s.stA.epoch := by
        rw [hst]
        exact hEqual.symm
      have hGenerator : s.stB.controlPosition.1 = true := by
        rw [hst]
        rfl
      have hAllowed := hPairB.1 hSame hGenerator
      cases ha : s.stA
      case noHeaderReceived e' b dec =>
        have he' : e' = e := by
          simpa [ha, State.epoch] using hEqual
        subst e'
        exact ⟨b, dec, rfl⟩
      all_goals simp [hst, ha] at hAllowed
    · change s.stA = .keysUnsampled e a at hst
      change ∃ b dec, s.stB = .noHeaderReceived e b dec
      have hUpper : s.stB.epoch ≤ e := by
        have h := hCrossB
        rw [hst] at h
        simp only [State.completedEpoch, State.epoch] at h
        have he : 0 < e := by
          simpa [hst, State.epoch] using hPosA
        have heq : e - 1 + 1 = e := by omega
        simpa only [State.epoch, heq] using h
      have hLower : e ≤ s.stB.epoch + 1 := by
        have h := hCrossA
        rw [hst] at h
        simp only [State.epoch] at h
        omega
      have hNotLag : ¬ e = s.stB.epoch + 1 := by
        intro hLag
        have hLag' : s.stA.epoch = s.stB.epoch + 1 := by
          rw [hst]
          exact hLag
        rcases hPairB.2 hLag' with ⟨a', enc, b, dec, _, hPeer⟩
        rw [hst] at hPeer
        cases hPeer
      have hEqual : s.stB.epoch = e := by omega
      have hSame : s.stA.epoch = s.stB.epoch := by
        rw [hst]
        exact hEqual.symm
      have hGenerator : s.stA.controlPosition.1 = true := by
        rw [hst]
        rfl
      have hAllowed := hPairA.1 hSame hGenerator
      cases hb : s.stB
      case noHeaderReceived e' b dec =>
        have he' : e' = e := by
          simpa [hb, State.epoch] using hEqual
        subst e'
        exact ⟨b, dec, rfl⟩
      all_goals simp [hst, hb] at hAllowed
  · intro party e a hdr dec hst
    cases party
    · change s.stB = .headerReceived e a hdr dec at hst
      change ∃ pk sk b enc,
        (T e).keypair = some (pk, sk) ∧
          s.stA = .keysSampled e b sk (P.inc.toVector pk) enc ∧
          hdr = P.inc.toHeader pk
      have hUpper : s.stA.epoch ≤ e := by
        have h := hCrossA
        rw [hst] at h
        simp only [State.completedEpoch, State.epoch] at h
        have he : 0 < e := by
          simpa [hst, State.epoch] using hPosB
        have heq : e - 1 + 1 = e := by omega
        simpa only [State.epoch, heq] using h
      have hLower : e ≤ s.stA.epoch + 1 := by
        have h := hCrossB
        rw [hst] at h
        simp only [State.epoch] at h
        omega
      have hNotLag : ¬ e = s.stA.epoch + 1 := by
        intro hLag
        have hLag' : s.stB.epoch = s.stA.epoch + 1 := by
          rw [hst]
          exact hLag
        rcases hPairA.2 hLag' with ⟨a', enc, b, dec, _, hPeer⟩
        rw [hst] at hPeer
        cases hPeer
      have hEqual : s.stA.epoch = e := by omega
      have hMod : e % 2 = 1 := by
        have hLt : e % 2 < 2 := Nat.mod_lt _ (by omega)
        rw [hst] at hRoleB
        simp only [State.controlPosition, State.epoch] at hRoleB
        have hNot : e % 2 ≠ 0 := by
          simpa only [decide_eq_false_iff_not] using hRoleB.symm
        omega
      have hGenerator : s.stA.controlPosition.1 = true := by
        rw [hRoleA, hEqual]
        simp [hMod]
      have hSame : s.stA.epoch = s.stB.epoch := by
        rw [hst]
        exact hEqual
      have hAllowed := hPairA.1 hSame hGenerator
      cases ha : s.stA
      case keysSampled e' b sk vec enc =>
        have he' : e' = e := by
          simpa [ha, State.epoch] using hEqual
        subst e'
        rw [ha] at hLocalA
        rw [hst] at hLocalB
        simp only [LocalPayloadInv] at hLocalA hLocalB
        rcases hLocalA with ⟨_, pk, hkeyA, hvec, _⟩
        rcases hLocalB with ⟨_, _, kp, hkeyB, hhdr, _⟩
        have hkp : kp = (pk, sk) :=
          Option.some.inj (hkeyB.symm.trans hkeyA)
        subst kp
        refine ⟨pk, sk, b, enc, hkeyA, ?_, ?_⟩
        · simp [hvec] at ha ⊢
        · simpa using hhdr
      all_goals simp [hst, ha] at hAllowed
    · change s.stA = .headerReceived e a hdr dec at hst
      change ∃ pk sk b enc,
        (T e).keypair = some (pk, sk) ∧
          s.stB = .keysSampled e b sk (P.inc.toVector pk) enc ∧
          hdr = P.inc.toHeader pk
      have hUpper : s.stB.epoch ≤ e := by
        have h := hCrossB
        rw [hst] at h
        simp only [State.completedEpoch, State.epoch] at h
        have he : 0 < e := by
          simpa [hst, State.epoch] using hPosA
        have heq : e - 1 + 1 = e := by omega
        simpa only [State.epoch, heq] using h
      have hLower : e ≤ s.stB.epoch + 1 := by
        have h := hCrossA
        rw [hst] at h
        simp only [State.epoch] at h
        omega
      have hNotLag : ¬ e = s.stB.epoch + 1 := by
        intro hLag
        have hLag' : s.stA.epoch = s.stB.epoch + 1 := by
          rw [hst]
          exact hLag
        rcases hPairB.2 hLag' with ⟨a', enc, b, dec, _, hPeer⟩
        rw [hst] at hPeer
        cases hPeer
      have hEqual : s.stB.epoch = e := by omega
      have hMod : e % 2 = 0 := by
        have hLt : e % 2 < 2 := Nat.mod_lt _ (by omega)
        rw [hst] at hRoleA
        simp only [State.controlPosition, State.epoch] at hRoleA
        have hNot : e % 2 ≠ 1 := by
          simpa only [decide_eq_false_iff_not] using hRoleA.symm
        omega
      have hGenerator : s.stB.controlPosition.1 = true := by
        rw [hRoleB, hEqual]
        simp [hMod]
      have hSame : s.stB.epoch = s.stA.epoch := by
        rw [hst]
        exact hEqual
      have hAllowed := hPairB.1 hSame hGenerator
      cases hb : s.stB
      case keysSampled e' b sk vec enc =>
        have he' : e' = e := by
          simpa [hb, State.epoch] using hEqual
        subst e'
        rw [hb] at hLocalB
        rw [hst] at hLocalA
        simp only [LocalPayloadInv] at hLocalA hLocalB
        rcases hLocalB with ⟨_, pk, hkeyB, hvec, _⟩
        rcases hLocalA with ⟨_, _, kp, hkeyA, hhdr, _⟩
        have hkp : kp = (pk, sk) :=
          Option.some.inj (hkeyA.symm.trans hkeyB)
        subst kp
        refine ⟨pk, sk, b, enc, hkeyB, ?_, ?_⟩
        · simp [hvec] at hb ⊢
        · simpa using hhdr
      all_goals simp [hst, hb] at hAllowed

end MLKEMBraid
