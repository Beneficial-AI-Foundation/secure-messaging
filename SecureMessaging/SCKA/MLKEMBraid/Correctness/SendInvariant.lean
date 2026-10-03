/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Correctness.Invariant

/-!
# Sends preserve the correctness invariant

A send samples a key pair (`SendEdge.keygen`), encapsulates against a received header
(`SendEdge.encaps1`), sends the next chunk of a recorded stream, or emits an empty message. The
transcript, extended when a new sample is drawn, is consistent with the successor state. Thus the
send oracles preserve `CorrectnessInv` (`oracleSend_preserves_correctnessInv`).

The three transcript lemmas describe the successor state without the correctness flag update;
`oracleSend_preserves_correctnessInv` supplies the flag, which must be true for the invariant to
say anything.
-/

open OracleSpec OracleComp
open ErasureCodePayload.Streaming
open SCKAScheme.sckaCorrectnessSpec

namespace MLKEMBraid

variable {P : Parameters ProbComp} {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)

/-- The send update before the oracle updates the correctness flag. -/
private def sendSuccessor (s : GameState P AuthState) (party : Bool)
    (r : SendResult P AuthState) : GameState P AuthState :=
  if party then
    { s with
      stA := r.state, tcurA := r.sendingEpoch, nA := s.nA + 1,
      msgA := Function.update s.msgA (s.nA + 1) (some (r.msg, r.sendingEpoch)),
      keyA := match r.outputKey with
        | none => s.keyA
        | some (e, key) => Function.update s.keyA e (some key) }
  else
    { s with
      stB := r.state, tcurB := r.sendingEpoch, nB := s.nB + 1,
      msgB := Function.update s.msgB (s.nB + 1) (some (r.msg, r.sendingEpoch)),
      keyB := match r.outputKey with
        | none => s.keyB
        | some (e, key) => Function.update s.keyB e (some key) }

/-- Recording one valid payload preserves the payload condition for the message table. -/
private theorem messagePayloads_update {ik : InitKey} {T : ℕ → EpochTranscript P}
    {messages : ℕ → Option (Message P.Sym × ℕ)} {msg : Message P.Sym} {tsnd k : ℕ}
    (hOld : ∀ n m t, messages n = some (m, t) → MessagePayloadInv auth ik T m)
    (hNew : MessagePayloadInv auth ik T msg) :
    ∀ n m t, Function.update messages k (some (msg, tsnd)) n = some (m, t) →
      MessagePayloadInv auth ik T m := by
  apply (Function.forall_update_iff messages
    (fun _ record => ∀ m t, record = some (m, t) → MessagePayloadInv auth ik T m)).2
  refine ⟨?_, fun n _ => hOld n⟩
  intro m t h
  cases h
  exact hNew

/-- The key-pair sample of a send from `keysUnsampled` fills the empty key-pair record of its
epoch; the extended transcript is consistent with the successor state. -/
private theorem send_keysUnsampled_transcript {ik : InitKey} {T : ℕ → EpochTranscript P}
    {s : GameState P AuthState} (hT : TranscriptConsistent auth ik T s)
    (party : Bool) {r : SendResult P AuthState}
    (hr : r ∈ support (send P auth (if party then s.stA else s.stB)))
    {e : ℕ} {a : AuthState} (hst : (if party then s.stA else s.stB) = .keysUnsampled e a) :
    let s' := sendSuccessor s party r
    (ControlInv s' ∧ StatePairInv s') →
      ∃ pk sk,
        TranscriptConsistent auth ik
          (Function.update T e { (T e) with keypair := some (pk, sk) }) s' := by
  -- The peer still holds an empty header decoder, and no stored message or key depends on the
  -- key-pair record of `e`.
  obtain ⟨b, dec, hpeer⟩ := peer_noHeaderReceived_of_keysUnsampled auth hT party hst
  have hposA := hT.control.epochKnowledge.keyPrefix.posA
  have hposB := hT.control.epochKnowledge.keyPrefix.posB
  have hRole := (hT.control.roles party).1
  obtain ⟨hcorr, -, -, h0k, h0e, hKeypair, hEncaps, hLocalA, hLocalB, hMessages, hKeys⟩ := hT
  have hpos : 0 < e := by
    have h : 0 < (if party then s.stA else s.stB).epoch := by
      cases party
      · exact hposB
      · exact hposA
    rw [hst] at h
    exact h
  rw [hst] at hRole
  simp only [State.controlPosition, State.epoch] at hRole
  have hpar : e % 2 = if party then 1 else 0 := of_decide_eq_true hRole.symm
  have hLs : LocalPayloadInv auth ik T (if party then s.stA else s.stB) := by
    cases party
    · exact hLocalB
    · exact hLocalA
  have hLp : LocalPayloadInv auth ik T (if party then s.stB else s.stA) := by
    cases party
    · exact hLocalA
    · exact hLocalB
  rw [hst] at hLs
  rw [hpeer] at hLp
  simp only [LocalPayloadInv] at hLs
  obtain ⟨ha, hkp0, hc0⟩ := hLs
  simp only [LocalPayloadInv, hkp0] at hLp
  obtain ⟨hb, hdec⟩ := hLp
  subst hdec
  rw [hst] at hr
  rcases (mem_support_send_iff auth).mp hr with ⟨_, _, pk, sk, -⟩
  have hTe : ∀ n, (Function.update T e { (T e) with keypair := some (pk, sk) } n).encaps1 =
      (T n).encaps1 := by
    intro n
    rcases eq_or_ne n e with rfl | hne
    · simp only [Function.update_self]
    · simp only [Function.update_of_ne hne]
  have hTk : ∀ n, n ≠ e →
      (Function.update T e { (T e) with keypair := some (pk, sk) } n).keypair =
        (T n).keypair :=
    fun n hne => by simp only [Function.update_of_ne hne]
  have hTke : (Function.update T e { (T e) with keypair := some (pk, sk) } e).keypair =
      some (pk, sk) := by
    simp only [Function.update_self]
  have hAuth : ∀ n, transcriptAuth auth ik
      (Function.update T e { (T e) with keypair := some (pk, sk) }) n =
      transcriptAuth auth ik T n :=
    fun n => transcriptAuth_congr auth n (fun i _ => hTe i)
  have haT : a = transcriptAuth auth ik
      (Function.update T e { (T e) with keypair := some (pk, sk) }) (e - 1) :=
    ha.trans (hAuth (e - 1)).symm
  have hbT : b = transcriptAuth auth ik
      (Function.update T e { (T e) with keypair := some (pk, sk) }) (e - 1) :=
    hb.trans (hAuth (e - 1)).symm
  have hKeyMono : ∀ n kp, (T n).keypair = some kp →
      (Function.update T e { (T e) with keypair := some (pk, sk) } n).keypair = some kp := by
    intro n kp h
    have hne : n ≠ e := by
      rintro rfl
      rw [hkp0] at h
      cases h
    rw [hTk n hne]
    exact h
  have hMsgOld : ∀ msg, MessagePayloadInv auth ik T msg →
      MessagePayloadInv auth ik
        (Function.update T e { (T e) with keypair := some (pk, sk) }) msg := by
    intro msg h
    exact h.transport auth (hKeyMono msg.epoch)
      (fun _ hc => (hTe msg.epoch).trans hc) (hAuth (msg.epoch - 1))
      (fun _ _ => hAuth msg.epoch)
  cases party
  · simp only [sendSuccessor, Bool.false_eq_true, ↓reduceIte] at hst hpeer hpar ⊢
    rintro ⟨hC', hP'⟩
    refine ⟨pk, sk, ?_⟩
    have hepB : s.stB.epoch = e := by rw [hst]; rfl
    have hcB : s.stB.completedEpoch = e - 1 := by rw [hst]; rfl
    refine ⟨hcorr, hC', hP', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hTk 0 (by omega)]
      exact h0k
    · rw [hTe]
      exact h0e
    · intro e' pk' sk' hk
      by_cases he : e' = e
      · subst e'
        rw [hTke] at hk
        cases hk
        refine ⟨hpos, ?_⟩
        rw [if_neg (by omega)]
        exact le_rfl
      · rw [hTk e' he] at hk
        obtain ⟨h0, hle⟩ := hKeypair e' pk' sk' hk
        refine ⟨h0, ?_⟩
        by_cases hpar' : e' % 2 = 1
        · rw [if_pos hpar'] at hle ⊢
          exact hle
        · rw [if_neg hpar'] at hle ⊢
          exact hle.trans_eq hepB
    · intro e' es ct1 key hc
      rw [hTe] at hc
      have he : e' ≠ e := by
        rintro rfl
        rw [hc0] at hc
        cases hc
      obtain ⟨h0, hle, pk', sk', hkp', hdec⟩ := hEncaps e' es ct1 key hc
      refine ⟨h0, ?_, pk', sk', by rw [hTk e' he]; exact hkp', fun hle' => hdec ?_⟩
      · by_cases hpar' : e' % 2 = 1
        · rw [if_pos hpar'] at hle ⊢
          exact hle.trans_eq hcB
        · rw [if_neg hpar'] at hle ⊢
          exact hle
      · by_cases hpar' : e' % 2 = 1
        · rw [if_pos hpar'] at hle' ⊢
          exact hle'
        · rw [if_neg hpar'] at hle' ⊢
          exact hle'.trans_eq hcB.symm
    · change LocalPayloadInv auth ik _ s.stA
      rw [hpeer]
      simp only [LocalPayloadInv, hTke]
      refine ⟨hbT, rfl, ∅, ?_⟩
      simp [DecoderState.empty]
    · exact ⟨haT, pk, hTke, rfl, rfl,
        congrArg (fun x => (P.inc.toHeader pk, auth.macHeader x e (P.inc.toHeader pk))) haT⟩
    · intro party'
      cases party'
      · exact messagePayloads_update auth
          (fun n msg tsnd hmsg => hMsgOld msg (hMessages false n msg tsnd hmsg))
          ⟨pk, sk, 0, hTke, congrArg (fun x => some (P.ecpHdr.encode
            (P.inc.toHeader pk, auth.macHeader x e (P.inc.toHeader pk)) 0)) haT⟩
      · intro n msg tsnd hmsg
        exact hMsgOld msg (hMessages true n msg tsnd hmsg)
    · intro party' e'
      have hK := hKeys party' e'
      cases party'
      · simp only [Bool.false_eq_true, ↓reduceIte] at hK ⊢
        rw [hTe]
        rw [hst] at hK
        exact hK
      · simp only [↓reduceIte] at hK ⊢
        rw [hTe]
        exact hK
  · simp only [sendSuccessor, ↓reduceIte] at hst hpeer hpar ⊢
    rintro ⟨hC', hP'⟩
    refine ⟨pk, sk, ?_⟩
    have hepA : s.stA.epoch = e := by rw [hst]; rfl
    have hcA : s.stA.completedEpoch = e - 1 := by rw [hst]; rfl
    refine ⟨hcorr, hC', hP', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hTk 0 (by omega)]
      exact h0k
    · rw [hTe]
      exact h0e
    · intro e' pk' sk' hk
      by_cases he : e' = e
      · subst e'
        rw [hTke] at hk
        cases hk
        refine ⟨hpos, ?_⟩
        rw [if_pos hpar]
        exact le_rfl
      · rw [hTk e' he] at hk
        obtain ⟨h0, hle⟩ := hKeypair e' pk' sk' hk
        refine ⟨h0, ?_⟩
        by_cases hpar' : e' % 2 = 1
        · rw [if_pos hpar'] at hle ⊢
          exact hle.trans_eq hepA
        · rw [if_neg hpar'] at hle ⊢
          exact hle
    · intro e' es ct1 key hc
      rw [hTe] at hc
      have he : e' ≠ e := by
        rintro rfl
        rw [hc0] at hc
        cases hc
      obtain ⟨h0, hle, pk', sk', hkp', hdec⟩ := hEncaps e' es ct1 key hc
      refine ⟨h0, ?_, pk', sk', by rw [hTk e' he]; exact hkp', fun hle' => hdec ?_⟩
      · by_cases hpar' : e' % 2 = 1
        · rw [if_pos hpar'] at hle ⊢
          exact hle
        · rw [if_neg hpar'] at hle ⊢
          exact hle.trans_eq hcA
      · by_cases hpar' : e' % 2 = 1
        · rw [if_pos hpar'] at hle' ⊢
          exact hle'.trans_eq hcA.symm
        · rw [if_neg hpar'] at hle' ⊢
          exact hle'
    · exact ⟨haT, pk, hTke, rfl, rfl,
        congrArg (fun x => (P.inc.toHeader pk, auth.macHeader x e (P.inc.toHeader pk))) haT⟩
    · change LocalPayloadInv auth ik _ s.stB
      rw [hpeer]
      simp only [LocalPayloadInv, hTke]
      refine ⟨hbT, rfl, ∅, ?_⟩
      simp [DecoderState.empty]
    · intro party'
      cases party'
      · intro n msg tsnd hmsg
        exact hMsgOld msg (hMessages false n msg tsnd hmsg)
      · exact messagePayloads_update auth
          (fun n msg tsnd hmsg => hMsgOld msg (hMessages true n msg tsnd hmsg))
          ⟨pk, sk, 0, hTke, congrArg (fun x => some (P.ecpHdr.encode
            (P.inc.toHeader pk, auth.macHeader x e (P.inc.toHeader pk)) 0)) haT⟩
    · intro party' e'
      have hK := hKeys party' e'
      cases party'
      · simp only [Bool.false_eq_true, ↓reduceIte] at hK ⊢
        rw [hTe]
        exact hK
      · simp only [↓reduceIte] at hK ⊢
        rw [hTe]
        rw [hst] at hK
        exact hK

/-- The encapsulation sample of a send from `headerReceived` fills the empty ciphertext record
of its epoch; the extended transcript is consistent with the successor state, and the send
outputs the derived epoch key. -/
private theorem send_headerReceived_transcript {ik : InitKey} {T : ℕ → EpochTranscript P}
    {s : GameState P AuthState} (hT : TranscriptConsistent auth ik T s)
    (party : Bool) {r : SendResult P AuthState}
    (hr : r ∈ support (send P auth (if party then s.stA else s.stB)))
    {e : ℕ} {a : AuthState} {hdr : P.inc.PKheader} {dec : DecoderState P.inc.PKvector P.Sym}
    (hst : (if party then s.stA else s.stB) = .headerReceived e a hdr dec) :
    let s' := sendSuccessor s party r
    (ControlInv s' ∧ StatePairInv s') →
      ∃ pk sk encapsState ct1 key,
        (T e).keypair = some (pk, sk) ∧
        r.outputKey = some (e, P.kdfOK key e) ∧
        TranscriptConsistent auth ik
          (Function.update T e { (T e) with encaps1 := some (encapsState, ct1, key) }) s' := by
  -- The generator is still at `keysSampled e`, whose completed epoch is `e - 1`, so the
  -- decapsulation clause for `e` is vacuous. Messages and authenticator values below `e`
  -- are unchanged.
  obtain ⟨pk, sk, b, enc, hkpT, hpeer, hhdr⟩ :=
    peer_keysSampled_of_headerReceived auth hT party hst
  have hposA := hT.control.epochKnowledge.keyPrefix.posA
  have hposB := hT.control.epochKnowledge.keyPrefix.posB
  have hRole := (hT.control.roles party).1
  obtain ⟨hcorr, hControl, -, h0k, h0e, hKeypair, hEncaps, hLocalA, hLocalB, hMessages,
    hKeys⟩ := hT
  have hpos : 0 < e := by
    have h : 0 < (if party then s.stA else s.stB).epoch := by
      cases party
      · exact hposB
      · exact hposA
    rw [hst] at h
    exact h
  rw [hst] at hRole
  simp only [State.controlPosition, State.epoch] at hRole
  have hpar : ¬ e % 2 = if party then 1 else 0 := of_decide_eq_false hRole.symm
  have hLs : LocalPayloadInv auth ik T (if party then s.stA else s.stB) := by
    cases party
    · exact hLocalB
    · exact hLocalA
  have hLp : LocalPayloadInv auth ik T (if party then s.stB else s.stA) := by
    cases party
    · exact hLocalA
    · exact hLocalB
  rw [hst] at hLs
  rw [hpeer] at hLp
  simp only [LocalPayloadInv] at hLs hLp
  obtain ⟨ha, hc0, _, _, -, -, hdec⟩ := hLs
  obtain ⟨hb, pk', hkp', hvec, hecp, hpay⟩ := hLp
  subst hhdr hdec
  rw [hst] at hr
  cases (mem_support_send_iff auth).mp hr
  rename_i es ct1 k _
  have hTk : ∀ n,
      (Function.update T e { (T e) with encaps1 := some (es, ct1, k) } n).keypair =
        (T n).keypair := by
    intro n
    rcases eq_or_ne n e with rfl | hne
    · simp only [Function.update_self]
    · simp only [Function.update_of_ne hne]
  have hTc : ∀ n, n ≠ e →
      (Function.update T e { (T e) with encaps1 := some (es, ct1, k) } n).encaps1 =
        (T n).encaps1 :=
    fun n hne => by simp only [Function.update_of_ne hne]
  have hTce : (Function.update T e { (T e) with encaps1 := some (es, ct1, k) } e).encaps1 =
      some (es, ct1, k) := by
    simp only [Function.update_self]
  have hAuthLt : ∀ n, n < e → transcriptAuth auth ik
      (Function.update T e { (T e) with encaps1 := some (es, ct1, k) }) n =
      transcriptAuth auth ik T n :=
    fun n hn => transcriptAuth_congr auth n (fun i hi => hTc i (by omega))
  have hAuthE : transcriptAuth auth ik
      (Function.update T e { (T e) with encaps1 := some (es, ct1, k) }) e =
      auth.update a e (P.kdfOK k e) := by
    obtain ⟨e0, rfl⟩ : ∃ e0, e = e0 + 1 := ⟨e - 1, by omega⟩
    rw [ha]
    simp only [transcriptAuth, hTce, hAuthLt e0 (by omega), Nat.add_sub_cancel]
  have hMsgOld : ∀ msg : Message P.Sym, msg.epoch ≤ e → MessagePayloadInv auth ik T msg →
      MessagePayloadInv auth ik
        (Function.update T e { (T e) with encaps1 := some (es, ct1, k) }) msg := by
    intro msg hle h
    have hlt : ∀ c, (T msg.epoch).encaps1 = some c → msg.epoch < e := by
      intro c hc
      have hne : msg.epoch ≠ e := by
        rintro he
        rw [he, hc0] at hc
        cases hc
      omega
    exact h.transport auth (fun _ hk => (hTk msg.epoch).trans hk)
      (fun c hc => (hTc msg.epoch (ne_of_lt (hlt c hc))).trans hc)
      (hAuthLt (msg.epoch - 1) (by omega)) (fun c hc => hAuthLt msg.epoch (hlt c hc))
  have hBnd : s.stA.epoch = e → s.stB.epoch = e → ∀ (party' : Bool) n msg tsnd,
      (if party' then s.msgA else s.msgB) n = some (msg, tsnd) → msg.epoch ≤ e := by
    intro hepA hepB party' n msg tsnd h
    have h2 := ((hControl.roles party').2.2 n msg tsnd h).2.1
    cases party'
    · exact h2.trans_eq hepB
    · exact h2.trans_eq hepA
  have hempty : (DecoderState.empty P.ecpEk).chunks =
      ErasureCodePayload.payloadChunks P.ecpEk (P.inc.toVector pk) ∅ := by
    simp [DecoderState.empty]
  cases party
  · simp only [sendSuccessor, Bool.false_eq_true, ↓reduceIte] at hst hpeer hpar ⊢
    rintro ⟨hC', hP'⟩
    refine ⟨pk, sk, es, ct1, k, hkpT, rfl, ?_⟩
    have hodd : e % 2 = 1 := by omega
    have hepA : s.stA.epoch = e := by rw [hpeer]; rfl
    have hepB : s.stB.epoch = e := by rw [hst]; rfl
    have hcA : s.stA.completedEpoch = e - 1 := by rw [hpeer]; rfl
    have hcB : s.stB.completedEpoch = e - 1 := by rw [hst]; rfl
    refine ⟨hcorr, hC', hP', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hTk]
      exact h0k
    · rw [hTc 0 (by omega)]
      exact h0e
    · intro e' pk'' sk'' hk
      rw [hTk] at hk
      obtain ⟨h0, hle⟩ := hKeypair e' pk'' sk'' hk
      refine ⟨h0, ?_⟩
      by_cases hpar' : e' % 2 = 1
      · rw [if_pos hpar'] at hle ⊢
        exact hle
      · rw [if_neg hpar'] at hle ⊢
        exact hle.trans_eq hepB
    · intro e' es' ct1' key' hc'
      by_cases he : e' = e
      · subst e'
        rw [hTce] at hc'
        cases hc'
        refine ⟨hpos, ?_, pk, sk, by rw [hTk]; exact hkpT, fun hle' => ?_⟩
        · rw [if_pos hodd]
          exact le_rfl
        · rw [if_pos hodd] at hle'
          exact absurd (hle'.trans_eq hcA) (by omega)
      · rw [hTc e' he] at hc'
        obtain ⟨h0, hle, pk'', sk'', hkp'', hdec⟩ := hEncaps e' es' ct1' key' hc'
        refine ⟨h0, ?_, pk'', sk'', by rw [hTk]; exact hkp'', fun hle' => hdec ?_⟩
        · by_cases hpar' : e' % 2 = 1
          · rw [if_pos hpar'] at hle ⊢
            change e' ≤ e
            have := hle.trans_eq hcB
            omega
          · rw [if_neg hpar'] at hle ⊢
            exact hle
        · by_cases hpar' : e' % 2 = 1
          · rw [if_pos hpar'] at hle' ⊢
            exact hle'
          · rw [if_neg hpar'] at hle' ⊢
            have h1 : e' ≤ e := hle'
            rw [hcB]
            omega
    · change LocalPayloadInv auth ik _ s.stA
      rw [hpeer]
      refine ⟨hb.trans (hAuthLt (e - 1) (by omega)).symm, pk', by rw [hTk]; exact hkp', hvec,
        hecp, ?_⟩
      rw [hAuthLt (e - 1) (by omega)]
      exact hpay
    · exact ⟨hAuthE.symm, pk, sk, k, by rw [hTk]; exact hkpT, hTce, rfl, ⟨rfl, rfl⟩, rfl,
        ∅, hempty⟩
    · intro party'
      cases party'
      · exact messagePayloads_update auth
          (fun n msg tsnd hmsg => hMsgOld msg (hBnd hepA hepB false n msg tsnd hmsg)
            (hMessages false n msg tsnd hmsg)) ⟨es, ct1, k, 0, hTce, rfl⟩
      · intro n msg tsnd hmsg
        exact hMsgOld msg (hBnd hepA hepB true n msg tsnd hmsg)
          (hMessages true n msg tsnd hmsg)
    · intro party' e'
      have hK := hKeys party' e'
      cases party'
      · simp only [Bool.false_eq_true, ↓reduceIte] at hK ⊢
        change _ = if 0 < e' ∧ e' ≤ e then _ else _
        rw [hcB] at hK
        by_cases he : e' = e
        · subst e'
          rw [Function.update_self, if_pos ⟨hpos, le_rfl⟩, hTce]
          rfl
        · rw [Function.update_of_ne he, hK, hTc e' he]
          by_cases h1 : 0 < e' ∧ e' ≤ e - 1
          · rw [if_pos h1, if_pos ⟨h1.1, by omega⟩]
          · rw [if_neg h1, if_neg (by omega)]
      · simp only [↓reduceIte] at hK ⊢
        by_cases he : e' = e
        · subst e'
          have hnc : ¬ (0 < e ∧ e ≤ e - 1) := by omega
          rw [hcA, if_neg hnc] at hK ⊢
          exact hK
        · rw [hTc e' he]
          exact hK
  · simp only [sendSuccessor, ↓reduceIte] at hst hpeer hpar ⊢
    rintro ⟨hC', hP'⟩
    refine ⟨pk, sk, es, ct1, k, hkpT, rfl, ?_⟩
    have hepA : s.stA.epoch = e := by rw [hst]; rfl
    have hepB : s.stB.epoch = e := by rw [hpeer]; rfl
    have hcA : s.stA.completedEpoch = e - 1 := by rw [hst]; rfl
    have hcB : s.stB.completedEpoch = e - 1 := by rw [hpeer]; rfl
    refine ⟨hcorr, hC', hP', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hTk]
      exact h0k
    · rw [hTc 0 (by omega)]
      exact h0e
    · intro e' pk'' sk'' hk
      rw [hTk] at hk
      obtain ⟨h0, hle⟩ := hKeypair e' pk'' sk'' hk
      refine ⟨h0, ?_⟩
      by_cases hpar' : e' % 2 = 1
      · rw [if_pos hpar'] at hle ⊢
        exact hle.trans_eq hepA
      · rw [if_neg hpar'] at hle ⊢
        exact hle
    · intro e' es' ct1' key' hc'
      by_cases he : e' = e
      · subst e'
        rw [hTce] at hc'
        cases hc'
        refine ⟨hpos, ?_, pk, sk, by rw [hTk]; exact hkpT, fun hle' => ?_⟩
        · rw [if_neg hpar]
          exact le_rfl
        · rw [if_neg hpar] at hle'
          exact absurd (hle'.trans_eq hcB) (by omega)
      · rw [hTc e' he] at hc'
        obtain ⟨h0, hle, pk'', sk'', hkp'', hdec⟩ := hEncaps e' es' ct1' key' hc'
        refine ⟨h0, ?_, pk'', sk'', by rw [hTk]; exact hkp'', fun hle' => hdec ?_⟩
        · by_cases hpar' : e' % 2 = 1
          · rw [if_pos hpar'] at hle ⊢
            exact hle
          · rw [if_neg hpar'] at hle ⊢
            change e' ≤ e
            have := hle.trans_eq hcA
            omega
        · by_cases hpar' : e' % 2 = 1
          · rw [if_pos hpar'] at hle' ⊢
            have h1 : e' ≤ e := hle'
            rw [hcA]
            omega
          · rw [if_neg hpar'] at hle' ⊢
            exact hle'
    · exact ⟨hAuthE.symm, pk, sk, k, by rw [hTk]; exact hkpT, hTce, rfl, ⟨rfl, rfl⟩, rfl,
        ∅, hempty⟩
    · change LocalPayloadInv auth ik _ s.stB
      rw [hpeer]
      refine ⟨hb.trans (hAuthLt (e - 1) (by omega)).symm, pk', by rw [hTk]; exact hkp', hvec,
        hecp, ?_⟩
      rw [hAuthLt (e - 1) (by omega)]
      exact hpay
    · intro party'
      cases party'
      · intro n msg tsnd hmsg
        exact hMsgOld msg (hBnd hepA hepB false n msg tsnd hmsg)
          (hMessages false n msg tsnd hmsg)
      · exact messagePayloads_update auth
          (fun n msg tsnd hmsg => hMsgOld msg (hBnd hepA hepB true n msg tsnd hmsg)
            (hMessages true n msg tsnd hmsg)) ⟨es, ct1, k, 0, hTce, rfl⟩
    · intro party' e'
      have hK := hKeys party' e'
      cases party'
      · simp only [Bool.false_eq_true, ↓reduceIte] at hK ⊢
        by_cases he : e' = e
        · subst e'
          have hnc : ¬ (0 < e ∧ e ≤ e - 1) := by omega
          rw [hcB, if_neg hnc] at hK ⊢
          exact hK
        · rw [hTc e' he]
          exact hK
      · simp only [↓reduceIte] at hK ⊢
        change _ = if 0 < e' ∧ e' ≤ e then _ else _
        rw [hcA] at hK
        by_cases he : e' = e
        · subst e'
          rw [Function.update_self, if_pos ⟨hpos, le_rfl⟩, hTce]
          rfl
        · rw [Function.update_of_ne he, hK, hTc e' he]
          by_cases h1 : 0 < e' ∧ e' ≤ e - 1
          · rw [if_pos h1, if_pos ⟨h1.1, by omega⟩]
          · rw [if_neg h1, if_neg (by omega)]

/-- The states whose send samples nothing: all but `keysUnsampled` and `headerReceived`. -/
def State.SendsNoSample : State P AuthState → Prop
  | .keysUnsampled .. => False
  | .headerReceived .. => False
  | _ => True

/-- A send from a state that samples nothing outputs no key, keeps the epoch, the completed
epoch and `LocalPayloadInv`, and emits a message satisfying `MessagePayloadInv`. -/
private theorem send_steady_step {ik : InitKey} {T : ℕ → EpochTranscript P}
    {st : State P AuthState} {r : SendResult P AuthState} (hedge : SendEdge auth st r)
    (hsteady : st.SendsNoSample) (hLocal : LocalPayloadInv auth ik T st) :
    r.outputKey = none ∧ r.state.epoch = st.epoch ∧ r.state.completedEpoch = st.completedEpoch ∧
      LocalPayloadInv auth ik T r.state ∧ MessagePayloadInv auth ik T r.msg := by
  cases hedge
  case keygen => exact False.elim hsteady
  case encaps1 => exact False.elim hsteady
  case hdrChunk _ _ sk _ enc =>
    have hL := hLocal
    simp only [LocalPayloadInv] at hL
    obtain ⟨-, pk, hkp, -, hecp, hpay⟩ := hL
    refine ⟨rfl, rfl, rfl, ?_, pk, sk, enc.nextIndex, hkp, ?_⟩
    · simpa only [LocalPayloadInv, EncoderState.nextChunk] using hLocal
    · simp only [EncoderState.nextChunk]
      rw [hecp, hpay]
  case ekChunk _ _ sk _ enc =>
    have hL := hLocal
    simp only [LocalPayloadInv] at hL
    obtain ⟨-, pk, _, _, _, hkp, -, -, hecp, hpay⟩ := hL
    refine ⟨rfl, rfl, rfl, ?_, pk, sk, enc.nextIndex, hkp, ?_⟩
    · simpa only [LocalPayloadInv, EncoderState.nextChunk] using hLocal
    · simp only [EncoderState.nextChunk]
      rw [hecp, hpay]
  case ackChunk _ _ sk _ enc =>
    have hL := hLocal
    simp only [LocalPayloadInv] at hL
    obtain ⟨-, pk, _, _, hkp, -, hecp, hpay⟩ := hL
    refine ⟨rfl, rfl, rfl, ?_, pk, sk, enc.nextIndex, hkp, ?_⟩
    · simpa only [LocalPayloadInv, EncoderState.nextChunk] using hLocal
    · simp only [EncoderState.nextChunk]
      rw [hecp, hpay]
  case idleEkSent => exact ⟨rfl, rfl, rfl, hLocal, rfl⟩
  case idleNoHeader => exact ⟨rfl, rfl, rfl, hLocal, rfl⟩
  case ct1Chunk _ _ _ es ct1 enc _ =>
    have hL := hLocal
    simp only [LocalPayloadInv] at hL
    obtain ⟨-, _, _, key, -, hc, -, ⟨hecp, hpay⟩, -⟩ := hL
    refine ⟨rfl, rfl, rfl, ?_, es, ct1, key, enc.nextIndex, hc, ?_⟩
    · simpa only [LocalPayloadInv, EncoderState.nextChunk] using hLocal
    · simp only [EncoderState.nextChunk]
      rw [hecp, hpay]
  case ct1ChunkVec _ _ es ct1 _ _ enc =>
    have hL := hLocal
    simp only [LocalPayloadInv] at hL
    obtain ⟨-, _, _, key, -, hc, -, -, hecp, hpay⟩ := hL
    refine ⟨rfl, rfl, rfl, ?_, es, ct1, key, enc.nextIndex, hc, ?_⟩
    · simpa only [LocalPayloadInv, EncoderState.nextChunk] using hLocal
    · simp only [EncoderState.nextChunk]
      rw [hecp, hpay]
  case idleAcknowledged => exact ⟨rfl, rfl, rfl, hLocal, rfl⟩
  case ct2Chunk _ _ enc =>
    have hL := hLocal
    simp only [LocalPayloadInv] at hL
    obtain ⟨-, pk, sk, es, ct1, key, hkp, hc, hecp, hpay⟩ := hL
    refine ⟨rfl, rfl, rfl, ?_, pk, sk, es, ct1, key, enc.nextIndex, hkp, hc, ?_⟩
    · simpa only [LocalPayloadInv, EncoderState.nextChunk] using hLocal
    · simp only [EncoderState.nextChunk]
      rw [hecp, hpay]

/-- A send that samples nothing keeps the transcript consistent with the successor state. -/
private theorem send_existing_transcript {ik : InitKey} {T : ℕ → EpochTranscript P}
    {s : GameState P AuthState} (hT : TranscriptConsistent auth ik T s)
    (party : Bool) {r : SendResult P AuthState}
    (hr : r ∈ support (send P auth (if party then s.stA else s.stB)))
    (hsteady : (if party then s.stA else s.stB).SendsNoSample) :
    let s' := sendSuccessor s party r
    (ControlInv s' ∧ StatePairInv s') → TranscriptConsistent auth ik T s' := by
  have hLocal : LocalPayloadInv auth ik T (if party then s.stA else s.stB) := by
    cases party
    · exact hT.localB
    · exact hT.localA
  obtain ⟨hnone, hep, hcomp, hLocalNew, hMsgNew⟩ :=
    send_steady_step auth ((mem_support_send_iff auth).mp hr) hsteady hLocal
  cases party
  · simp only [sendSuccessor, Bool.false_eq_true, ↓reduceIte] at hep hcomp ⊢
    rintro ⟨hC', hP'⟩
    refine hT.of_fields auth hT.correct hC' hP' rfl hep rfl hcomp hT.localA hLocalNew
      ?_ rfl (by simp [hnone])
    intro party'
    cases party'
    · exact messagePayloads_update auth (hT.messages false) hMsgNew
    · exact hT.messages true
  · simp only [sendSuccessor, ↓reduceIte] at hep hcomp ⊢
    rintro ⟨hC', hP'⟩
    refine hT.of_fields auth hT.correct hC' hP' hep rfl hcomp rfl hLocalNew hT.localB
      ?_ (by simp [hnone]) rfl
    intro party'
    cases party'
    · exact hT.messages false
    · exact messagePayloads_update auth (hT.messages true) hMsgNew

/-- A supported send leaves the game consistent with a transcript whenever its successor
satisfies the control and pair invariants. -/
private theorem send_preserves_transcript {ik : InitKey} {T : ℕ → EpochTranscript P}
    {s : GameState P AuthState} (hT : TranscriptConsistent auth ik T s)
    (party : Bool) {r : SendResult P AuthState}
    (hr : r ∈ support (send P auth (if party then s.stA else s.stB))) :
    (ControlInv (sendSuccessor s party r) ∧ StatePairInv (sendSuccessor s party r)) →
      ∃ T', TranscriptConsistent auth ik T' (sendSuccessor s party r) := by
  cases hst : (if party then s.stA else s.stB) with
  | keysUnsampled e a =>
      intro hCP
      obtain ⟨pk, sk, h⟩ := send_keysUnsampled_transcript auth hT party hr hst hCP
      exact ⟨_, h⟩
  | headerReceived e a hdr dec =>
      intro hCP
      obtain ⟨pk, sk, es, ct1, key, -, -, h⟩ :=
        send_headerReceived_transcript auth hT party hr hst hCP
      exact ⟨_, h⟩
  | _ =>
      intro hCP
      exact ⟨T, send_existing_transcript auth hT party hr
        (by simp only [hst, State.SendsNoSample]) hCP⟩

variable [DecidableEq P.EpochKey] [DecidableEq P.Sym]
  (irl : P.kem.IncrementalRandLeak P.inc) (sampleInitKey : ProbComp InitKey)

/-- The send oracle of `party` preserves `CorrectnessInv`. -/
theorem oracleSend_preserves_correctnessInv (ik : InitKey) (party : Bool) :
    QueryImpl.PreservesInv
      (if party then SCKAScheme.oracleSendA (scheme P auth irl sampleInitKey)
        else SCKAScheme.oracleSendB (scheme P auth irl sampleInitKey))
      (CorrectnessInv auth ik) := by
  -- A false entry flag forces a false result flag. Otherwise the lemma for the sender's state
  -- gives a consistent transcript for the successor with the entry flag, and a true result flag
  -- makes that successor the oracle's state.
  cases party
  · intro t s hs z hz
    cases t
    change z ∈ support ((SCKAScheme.oracleSendB (scheme P auth irl sampleInitKey) ()).run s) at hz
    have hCP : ∀ T, TranscriptConsistent auth ik T s → ControlInv z.2 ∧ StatePairInv z.2 :=
      fun T hT => correctnessImpl_preserves_controlInv_statePairInv auth irl sampleInitKey
        (OSendB (Rho := Message P.Sym)) s ⟨hT.control, hT.statePair⟩ z hz
    cases hzc : z.2.correct
    · exact Or.inl hzc
    obtain ⟨r, hr, rfl⟩ := (mem_support_oracleSendB_run_iff auth irl sampleInitKey s z).mp hz
    rcases hs with hsf | ⟨T, hT⟩
    · rcases hkey : r.outputKey with _ | ⟨tI, key⟩ <;>
        simp [SCKAScheme.sendBUpdate, hkey, hsf] at hzc
    have hCPz := hCP T hT
    have h := send_preserves_transcript auth hT false hr
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩
    all_goals
      simp only [sendSuccessor, Bool.false_eq_true, ↓reduceIte, hkey, hT.correct] at h
      simp only [SCKAScheme.sendBUpdate, hkey] at hzc hCPz ⊢
      rw [hzc] at hCPz ⊢
      exact Or.inr (h hCPz)
  · intro t s hs z hz
    cases t
    change z ∈ support ((SCKAScheme.oracleSendA (scheme P auth irl sampleInitKey) ()).run s) at hz
    have hCP : ∀ T, TranscriptConsistent auth ik T s → ControlInv z.2 ∧ StatePairInv z.2 :=
      fun T hT => correctnessImpl_preserves_controlInv_statePairInv auth irl sampleInitKey
        (OSendA (Rho := Message P.Sym)) s ⟨hT.control, hT.statePair⟩ z hz
    cases hzc : z.2.correct
    · exact Or.inl hzc
    obtain ⟨r, hr, rfl⟩ := (mem_support_oracleSendA_run_iff auth irl sampleInitKey s z).mp hz
    rcases hs with hsf | ⟨T, hT⟩
    · rcases hkey : r.outputKey with _ | ⟨tI, key⟩ <;>
        simp [SCKAScheme.sendAUpdate, hkey, hsf] at hzc
    have hCPz := hCP T hT
    have h := send_preserves_transcript auth hT true hr
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩
    all_goals
      simp only [sendSuccessor, ↓reduceIte, hkey, hT.correct] at h
      simp only [SCKAScheme.sendAUpdate, hkey] at hzc hCPz ⊢
      rw [hzc] at hCPz ⊢
      exact Or.inr (h hCPz)

end MLKEMBraid
