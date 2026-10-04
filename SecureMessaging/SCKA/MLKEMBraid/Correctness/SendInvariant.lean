/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Correctness.Invariant

/-!
# Sends preserve the correctness invariant

The send oracle of either party preserves `CorrectnessInv` (`oracleSend_preserves_correctnessInv`).
A send from `keysUnsampled` or `headerReceived` extends the transcript with its sample; every other
send keeps the transcript.
-/

open OracleSpec OracleComp
open ErasureCodePayload.Streaming
open SCKAScheme.sckaCorrectnessSpec

namespace MLKEMBraid

variable {P : Parameters ProbComp} {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)

/-- If every message of a table and `msg` satisfy `MessagePayloadInv`, then so does every message of
the table after recording `msg` at index `k`. -/
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

/-- A send from `keysUnsampled` records its sampled key pair and leaves the successor consistent
with the extended transcript. -/
private theorem send_keysUnsampled_transcript {ik : InitKey} {T : ℕ → EpochTranscript P}
    {s : GameState P AuthState} (hT : TranscriptConsistent auth ik T s)
    (party : Bool) {r : SendResult P AuthState}
    (hr : r ∈ support (send P auth (s.stateAt party)))
    {e : ℕ} {a : AuthState} (hst : (s.stateAt party) = .keysUnsampled e a) :
    let s' := sendSuccessor s party r
    (ControlInv s' ∧ StatePairInv s') →
      ∃ pk sk,
        TranscriptConsistent auth ik
          (Function.update T e { (T e) with keypair := some (pk, sk) }) s' := by
  dsimp only
  -- The peer still holds an empty header decoder, and no stored message or key depends on the
  -- key-pair record of `e`.
  obtain ⟨b, dec, hpeer⟩ := peer_noHeaderReceived_of_keysUnsampled auth hT party hst
  have hpos := hT.control.epochKnowledge.keyPrefix.pos party
  rw [hst] at hpos
  simp only [State.epoch] at hpos
  have hLs := hT.local auth party
  have hLp := hT.local auth (!party)
  obtain ⟨hcorr, -, -, h0k, h0e, hKeypair, hEncaps, hLocalA, hLocalB, hMessages, hKeys⟩ := hT
  rw [hst] at hLs
  rw [hpeer] at hLp
  simp only [LocalPayloadInv] at hLs
  obtain ⟨ha, hkp0, hc0⟩ := hLs
  simp only [LocalPayloadInv, hkp0] at hLp
  obtain ⟨hb, hdec⟩ := hLp
  subst hdec
  rw [hst] at hr
  rcases (mem_support_send_iff auth).mp hr with ⟨_, _, pk, sk, -⟩
  set r' : SendResult P AuthState :=
    ⟨⟨e, .hdr, some (EncoderState.init P.ecpHdr
      (P.inc.toHeader pk, auth.macHeader a e (P.inc.toHeader pk))).nextChunk.1⟩,
      e - 1, none, .keysSampled e a sk (P.inc.toVector pk)
        (EncoderState.init P.ecpHdr
          (P.inc.toHeader pk, auth.macHeader a e (P.inc.toHeader pk))).nextChunk.2⟩
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
  have hep : ∀ who, (s.stateAt who).epoch = e := by
    intro who
    rcases Bool.eq_or_eq_not who party with rfl | rfl
    · rw [hst]; rfl
    · rw [hpeer]; rfl
  have hep' : ∀ who, ((sendSuccessor s party r').stateAt who).epoch =
      (s.stateAt who).epoch := fun who =>
    epoch_stateAt_sendSuccessor s party who r' (by rw [hst]; rfl)
  have hcomp' : ∀ who, ((sendSuccessor s party r').stateAt who).completedEpoch =
      (s.stateAt who).completedEpoch := fun who =>
    completedEpoch_stateAt_sendSuccessor s party who r' (by rw [hst]; rfl)
  have hLocal : ∀ who, LocalPayloadInv auth ik
      (Function.update T e { (T e) with keypair := some (pk, sk) })
        ((sendSuccessor s party r').stateAt who) := by
    intro who
    rcases Bool.eq_or_eq_not who party with rfl | rfl
    · simp only [stateAt_sendSuccessor, ↓reduceIte]
      exact ⟨haT, pk, hTke, rfl, rfl,
        congrArg (fun x => (P.inc.toHeader pk, auth.macHeader x e (P.inc.toHeader pk))) haT⟩
    · simp only [stateAt_sendSuccessor, Bool.not_eq_self, ↓reduceIte]
      rw [hpeer]
      simp only [LocalPayloadInv, hTke]
      refine ⟨hbT, rfl, ∅, ?_⟩
      simp [DecoderState.empty]
  rintro ⟨hC', hP'⟩
  refine ⟨pk, sk, by simpa only [correct_sendSuccessor] using hcorr, hC', hP',
    ?_, ?_, ?_, ?_, hLocal true, hLocal false, ?_, ?_⟩
  · rw [hTk 0 (by omega)]; exact h0k
  · rw [hTe]; exact h0e
  · intro e' pk' sk' hk
    by_cases he : e' = e
    · subst e'
      rw [hTke] at hk
      cases hk
      refine ⟨hpos, ?_⟩
      rw [← GameState.stateAt_generator]
      rw [hep', hep]
    · rw [hTk e' he] at hk
      obtain ⟨h0, hle⟩ := hKeypair e' pk' sk' hk
      refine ⟨h0, ?_⟩
      rw [← GameState.stateAt_generator]
      rw [hep', GameState.stateAt_generator]
      exact hle
  · intro e' es ct1 key hc
    rw [hTe] at hc
    have he : e' ≠ e := by
      rintro rfl
      rw [hc0] at hc
      cases hc
    obtain ⟨h0, hle, pk', sk', hkp', hdec⟩ := hEncaps e' es ct1 key hc
    refine ⟨h0, ?_, pk', sk', by rw [hTk e' he]; exact hkp', fun hle' => hdec ?_⟩
    · rw [← GameState.stateAt_encapsulator]
      rw [hcomp', GameState.stateAt_encapsulator]
      exact hle
    · rw [← GameState.stateAt_generator]
      rw [← GameState.stateAt_generator] at hle'
      rwa [hcomp'] at hle'
  · intro who
    change ∀ n msg tsnd, (sendSuccessor s party r').messagesAt who n = some (msg, tsnd) → _
    rw [messagesAt_sendSuccessor]
    split_ifs with hwho
    · subst who
      exact messagePayloads_update auth
        (fun n msg tsnd hmsg => hMsgOld msg (hMessages party n msg tsnd hmsg))
        ⟨pk, sk, 0, hTke, congrArg (fun x => some (P.ecpHdr.encode
          (P.inc.toHeader pk, auth.macHeader x e (P.inc.toHeader pk)) 0)) haT⟩
    · intro n msg tsnd hmsg
      exact hMsgOld msg (hMessages who n msg tsnd hmsg)
  · intro who e'
    change (sendSuccessor s party r').keysAt who e' = _
    rw [keysAt_sendSuccessor]
    simp only [r', ite_self]
    change s.keysAt who e' = if 0 < e' ∧
      e' ≤ ((sendSuccessor s party r').stateAt who).completedEpoch then _ else _
    rw [hcomp', hTe]
    exact hKeys who e'

/-- A send from `headerReceived` records its first-stage encapsulation and outputs the derived epoch
key; the successor is consistent with the extended transcript. -/
private theorem send_headerReceived_transcript {ik : InitKey} {T : ℕ → EpochTranscript P}
    {s : GameState P AuthState} (hT : TranscriptConsistent auth ik T s)
    (party : Bool) {r : SendResult P AuthState}
    (hr : r ∈ support (send P auth (s.stateAt party)))
    {e : ℕ} {a : AuthState} {hdr : P.inc.PKheader} {dec : DecoderState P.inc.PKvector P.Sym}
    (hst : (s.stateAt party) = .headerReceived e a hdr dec) :
    let s' := sendSuccessor s party r
    (ControlInv s' ∧ StatePairInv s') →
      ∃ pk sk encapsState ct1 key,
        (T e).keypair = some (pk, sk) ∧
        r.outputKey = some (e, P.kdfOK key e) ∧
        TranscriptConsistent auth ik
          (Function.update T e { (T e) with encaps1 := some (encapsState, ct1, key) }) s' := by
  dsimp only
  -- The generator is still at `keysSampled e`, whose completed epoch is `e - 1`, so the
  -- decapsulation clause for `e` is vacuous. Messages and authenticator values below `e`
  -- are unchanged.
  obtain ⟨pk, sk, b, enc, hkpT, hpeer, hhdr⟩ :=
    peer_keysSampled_of_headerReceived auth hT party hst
  have hpos := hT.control.epochKnowledge.keyPrefix.pos party
  rw [hst] at hpos
  simp only [State.epoch] at hpos
  have hRole := hT.control.role party
  have hLs := hT.local auth party
  have hLp := hT.local auth (!party)
  obtain ⟨hcorr, hControl, -, h0k, h0e, hKeypair, hEncaps, -, -, hMessages, hKeys⟩ := hT
  rw [hst] at hRole
  simp only [State.controlPosition, State.epoch] at hRole
  have hpar : ¬ e % 2 = if party then 1 else 0 := of_decide_eq_false hRole.symm
  rw [hst] at hLs
  rw [hpeer] at hLp
  simp only [LocalPayloadInv] at hLs hLp
  obtain ⟨ha, hc0, _, _, -, -, hdec⟩ := hLs
  obtain ⟨hb, pk', hkp', hvec, hecp, hpay⟩ := hLp
  subst hhdr hdec
  rw [hst] at hr
  cases (mem_support_send_iff auth).mp hr
  rename_i es ct1 k _
  set r' : SendResult P AuthState :=
    ⟨⟨e, .ct1, some (EncoderState.init P.ecpCt1 ct1).nextChunk.1⟩,
      e - 1, some (e, P.kdfOK k e),
      .ct1Sampled e (auth.update a e (P.kdfOK k e)) (P.inc.toHeader pk) es ct1
        (EncoderState.init P.ecpCt1 ct1).nextChunk.2 (DecoderState.empty P.ecpEk)⟩
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
  have hep : ∀ who, (s.stateAt who).epoch = e := by
    intro who
    rcases Bool.eq_or_eq_not who party with rfl | rfl
    · rw [hst]; rfl
    · rw [hpeer]; rfl
  have hcomp : ∀ who, (s.stateAt who).completedEpoch = e - 1 := by
    intro who
    rcases Bool.eq_or_eq_not who party with rfl | rfl
    · rw [hst]; rfl
    · rw [hpeer]; rfl
  have hep' : ∀ who, ((sendSuccessor s party r').stateAt who).epoch =
      (s.stateAt who).epoch := fun who =>
    epoch_stateAt_sendSuccessor s party who r' (by rw [hst]; rfl)
  have hcomp' : ∀ who, ((sendSuccessor s party r').stateAt who).completedEpoch =
      if who = party then e else e - 1 := by
    intro who
    simp only [stateAt_sendSuccessor]
    split_ifs
    · rfl
    · exact hcomp who
  have hBnd : ∀ (who : Bool) n msg tsnd,
      s.messagesAt who n = some (msg, tsnd) → msg.epoch ≤ e := by
    intro who n msg tsnd h
    have h2 := ((hControl.roles who).2.2 n msg tsnd h).2.1
    exact h2.trans_eq (hep who)
  have hempty : (DecoderState.empty P.ecpEk).chunks =
      ErasureCodePayload.payloadChunks P.ecpEk (P.inc.toVector pk) ∅ := by
    simp [DecoderState.empty]
  have hLocal : ∀ who, LocalPayloadInv auth ik
      (Function.update T e { (T e) with encaps1 := some (es, ct1, k) })
        ((sendSuccessor s party r').stateAt who) := by
    intro who
    rcases Bool.eq_or_eq_not who party with rfl | rfl
    · simp only [stateAt_sendSuccessor, ↓reduceIte]
      exact ⟨hAuthE.symm, pk, sk, k, by rw [hTk]; exact hkpT, hTce, rfl, ⟨rfl, rfl⟩,
        rfl, ∅, hempty⟩
    · simp only [stateAt_sendSuccessor, Bool.not_eq_self, ↓reduceIte]
      rw [hpeer]
      refine ⟨hb.trans (hAuthLt (e - 1) (by omega)).symm, pk',
        by rw [hTk]; exact hkp', hvec, hecp, ?_⟩
      rw [hAuthLt (e - 1) (by omega)]
      exact hpay
  have howner : decide (e % 2 = 1) = !party := by
    cases party
    · apply decide_eq_true
      simp only [Bool.false_eq_true, ↓reduceIte] at hpar
      omega
    · exact decide_eq_false hpar
  rintro ⟨hC', hP'⟩
  refine ⟨pk, sk, es, ct1, k, hkpT, rfl,
    by simpa only [correct_sendSuccessor] using hcorr, hC', hP', ?_, ?_, ?_, ?_,
    hLocal true, hLocal false, ?_, ?_⟩
  · rw [hTk]; exact h0k
  · rw [hTc 0 (by omega)]; exact h0e
  · intro e' pk'' sk'' hk
    rw [hTk] at hk
    obtain ⟨h0, hle⟩ := hKeypair e' pk'' sk'' hk
    refine ⟨h0, ?_⟩
    rw [← GameState.stateAt_generator]
    rw [hep', GameState.stateAt_generator]
    exact hle
  · intro e' es' ct1' key' hc'
    by_cases he : e' = e
    · subst e'
      rw [hTce] at hc'
      cases hc'
      refine ⟨hpos, ?_, pk, sk, by rw [hTk]; exact hkpT, fun hle' => ?_⟩
      · rw [← GameState.stateAt_encapsulator]
        rw [hcomp', howner]
        simp
      · rw [← GameState.stateAt_generator] at hle'
        rw [hcomp', howner] at hle'
        simp only [Bool.not_eq_self, ↓reduceIte] at hle'
        omega
    · rw [hTc e' he] at hc'
      obtain ⟨h0, hle, pk'', sk'', hkp'', hdec⟩ := hEncaps e' es' ct1' key' hc'
      have hleOld : e' ≤ e - 1 := by
        rw [← GameState.stateAt_encapsulator] at hle
        rwa [hcomp] at hle
      refine ⟨h0, ?_, pk'', sk'', by rw [hTk]; exact hkp'', fun _ => hdec ?_⟩
      · rw [← GameState.stateAt_encapsulator]
        rw [hcomp']; split_ifs <;> omega
      · rw [← GameState.stateAt_generator]
        rwa [hcomp]
  · intro who
    change ∀ n msg tsnd, (sendSuccessor s party r').messagesAt who n = some (msg, tsnd) → _
    rw [messagesAt_sendSuccessor]
    split_ifs with hwho
    · subst who
      exact messagePayloads_update auth
        (fun n msg tsnd hmsg => hMsgOld msg (hBnd party n msg tsnd hmsg)
          (hMessages party n msg tsnd hmsg)) ⟨es, ct1, k, 0, hTce, rfl⟩
    · intro n msg tsnd hmsg
      exact hMsgOld msg (hBnd who n msg tsnd hmsg) (hMessages who n msg tsnd hmsg)
  · intro who e'
    change (sendSuccessor s party r').keysAt who e' = _
    rw [keysAt_sendSuccessor]
    change (if who = party then Function.update (s.keysAt who) e (some (P.kdfOK k e))
      else s.keysAt who) e' = if 0 < e' ∧
        e' ≤ ((sendSuccessor s party r').stateAt who).completedEpoch then _ else _
    rw [hcomp']
    have hK : s.keysAt who e' =
        if 0 < e' ∧ e' ≤ (s.stateAt who).completedEpoch then
          (T e').encaps1.map (fun (_, _, key) => P.kdfOK key e') else none := hKeys who e'
    rw [hcomp] at hK
    by_cases hwho : who = party
    · rw [if_pos hwho, if_pos hwho]
      by_cases he : e' = e
      · subst e'
        rw [Function.update_self, if_pos ⟨hpos, le_rfl⟩, hTce]
        rfl
      · rw [Function.update_of_ne he, hK, hTc e' he]
        by_cases h1 : 0 < e' ∧ e' ≤ e - 1
        · rw [if_pos h1, if_pos ⟨h1.1, by omega⟩]
        · rw [if_neg h1, if_neg (by omega)]
    · rw [if_neg hwho, if_neg hwho, hK]
      by_cases he : e' = e
      · subst e'
        simp [show ¬ (0 < e ∧ e ≤ e - 1) by omega]
      · rw [hTc e' he]

/-- The states whose send samples nothing: all but `keysUnsampled` and `headerReceived`. -/
def State.SendsNoSample : State P AuthState → Prop
  | .keysUnsampled .. => False
  | .headerReceived .. => False
  | _ => True

/-- A send without sampling preserves epochs and `LocalPayloadInv`, outputs no key, and emits a
message satisfying `MessagePayloadInv`. -/
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

/-- A send that samples nothing keeps the game state consistent with the same transcript, provided
its successor satisfies the control and pair invariants. -/
theorem send_existing_transcript {ik : InitKey} {T : ℕ → EpochTranscript P}
    {s : GameState P AuthState} (hT : TranscriptConsistent auth ik T s)
    (party : Bool) {r : SendResult P AuthState}
    (hr : r ∈ support (send P auth (s.stateAt party)))
    (hsteady : (s.stateAt party).SendsNoSample) :
    let s' := sendSuccessor s party r
    (ControlInv s' ∧ StatePairInv s') → TranscriptConsistent auth ik T s' := by
  dsimp only
  obtain ⟨hnone, hep, hcomp, hLocalNew, hMsgNew⟩ :=
    send_steady_step auth ((mem_support_send_iff auth).mp hr) hsteady (hT.local auth party)
  rintro ⟨hC', hP'⟩
  refine hT.of_party auth (by simpa only [correct_sendSuccessor] using hT.correct)
    hC' hP' ?_ ?_ ?_ ?_ ?_
  · exact fun who => epoch_stateAt_sendSuccessor s party who r hep
  · exact fun who => completedEpoch_stateAt_sendSuccessor s party who r hcomp
  · intro who
    simp only [stateAt_sendSuccessor]
    split_ifs with hwho
    · exact hLocalNew
    · exact hT.local auth who
  · intro who
    rw [messagesAt_sendSuccessor]
    split_ifs with hwho
    · subst who
      exact messagePayloads_update auth (hT.messages party) hMsgNew
    · exact hT.messages who
  · intro who
    simp [keysAt_sendSuccessor, hnone]

/-- A supported send leaves the game consistent with a transcript whenever its successor
satisfies the control and pair invariants. -/
private theorem send_preserves_transcript {ik : InitKey} {T : ℕ → EpochTranscript P}
    {s : GameState P AuthState} (hT : TranscriptConsistent auth ik T s)
    (party : Bool) {r : SendResult P AuthState}
    (hr : r ∈ support (send P auth (s.stateAt party))) :
    (ControlInv (sendSuccessor s party r) ∧ StatePairInv (sendSuccessor s party r)) →
      ∃ T', TranscriptConsistent auth ik T' (sendSuccessor s party r) := by
  cases hst : (s.stateAt party) with
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

/-- The send oracle of either party preserves `ControlInv ∧ StatePairInv`. -/
theorem oracleSend_preserves_controlInv_statePairInv (party : Bool) :
    QueryImpl.PreservesInv
      (oracleSend auth irl sampleInitKey party)
      (fun s => ControlInv s ∧ StatePairInv s) := by
  intro t s hs z hz
  cases t
  cases party
  · exact correctnessImpl_preserves_controlInv_statePairInv auth irl sampleInitKey
      (OSendB (Rho := Message P.Sym)) s hs z hz
  · exact correctnessImpl_preserves_controlInv_statePairInv auth irl sampleInitKey
      (OSendA (Rho := Message P.Sym)) s hs z hz

/-- The send oracle of `party` preserves `CorrectnessInv`. -/
theorem oracleSend_preserves_correctnessInv (ik : InitKey) (party : Bool) :
    QueryImpl.PreservesInv
      (oracleSend auth irl sampleInitKey party)
      (CorrectnessInv auth ik) := by
  intro t s hs z hz
  cases t
  cases hzc : z.2.correct
  · exact Or.inl hzc
  have hCP : ∀ T, TranscriptConsistent auth ik T s → ControlInv z.2 ∧ StatePairInv z.2 :=
    fun T hT => oracleSend_preserves_controlInv_statePairInv auth irl sampleInitKey party
      () s ⟨hT.control, hT.statePair⟩ z hz
  obtain ⟨r, hr, rfl⟩ := (mem_support_oracleSend_run_iff auth irl sampleInitKey s party z).mp hz
  rcases hs with hsf | ⟨T, hT⟩
  · rw [sendUpdate_correct] at hzc
    rcases hkey : r.outputKey with _ | ⟨tI, key⟩ <;> simp [hkey, hsf] at hzc
  have hCPz := hCP T hT
  have heq := sendUpdate_eq_successor_of_correct s party r hT.correct hzc
  rw [heq] at hCPz ⊢
  exact Or.inr (send_preserves_transcript auth hT party hr hCPz)

end MLKEMBraid
