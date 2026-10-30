/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.Invariant.Basic
import SecureMessaging.SCKA.MLKEMBraid.Security.Sampling
import SecureMessaging.SCKA.MLKEMBraid.Correctness.ReceiveInvariant

/-!
# Receives preserve the repaired invariant

A recorded message either advances a receive without an output key, or completes the decoder of
the second ciphertext component at the key generator. In the second case the repaired receive
outputs the recorded key. The invariant holds after both kinds of receive. The proof of the
second case does not assume that decapsulation succeeds.
-/

open OracleSpec OracleComp
open ErasureCodePayload.Streaming

namespace MLKEMBraid.NoAuth

variable {P : Parameters ProbComp}

section Receive

variable [DecidableEq P.Sym] {hMac : P.Mac = Unit} {T : ℕ → EpochTranscript P}
  {s : MLKEMBraid.GameState P Unit}

/-- Outside the generator's `ct₂` states, `repairedRecv` runs `recvSCKA`. -/
theorem repairedRecv_eq_of_not_ekSent (repair : Bool) (T : ℕ → EpochTranscript P)
    {st : State P Unit} (msg : Message P.Sym)
    (hst : ∀ e a sk ct1 dec, st ≠ .ekSentCt1Received e a sk ct1 dec) :
    repairedRecv P hMac repair T st msg = MLKEMBraid.recvSCKA P (auth P hMac) st msg := by
  cases repair
  · rfl
  · cases st <;> first | rfl | exact absurd rfl (hst _ _ _ _ _)

/-- Under the repaired invariant, a recorded message either completes the `ct₂` decoder of the
generator's epoch, or `receive` accepts it without an output key, keeps the local invariant, and
`repairedRecv` runs it unchanged. -/
theorem receive_cases
    (hHdrCorrect : P.ecpHdr.ec.Correct) (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct) (hCt2Correct : P.ecpCt2.ec.Correct)
    (h : RepairInv hMac T s) (party : Bool) {n : ℕ} {msg : Message P.Sym} {tsnd : ℕ}
    (hmsg : s.messagesAt (!party) n = some (msg, tsnd)) :
    (∃ e sk ct1 dec chunk pk es k tag,
      s.stateAt party = .ekSentCt1Received e () sk ct1 dec ∧
      msg = ⟨e, .ct2, some chunk⟩ ∧ (T e).keypair = some (pk, sk) ∧
      (T e).encaps1 = some (es, ct1, k) ∧
      (dec.addChunk chunk).decodedPayload =
        some (P.hEnc2.encaps2Det es (P.inc.toHeader pk) (P.inc.toVector pk), tag)) ∨
    (∃ r, receive P (auth P hMac) (s.stateAt party) msg = .ok r ∧ r.outputKey = none ∧
      LocalPayloadInv (auth P hMac) () T r.state ∧
      ∀ repair, repairedRecv P hMac repair T (s.stateAt party) msg =
        MLKEMBraid.recvSCKA P (auth P hMac) (s.stateAt party) msg) := by
  have hRole := h.control.role party
  have hLocal := h.local _ party
  have hPayload := h.messages (!party) n msg tsnd hmsg
  have hF : (s.stateAt party).controlPosition.isGenerator = false →
      ∀ t, t = (s.stateAt party).epoch →
        (if t % 2 = 1 then s.stB else s.stA) = (s.stateAt party) ∧
          (if (t + 1) % 2 = 1 then s.stA else s.stB) = (s.stateAt party) := by
    intro hencapsulator t ht
    cases party
    · simp only [GameState.stateAt, Bool.false_eq_true, ↓reduceIte] at hRole hencapsulator ht ⊢
      rw [hencapsulator] at hRole
      have hne := of_decide_eq_false hRole.symm
      rw [ite_eq_left (by omega), ite_eq_right (by omega)]
      exact ⟨rfl, rfl⟩
    · simp only [GameState.stateAt, ↓reduceIte] at hRole hencapsulator ht ⊢
      rw [hencapsulator] at hRole
      have hne := of_decide_eq_false hRole.symm
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      exact ⟨rfl, rfl⟩
  obtain ⟨st, hst⟩ : ∃ st, s.stateAt party = st := ⟨_, rfl⟩
  rw [hst] at hLocal hF ⊢
  have hplain : ∀ r, receive P (auth P hMac) st msg = .ok r → r.outputKey = none →
      LocalPayloadInv (auth P hMac) () T r.state →
      (∀ e a sk ct1 dec, st ≠ .ekSentCt1Received e a sk ct1 dec) →
      ∃ r, receive P (auth P hMac) st msg = .ok r ∧ r.outputKey = none ∧
        LocalPayloadInv (auth P hMac) () T r.state ∧
        ∀ repair, repairedRecv P hMac repair T st msg =
          MLKEMBraid.recvSCKA P (auth P hMac) st msg :=
    fun r hr hnone hinv hne =>
      ⟨r, hr, hnone, hinv, fun repair => repairedRecv_eq_of_not_ekSent repair T msg hne⟩
  cases st
  case keysUnsampled e a =>
    have hsame : receive P (auth P hMac) (.keysUnsampled e a) msg =
        .ok ⟨e - 1, none, .keysUnsampled e a⟩ := by
      rcases msg with ⟨me, mt, md⟩
      cases mt <;> cases md <;> rfl
    exact Or.inr (hplain _ hsame rfl hLocal (by intros; simp))
  case keysSampled e a sk vec enc =>
    obtain ⟨r, hr, hnone, hinv⟩ :=
      receive_keysSampled_payload (auth P hMac) () T e a sk vec enc msg hLocal hPayload
    exact Or.inr (hplain r hr hnone hinv (by intros; simp))
  case headerSent e a sk dec enc =>
    obtain ⟨r, hr, hnone, hinv⟩ := receive_headerSent_payload (auth P hMac) hCt1Correct () T
      e a sk dec enc msg hLocal hPayload
    exact Or.inr (hplain r hr hnone hinv (by intros; simp))
  case ct1Received e a sk ct1 enc =>
    obtain ⟨r, hr, hnone, hinv⟩ :=
      receive_ct1Received_payload (auth P hMac) () T e a sk ct1 enc msg hLocal hPayload
    exact Or.inr (hplain r hr hnone hinv (by intros; simp))
  case ekSentCt1Received e a sk ct1 dec =>
    have hold := hLocal
    obtain ⟨-, pk, es, key, hkp, hc, hdec⟩ := hLocal
    rcases msg with ⟨me, mt, md⟩
    cases mt with
    | ct2 =>
        cases md with
        | none =>
            exact Or.inr ⟨_, rfl, rfl, hold, fun repair => by cases repair <;> rfl⟩
        | some chunk =>
            by_cases he : me = e
            · subst me
              simp only [MessagePayloadInv] at hPayload
              obtain ⟨pk', sk', es', ct1', key', i, hkp', hc', hchunk⟩ := hPayload
              obtain ⟨rfl, rfl⟩ : pk = pk' ∧ sk = sk' := by simpa using hkp.symm.trans hkp'
              obtain ⟨rfl, rfl, rfl⟩ : es = es' ∧ ct1 = ct1' ∧ key = key' := by
                simpa using hc.symm.trans hc'
              have hch := Option.some.inj hchunk
              have hC :=
                DecoderState.addChunk_encode_of_payloadChunks P.ecpCt2 hCt2Correct _ dec hdec i
              rw [← hch] at hC
              obtain ⟨hecp, ⟨I, hchunks⟩, hnone | hsome⟩ := hC
              · refine Or.inr ⟨⟨e - 1, none, .ekSentCt1Received e a sk ct1 (dec.addChunk chunk)⟩,
                  by simp [receive, Message.wellFormed, hnone], rfl,
                  ⟨Subsingleton.elim _ _, pk, es, key, hkp, hc, hecp, I, hchunks⟩,
                  fun repair => ?_⟩
                cases repair
                · rfl
                · simp [repairedRecv, Message.wellFormed, hnone]
              · exact Or.inl ⟨e, sk, ct1, dec, chunk, pk, es, key, _, rfl, rfl, hkp, hc, hsome⟩
            · refine Or.inr ⟨⟨e - 1, none, .ekSentCt1Received e a sk ct1 dec⟩,
                by simp [receive, Message.wellFormed, State.epoch, he], rfl, hold,
                fun repair => ?_⟩
              cases repair
              · rfl
              · simp [repairedRecv, Message.wellFormed, he]
    | _ =>
        cases md <;>
          exact Or.inr ⟨_, rfl, rfl, hold, fun repair => by cases repair <;> rfl⟩
  case noHeaderReceived e a dec =>
    have hNoEncaps : (T e).encaps1 = none := by
      cases hce : (T e).encaps1 with
      | none => rfl
      | some c =>
          obtain ⟨hpos, hle, -⟩ := h.encaps e c.1 c.2.1 c.2.2 hce
          rw [(hF rfl e rfl).1] at hle
          have hcomp : (State.noHeaderReceived e a dec : State P Unit).completedEpoch =
              e - 1 := rfl
          omega
    obtain ⟨r, hr, hnone, hinv⟩ := receive_noHeaderReceived_payload (auth P hMac) () T
      hHdrCorrect e a dec msg hLocal hPayload hNoEncaps
    exact Or.inr (hplain r hr hnone hinv (by intros; simp))
  case headerReceived e a hdr dec =>
    exact Or.inr (hplain ⟨e - 1, none, .headerReceived e a hdr dec⟩
      (by simp [receive, State.epoch]) rfl hLocal (by intros; simp))
  case ct1Sampled e a hdr encapsState ct1 enc dec =>
    obtain ⟨r, hr, hnone, hinv⟩ := receive_ct1Sampled_payload (auth P hMac) () T hEkCorrect
      e a hdr encapsState ct1 enc dec msg hLocal hPayload
    exact Or.inr (hplain r hr hnone hinv (by intros; simp))
  case ekReceivedCt1Sampled e a encapsState ct1 hdr vec enc =>
    obtain ⟨r, hr, hnone, hinv⟩ := receive_ekReceivedCt1Sampled_payload (auth P hMac) () T
      e a encapsState ct1 hdr vec enc msg hLocal
    exact Or.inr (hplain r hr hnone hinv (by intros; simp))
  case ct1Acknowledged e a hdr encapsState ct1 dec =>
    obtain ⟨r, hr, hnone, hinv⟩ := receive_ct1Acknowledged_payload (auth P hMac) () T
      hEkCorrect e a hdr encapsState ct1 dec msg hLocal hPayload
    exact Or.inr (hplain r hr hnone hinv (by intros; simp))
  case ct2Sampled e a enc =>
    have hkp : (T (e + 1)).keypair = none := by
      cases hk : (T (e + 1)).keypair with
      | none => rfl
      | some kp =>
          obtain ⟨-, hle⟩ := h.keypair (e + 1) kp.1 kp.2 hk
          rw [(hF rfl e rfl).2] at hle
          have hep : (State.ct2Sampled e a enc : State P Unit).epoch = e := rfl
          omega
    have hce : (T (e + 1)).encaps1 = none := by
      cases hc : (T (e + 1)).encaps1 with
      | none => rfl
      | some c =>
          obtain ⟨-, -, pk, sk, hkp', -⟩ := h.encaps (e + 1) c.1 c.2.1 c.2.2 hc
          rw [hkp] at hkp'
          cases hkp'
    obtain ⟨r, hr, hnone, hinv⟩ :=
      receive_ct2Sampled_payload (auth P hMac) () T e a enc msg hLocal ⟨hkp, hce⟩
    exact Or.inr (hplain r hr hnone hinv (by intros; simp))

omit [DecidableEq P.Sym] in
/-- The game-state message bound needed by the known-prefix check of a receive. -/
private theorem knownPrefix_recv (h : RepairInv hMac T s) (party : Bool) {n : ℕ}
    {msg : Message P.Sym} {tsnd : ℕ} (hmsg : s.messagesAt (!party) n = some (msg, tsnd)) :
    SCKAScheme.knownPrefix (s.keysAt party) (max (s.tcurAt party) (msg.epoch - 1)) = true := by
  have hE := h.control.epochKnowledge
  have hbound := (hE.msgs (!party) n msg tsnd hmsg).2.1
  simp only [Bool.not_not] at hbound
  have htcur := hE.tcur_le party
  have hmax : max (s.tcurAt party) (msg.epoch - 1) ≤ (s.stateAt party).completedEpoch := by
    omega
  exact SCKAScheme.knownPrefix_eq_true
    fun t h0 hle => (hE.keyPrefix.keys party t).2 ⟨h0, hle.trans hmax⟩

/-- An accepted receive without output key keeps the invariant for the same transcript. -/
private theorem recvNoKey (irl : P.kem.IncrementalRandLeak P.inc) [DecidableEq P.EpochKey]
    (h : RepairInv hMac T s) (party : Bool) {n : ℕ} {msg : Message P.Sym} {tsnd : ℕ}
    (hmsg : s.messagesAt (!party) n = some (msg, tsnd))
    {r : RecvResult P Unit} (hr : receive P (auth P hMac) (s.stateAt party) msg = .ok r)
    (hnone : r.outputKey = none) (hLocalNew : LocalPayloadInv (auth P hMac) () T r.state) :
    RepairInv hMac T (recvUpdate s party tsnd r (msg.epoch - 1)) := by
  have hrep := h.control.recordedReport.report (!party) n msg tsnd hmsg
  have hzc : (recvUpdate s party tsnd r (msg.epoch - 1)).correct = true := by
    rw [recvUpdate_correct, hnone]
    simp only [Bool.and_eq_true]
    exact ⟨⟨h.correct, by simp [hrep]⟩, knownPrefix_recv h party hmsg⟩
  have hCP : ControlInv (recvUpdate s party tsnd r (msg.epoch - 1)) ∧
      StatePairInv (recvUpdate s party tsnd r (msg.epoch - 1)) := by
    have hsupp : (some (msg.epoch - 1, r.outputKey.map Prod.fst),
        recvUpdate s party tsnd r (msg.epoch - 1)) ∈
        support ((oracleRecv (auth P hMac) irl (pure ()) party n).run s) := by
      cases party
      · rw [oracleRecv, ite_eq_right Bool.false_ne_true,
          oracleRecvB_run_eq_of_ok (auth P hMac) irl (pure ()) hmsg hr]
        simp [recvUpdate]
      · rw [oracleRecv, ite_eq_left rfl,
          oracleRecvA_run_eq_of_ok (auth P hMac) irl (pure ()) hmsg hr]
        simp [recvUpdate]
    cases party
    · exact correctnessImpl_preserves_controlInv_statePairInv (auth P hMac) irl (pure ())
        (SCKAScheme.sckaCorrectnessSpec.ORecvB (Rho := Message P.Sym) n) s
        ⟨h.control, h.statePair⟩ _ hsupp
    · exact correctnessImpl_preserves_controlInv_statePairInv (auth P hMac) irl (pure ())
        (SCKAScheme.sckaCorrectnessSpec.ORecvA (Rho := Message P.Sym) n) s
        ⟨h.control, h.statePair⟩ _ hsupp
  have hsucc := recvUpdate_eq_successor_of_correct s party tsnd r (msg.epoch - 1) h.correct hzc
  rw [hsucc] at hzc hCP ⊢
  have hedge := ReceiveEdge.of_eq_ok (auth P hMac) hr
  have hpos := h.control.epochKnowledge.keyPrefix.pos party
  have hcompEq : r.state.completedEpoch = (s.stateAt party).completedEpoch := by
    have := (hedge.completedEpoch hpos).2
    simpa only [hnone] using this
  refine h.of_le hzc hCP.1 hCP.2 ?_ ?_ ?_ ?_ ?_
  · intro who
    rw [stateAt_recvSuccessor]
    split_ifs with hwho
    · subst who; exact hedge.epoch_le.1
    · exact le_rfl
  · intro who
    rw [stateAt_recvSuccessor]
    split_ifs with hwho
    · subst who; exact hcompEq.ge
    · exact le_rfl
  · intro who
    rw [stateAt_recvSuccessor]
    split_ifs with hwho
    · exact hLocalNew
    · exact h.local _ who
  · intro who n' msg' tsnd' hmsg'
    exact h.messages who n' msg' tsnd'
      ((congrFun (messagesAt_recvSuccessor s party who r (msg.epoch - 1)) n').symm.trans hmsg')
  · intro who e
    rw [keysAt_recvSuccessor, stateAt_recvSuccessor]
    by_cases hwho : who = party
    · subst who
      rw [ite_eq_left rfl, ite_eq_left rfl, hnone, hcompEq]
      exact h.keys party e
    · rw [ite_eq_right hwho, ite_eq_right hwho]
      exact h.keys who e

omit [DecidableEq P.Sym] in
/-- The current game epoch after a receive. -/
private theorem tcurAt_recvSuccessor (s : MLKEMBraid.GameState P Unit) (party who : Bool)
    (r : RecvResult P Unit) (trcv : ℕ) :
    (recvSuccessor s party r trcv).tcurAt who =
      if who = party then max (s.tcurAt who) trcv else s.tcurAt who := by
  cases party <;> cases who <;> rfl

omit [DecidableEq P.Sym] in
/-- The repaired completion of epoch `e` keeps the control and pair invariants: the generator
advances from `ekSentCt1Received e` to `noHeaderReceived (e + 1)`, its peer is `ct2Sampled e`, and
its key table gains epoch `e`. -/
private theorem completion_control (h : RepairInv hMac T s) (party : Bool) {e : ℕ}
    {sk : P.SK} {ct1 : P.inc.C₁} {dec : DecoderState (P.inc.C₂ × P.Mac) P.Sym}
    (hst : s.stateAt party = .ekSentCt1Received e () sk ct1 dec) (key : P.EpochKey) :
    let s' := recvSuccessor s party
      ⟨e - 1, some (e, key), .noHeaderReceived (e + 1) () (DecoderState.empty P.ecpHdr)⟩ (e - 1)
    ControlInv s' ∧ StatePairInv s' := by
  intro s'
  obtain ⟨h1, h2, hpos, hposP, hcross, hcrossP, -⟩ := h.pairBounds _ party
  obtain ⟨b, enc, hpeer⟩ :=
    PairInv.peer_of_ekSentCt1Received h1 h2 hpos hposP hcross hcrossP hst
  have he0 : 0 < e := by rw [hst] at hpos; exact hpos
  have hC := h.control
  have hE := hC.epochKnowledge
  have hcompS : (s.stateAt party).completedEpoch = e - 1 := by rw [hst]; rfl
  have hepS : (s.stateAt party).epoch = e := by rw [hst]; rfl
  have hcompP : (s.stateAt (!party)).completedEpoch = e := by rw [hpeer]; rfl
  have hepP : (s.stateAt (!party)).epoch = e := by rw [hpeer]; rfl
  have hst' : s'.stateAt party = .noHeaderReceived (e + 1) () (DecoderState.empty P.ecpHdr) := by
    simp [s']
  have hpeer' : s'.stateAt (!party) = s.stateAt (!party) := by simp [s']
  have hkeys' : s'.keysAt party = Function.update (s.keysAt party) e (some key) := by simp [s']
  have hkeysP' : s'.keysAt (!party) = s.keysAt (!party) := by simp [s']
  have hmsgs' : ∀ who, s'.messagesAt who = s.messagesAt who := fun who => by simp [s']
  have htcur' : s'.tcurAt party = max (s.tcurAt party) (e - 1) := by
    simp [s', tcurAt_recvSuccessor]
  have htcurP' : s'.tcurAt (!party) = s.tcurAt (!party) := by
    simp [s', tcurAt_recvSuccessor]
  have hcomp' : (s'.stateAt party).completedEpoch = e := by rw [hst']; rfl
  have hep' : (s'.stateAt party).epoch = e + 1 := by rw [hst']; rfl
  have hRole : true = decide (e % 2 = if party then 1 else 0) := by
    have := hC.role party
    rwa [hst] at this
  have hpar : e % 2 = if party then 1 else 0 := of_decide_eq_true hRole.symm
  -- The key prefix of the generator grows by epoch `e`.
  have hK : KeyPrefixInv s' := by
    have hpos' : ∀ who, 0 < (s'.stateAt who).epoch := by
      intro who
      rcases Bool.eq_or_eq_not who party with rfl | rfl
      · rw [hep']; omega
      · rw [hpeer']; exact hE.keyPrefix.pos (!party)
    have hkeys : ∀ who t, s'.keysAt who t ≠ none ↔
        0 < t ∧ t ≤ (s'.stateAt who).completedEpoch := by
      intro who t
      rcases Bool.eq_or_eq_not who party with rfl | rfl
      · rw [hkeys', hcomp']
        have hold : ∀ t, s.keysAt who t ≠ none ↔ 0 < t ∧ t ≤ e - 1 := fun t => by
          rw [← hcompS]; exact hE.keyPrefix.keys who t
        have := SCKAScheme.update_succ_ne_none_iff hold key t
        rwa [Nat.sub_add_cancel he0] at this
      · rw [hkeysP', hpeer']
        exact hE.keyPrefix.keys (!party) t
    exact ⟨hpos' true, hpos' false, hkeys true, hkeys false⟩
  have hEK : EpochKnowledgeInv s' := by
    have hepLe : ∀ who, (s'.stateAt who).epoch ≤ (s'.stateAt (!who)).completedEpoch + 1 := by
      intro who
      rcases Bool.eq_or_eq_not who party with rfl | rfl
      · rw [hep', hpeer', hcompP]
      · rw [Bool.not_not, hpeer', hcomp', hepP]; omega
    have htcurLe : ∀ who, s'.tcurAt who ≤ (s'.stateAt who).completedEpoch := by
      intro who
      rcases Bool.eq_or_eq_not who party with rfl | rfl
      · rw [htcur', hcomp']
        have := hE.tcur_le who
        rw [hcompS] at this
        omega
      · rw [htcurP', hpeer']; exact hE.tcur_le (!party)
    have hmsgsLe : ∀ who n msg tsnd, s'.messagesAt who n = some (msg, tsnd) →
        msg.epoch ≤ (s'.stateAt who).completedEpoch + 1 ∧
          msg.epoch ≤ (s'.stateAt (!who)).completedEpoch + 1 ∧
          (msg.type = .ct2 → msg.epoch ≤ (s'.stateAt who).completedEpoch) := by
      intro who n msg tsnd hm
      rw [hmsgs'] at hm
      have hb := hE.msgs who n msg tsnd hm
      rcases Bool.eq_or_eq_not who party with rfl | rfl
      · rw [hcomp', hpeer', hcompP]
        rw [hcompS, hcompP] at hb
        omega
      · rw [Bool.not_not, hpeer', hcomp']
        rw [Bool.not_not, hcompP, hcompS] at hb
        omega
    exact ⟨hK, hepLe true, hepLe false, htcurLe true, htcurLe false, hmsgsLe true,
      hmsgsLe false⟩
  have hRR : RecordedReportInv s' := by
    have hrep : ∀ who n msg tsnd, s'.messagesAt who n = some (msg, tsnd) →
        tsnd = msg.epoch - 1 := by
      intro who n msg tsnd hm
      rw [hmsgs'] at hm
      exact hC.recordedReport.report who n msg tsnd hm
    exact ⟨hrep true, hrep false⟩
  have hTcur : ∀ who, s'.tcurAt who ≤ (s'.stateAt who).epoch - 1 := by
    intro who
    rcases Bool.eq_or_eq_not who party with rfl | rfl
    · rw [htcur', hep']
      have := hE.tcur_le who
      rw [hcompS] at this
      omega
    · rw [htcurP', hpeer']; exact hC.tcur_le_sub_one (!party)
  have hRoles : ∀ who, PartyControl who s' := by
    intro who
    rcases Bool.eq_or_eq_not who party with rfl | rfl
    · obtain ⟨-, -, hmsgOld⟩ := hC.roles who
      refine ⟨?_, ?_, ?_⟩
      · rw [hst']
        simp only [State.controlPosition, State.epoch]
        symm
        apply decide_eq_false
        cases who <;> simp at hpar ⊢ <;> omega
      · intro h'
        rw [hpeer', hepP, hep'] at h'
        omega
      · intro n msg tsnd hm
        rw [hmsgs'] at hm
        obtain ⟨hwf, hle, -, howner⟩ := hmsgOld n msg tsnd hm
        rw [hepS] at hle
        refine ⟨hwf, ?_, fun h' => absurd h' (by omega), howner⟩
        rw [hep']; omega
    · obtain ⟨hroleP, -, hmsgP⟩ := hC.roles (!party)
      refine ⟨?_, ?_, ?_⟩
      · rw [hpeer']; exact hroleP
      · intro _
        rw [hpeer', hpeer]
        rfl
      · intro n msg tsnd hm
        rw [hmsgs'] at hm
        rw [hpeer']
        exact hmsgP n msg tsnd hm
  have hPair : ∀ who, PairInv (s'.stateAt who) (s'.stateAt (!who)) := by
    intro who
    rcases Bool.eq_or_eq_not who party with rfl | rfl
    · rw [hst', hpeer', hpeer]
      simp [PairInv, State.epoch, State.controlPosition]
      omega
    · rw [Bool.not_not, hst', hpeer', hpeer]
      simp [PairInv, State.epoch, State.controlPosition]
  exact ⟨⟨hEK, hRR, hTcur true, hTcur false, hRoles⟩, ⟨hPair true, hPair false⟩⟩

omit [DecidableEq P.Sym] in
/-- The repaired completion of epoch `e` keeps the invariant for the same transcript: the
generator outputs the transcript's derived key of epoch `e`, whatever actual decapsulation gives. -/
private theorem completion [DecidableEq P.EpochKey] (h : RepairInv hMac T s) (party : Bool)
    {e : ℕ} {sk : P.SK} {ct1 : P.inc.C₁} {dec : DecoderState (P.inc.C₂ × P.Mac) P.Sym}
    (hst : s.stateAt party = .ekSentCt1Received e () sk ct1 dec)
    {es : P.inc.St} {k : P.K} (hc : (T e).encaps1 = some (es, ct1, k)) :
    RepairInv hMac T (recvUpdate s party (e - 1)
      ⟨e - 1, some (e, P.kdfOK k e), .noHeaderReceived (e + 1) () (DecoderState.empty P.ecpHdr)⟩
      (e - 1)) := by
  obtain ⟨h1, h2, hpos, hposP, hcross, hcrossP, -⟩ := h.pairBounds _ party
  obtain ⟨b, enc, hpeer⟩ :=
    PairInv.peer_of_ekSentCt1Received h1 h2 hpos hposP hcross hcrossP hst
  have he0 : 0 < e := by rw [hst] at hpos; exact hpos
  have hE := h.control.epochKnowledge
  have hcompS : (s.stateAt party).completedEpoch = e - 1 := by rw [hst]; rfl
  have hcompP : (s.stateAt (!party)).completedEpoch = e := by rw [hpeer]; rfl
  have hkeysS : ∀ t, s.keysAt party t = if 0 < t ∧ t ≤ e - 1 then
      (T t).encaps1.map (fun (_, _, key) => P.kdfOK key t) else none := by
    intro t; rw [← hcompS]; exact h.keys party t
  have hkeysP : ∀ t, s.keysAt (!party) t = if 0 < t ∧ t ≤ e then
      (T t).encaps1.map (fun (_, _, key) => P.kdfOK key t) else none := by
    intro t; rw [← hcompP]; exact h.keys (!party) t
  have hnone : s.keysAt party e = none := by rw [hkeysS, ite_eq_right (by omega)]
  have hpeerKey : s.keysAt (!party) e = some (P.kdfOK k e) := by
    rw [hkeysP, ite_eq_left ⟨he0, le_rfl⟩, hc]; rfl
  have hknown : SCKAScheme.knownPrefix (s.keysAt party) (max (s.tcurAt party) (e - 1)) = true := by
    apply SCKAScheme.knownPrefix_eq_true
    intro t ht hle
    have htcur := hE.tcur_le party
    rw [hcompS] at htcur
    exact (hE.keyPrefix.keys party t).2 ⟨ht, by rw [hcompS]; omega⟩
  have hzc : (recvUpdate s party (e - 1) ⟨e - 1, some (e, P.kdfOK k e),
      .noHeaderReceived (e + 1) () (DecoderState.empty P.ecpHdr)⟩ (e - 1)).correct = true := by
    rw [recvUpdate_correct]
    simp only [hnone, hpeerKey, h.correct, Bool.and_eq_true, beq_self_eq_true,
      Option.isNone_none, Option.isNone_some, Bool.false_or, and_self, true_and]
    exact SCKAScheme.knownPrefix_update_some hknown e _
  have hsucc := recvUpdate_eq_successor_of_correct s party (e - 1) _ (e - 1) h.correct hzc
  rw [hsucc] at hzc ⊢
  obtain ⟨hC', hP'⟩ := completion_control h party hst (P.kdfOK k e)
  refine h.of_le hzc hC' hP' ?_ ?_ ?_ ?_ ?_
  · intro who
    rw [stateAt_recvSuccessor]
    split_ifs with hwho
    · subst who; rw [hst]; simp [State.epoch]
    · exact le_rfl
  · intro who
    rw [stateAt_recvSuccessor]
    split_ifs with hwho
    · subst who; rw [hcompS]; simp [State.completedEpoch, State.epoch]
    · exact le_rfl
  · intro who
    rw [stateAt_recvSuccessor]
    split_ifs with hwho
    · refine ⟨Subsingleton.elim _ _, ?_⟩
      cases (T (e + 1)).keypair with
      | none => exact rfl
      | some kp => exact ⟨rfl, ∅, (ErasureCodePayload.payloadChunks_empty P.ecpHdr _).symm⟩
    · exact h.local _ who
  · intro who n' msg' tsnd' hmsg'
    exact h.messages who n' msg' tsnd'
      ((congrFun (messagesAt_recvSuccessor s party who _ (e - 1)) n').symm.trans hmsg')
  · intro who t
    rw [keysAt_recvSuccessor, stateAt_recvSuccessor]
    by_cases hwho : who = party
    · subst who
      rw [ite_eq_left rfl, ite_eq_left rfl]
      simp only [State.completedEpoch, State.epoch, Nat.add_sub_cancel]
      by_cases ht : t = e
      · subst t
        rw [Function.update_self, ite_eq_left ⟨he0, le_rfl⟩, hc]
        rfl
      · rw [Function.update_of_ne ht, hkeysS]
        by_cases h1 : 0 < t ∧ t ≤ e - 1
        · rw [ite_eq_left h1, ite_eq_left ⟨h1.1, by omega⟩]
        · rw [ite_eq_right h1, ite_eq_right (by omega)]
    · rw [ite_eq_right hwho, ite_eq_right hwho]
      exact h.keys who t

/-- Under the repaired invariant, and decapsulation agreement for the real receive, a recorded
message gets the same accepted result from the real and repaired receives, and the successor keeps
the invariant for the same transcript. -/
theorem recv_outcome [DecidableEq P.EpochKey]
    (hHdrCorrect : P.ecpHdr.ec.Correct) (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct) (hCt2Correct : P.ecpCt2.ec.Correct)
    (irl : P.kem.IncrementalRandLeak P.inc)
    (h : RepairInv hMac T s) (party : Bool) {n : ℕ} {msg : Message P.Sym} {tsnd : ℕ}
    (hmsg : s.messagesAt (!party) n = some (msg, tsnd))
    (repair : Bool) (hgood : repair = false → DecapsGood T) :
    ∃ key? st',
      repairedRecv P hMac repair T (s.stateAt party) msg = some (key?, msg.epoch - 1, st') ∧
      repairedRecv P hMac true T (s.stateAt party) msg = some (key?, msg.epoch - 1, st') ∧
      RepairInv hMac T (recvUpdate s party tsnd ⟨msg.epoch - 1, key?, st'⟩ (msg.epoch - 1)) := by
  rcases receive_cases hHdrCorrect hEkCorrect hCt1Correct hCt2Correct h party hmsg with
    ⟨e, sk, ct1, dec, chunk, pk, es, k, tag, hst, rfl, hkp, hc, hdecode⟩ |
      ⟨r, hr, hnone, hinv, hrep⟩
  · have hrep_true : repairedRecv P hMac true T (s.stateAt party) ⟨e, .ct2, some chunk⟩ =
        some (some (e, P.kdfOK k e), e - 1,
          .noHeaderReceived (e + 1) () (DecoderState.empty P.ecpHdr)) := by
      rw [hst]
      simp [repairedRecv, Message.wellFormed, hdecode, hc]
    have htsnd : tsnd = e - 1 := h.control.recordedReport.report (!party) n _ tsnd hmsg
    subst htsnd
    refine ⟨some (e, P.kdfOK k e), .noHeaderReceived (e + 1) () (DecoderState.empty P.ecpHdr),
      ?_, hrep_true, completion h party hst hc⟩
    cases repair
    · have hg := hgood rfl e pk sk es ct1 k hkp hc
      unfold decapsEpochKey at hg
      cases hdk : P.hDet.decapsDet sk (P.inc.splitC.symm (ct1,
          P.hEnc2.encaps2Det es (P.inc.toHeader pk) (P.inc.toVector pk))) with
      | none => rw [hdk] at hg; cases hg
      | some k' =>
          rw [hdk] at hg
          have hk' : P.kdfOK k' e = P.kdfOK k e := Option.some.inj hg
          rw [hst]
          simp [repairedRecv, MLKEMBraid.recvSCKA, receive, Message.wellFormed, hdecode, hdk,
            hk', auth]
    · exact hrep_true
  · have hscka : MLKEMBraid.recvSCKA P (auth P hMac) (s.stateAt party) msg =
        some (none, msg.epoch - 1, r.state) := by
      simp [MLKEMBraid.recvSCKA, hr, hnone]
    have hupd : recvUpdate s party tsnd ⟨msg.epoch - 1, none, r.state⟩ (msg.epoch - 1) =
        recvUpdate s party tsnd r (msg.epoch - 1) := by
      rcases r with ⟨re, rk, rs⟩
      simp only at hnone
      subst hnone
      rfl
    exact ⟨none, r.state, (hrep repair).trans hscka, (hrep true).trans hscka,
      hupd ▸ recvNoKey irl h party hmsg hr hnone hinv⟩

end Receive

variable [DecidableEq P.EpochKey] (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
  [DecidableEq P.Sym]

/-- The trace receive is the receive oracle of `recvScheme` on the game state. -/
theorem traceReceive_run (repair party : Bool) (n : ℕ) (s : TraceState P) :
    (traceReceive P hMac irl repair party n).run s =
      (liftGame (if party then
          SCKAScheme.oracleRecvA (recvScheme P hMac irl repair s.transcript) n
        else SCKAScheme.oracleRecvB (recvScheme P hMac irl repair s.transcript) n)).run s :=
  rfl

/-- Under the repaired invariant, and decapsulation agreement for the real receive, the real and
repaired trace receives are equal, keep the records and keep the invariant. -/
theorem traceReceive_outcome
    (hHdrCorrect : P.ecpHdr.ec.Correct) (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct) (hCt2Correct : P.ecpCt2.ec.Correct)
    (repair party : Bool) (n : ℕ) (s : TraceState P)
    (h : RepairInv hMac s.transcript s.game) (hgood : repair = false → DecapsGood s.transcript) :
    (traceReceive P hMac irl repair party n).run s = (traceReceive P hMac irl true party n).run s ∧
      ∀ z ∈ support ((traceReceive P hMac irl repair party n).run s),
        RepairInv hMac z.2.transcript z.2.game ∧ z.2.transcript = s.transcript ∧
          z.2.bad = s.bad := by
  cases hm : s.game.messagesAt (!party) n with
  | none =>
      have hpure : ∀ rep, (traceReceive P hMac irl rep party n).run s = pure (none, s) := by
        intro rep
        rw [traceReceive_run, liftGame_run]
        cases party
        · have hm' : s.game.msgA n = none := hm
          rw [ite_eq_right Bool.false_ne_true, SCKAScheme.oracleRecvB_run_eq_of_none _ _ hm',
            map_pure]
        · have hm' : s.game.msgB n = none := hm
          rw [ite_eq_left rfl, SCKAScheme.oracleRecvA_run_eq_of_none _ _ hm', map_pure]
      refine ⟨by rw [hpure, hpure], fun z hz => ?_⟩
      rw [hpure, mem_support_pure_iff] at hz
      subst hz
      exact ⟨h, rfl, rfl⟩
  | some entry =>
      obtain ⟨msg, tsnd⟩ := entry
      obtain ⟨key?, st', hrep, htrue, hinv⟩ :=
        recv_outcome hHdrCorrect hEkCorrect hCt1Correct hCt2Correct irl h party hm repair hgood
      have hacc : ∀ rep, repairedRecv P hMac rep s.transcript (s.game.stateAt party) msg =
          some (key?, msg.epoch - 1, st') →
          (traceReceive P hMac irl rep party n).run s =
            pure (some (msg.epoch - 1, key?.map Prod.fst),
              { s with game := (recvUpdate s.game party tsnd ⟨msg.epoch - 1, key?, st'⟩
                (msg.epoch - 1)) }) := by
        intro rep hr
        rw [traceReceive_run, liftGame_run]
        cases party
        · have hm' : s.game.msgA n = some (msg, tsnd) := hm
          rw [ite_eq_right Bool.false_ne_true,
            SCKAScheme.oracleRecvB_run_eq_of_accept (recvScheme P hMac irl rep s.transcript)
              s.game hm' hr, map_pure]
          rfl
        · have hm' : s.game.msgB n = some (msg, tsnd) := hm
          rw [ite_eq_left rfl,
            SCKAScheme.oracleRecvA_run_eq_of_accept (recvScheme P hMac irl rep s.transcript)
              s.game hm' hr, map_pure]
          rfl
      refine ⟨by rw [hacc repair hrep, hacc true htrue], fun z hz => ?_⟩
      rw [hacc repair hrep, mem_support_pure_iff] at hz
      subst hz
      exact ⟨hinv, rfl, rfl⟩

end MLKEMBraid.NoAuth
