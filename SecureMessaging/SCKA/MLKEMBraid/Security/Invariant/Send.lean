/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.Invariant.Basic
import SecureMessaging.SCKA.MLKEMBraid.Security.Sampling
import SecureMessaging.SCKA.MLKEMBraid.Correctness.SendPayload

/-!
# Sends preserve the repaired invariant

A send that generates a key pair or runs the first stage of encapsulation adds its sample to
the transcript. A send that samples nothing keeps the transcript and uses the facts of
`Correctness.SendPayload`. The repaired invariant holds after every send. Decapsulation agreement
holds after the send while the bad flag stays false.
-/

open OracleSpec OracleComp
open ErasureCodePayload.Streaming
open SCKAScheme.sckaCorrectnessSpec

namespace MLKEMBraid.NoAuth

variable {P : Parameters ProbComp}

namespace RepairInv

variable {hMac : P.Mac = Unit} {T : ℕ → EpochTranscript P} {s : MLKEMBraid.GameState P Unit}

/-- A send without sampling keeps the invariant for the same transcript. -/
private theorem sendSteady (h : RepairInv hMac T s) (party : Bool) {r : SendResult P Unit}
    (hr : r ∈ support (send P (auth P hMac) (s.stateAt party)))
    (hsteady : (s.stateAt party).SendsNoSample)
    (hCP : ControlInv (sendSuccessor s party r) ∧ StatePairInv (sendSuccessor s party r)) :
    RepairInv hMac T (sendSuccessor s party r) := by
  obtain ⟨hnone, hep, hcomp, hLocalNew, hMsgNew⟩ :=
    send_steady_step (auth P hMac) ((mem_support_send_iff (auth P hMac)).mp hr)
      hsteady (h.local party)
  refine h.of_le (by simpa only [correct_sendSuccessor] using h.correct) hCP.1 hCP.2
    (fun who => (epoch_stateAt_sendSuccessor s party who r hep).ge)
    (fun who => (completedEpoch_stateAt_sendSuccessor s party who r hcomp).ge) ?_ ?_ ?_
  · intro who
    simp only [stateAt_sendSuccessor]
    split_ifs with hwho
    · exact hLocalNew
    · exact h.local who
  · intro who
    rw [messagesAt_sendSuccessor]
    split_ifs with hwho
    · subst who
      apply (Function.forall_update_iff _
        (fun _ record => ∀ msg tsnd, record = some (msg, tsnd) →
          MessagePayloadInv (auth P hMac) () T msg)).2
      refine ⟨?_, fun n _ => h.messages party n⟩
      intro msg tsnd hmsg
      cases hmsg
      exact hMsgNew
    · exact h.messages who
  · intro who e
    rw [keysAt_sendSuccessor, completedEpoch_stateAt_sendSuccessor s party who r hcomp]
    simp only [hnone, ite_self]
    exact h.keys who e

/-- A key-generation send records its key pair. -/
private theorem sendKeygen (h : RepairInv hMac T s) (party : Bool) {e : ℕ} {a : Unit}
    (hst : s.stateAt party = .keysUnsampled e a) (pk : P.PK) (sk : P.SK)
    (hCP : ControlInv (sendSuccessor s party (keygenStep P hMac e a pk sk)) ∧
      StatePairInv (sendSuccessor s party (keygenStep P hMac e a pk sk))) :
    RepairInv hMac (Function.update T e { (T e) with keypair := some (pk, sk) })
      (sendSuccessor s party (keygenStep P hMac e a pk sk)) := by
  obtain ⟨b, dec, hpeer⟩ := h.peer_of_keysUnsampled party hst
  have hpos := h.control.epochKnowledge.keyPrefix.pos party
  rw [hst] at hpos
  simp only [State.epoch] at hpos
  have hLs := h.local party
  have hLp := h.local (!party)
  obtain ⟨hcorr, -, -, h0k, h0e, hKeypair, hEncaps, -, -, hMessages, hKeys⟩ := h
  rw [hst] at hLs
  rw [hpeer] at hLp
  simp only [LocalPayloadInv] at hLs
  obtain ⟨-, hkp0, hc0⟩ := hLs
  simp only [LocalPayloadInv, hkp0] at hLp
  obtain ⟨-, hdec⟩ := hLp
  subst hdec
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
  have hAuth : ∀ n, transcriptAuth (auth P hMac) ()
      (Function.update T e { (T e) with keypair := some (pk, sk) }) n =
      transcriptAuth (auth P hMac) () T n :=
    fun n => transcriptAuth_congr (auth P hMac) n (fun i _ => hTe i)
  have haT : a = transcriptAuth (auth P hMac) ()
      (Function.update T e { (T e) with keypair := some (pk, sk) }) (e - 1) :=
    Subsingleton.elim _ _
  have hKeyMono : ∀ n kp, (T n).keypair = some kp →
      (Function.update T e { (T e) with keypair := some (pk, sk) } n).keypair = some kp := by
    intro n kp h
    have hne : n ≠ e := by
      rintro rfl
      rw [hkp0] at h
      cases h
    rw [hTk n hne]
    exact h
  have hMsgOld : ∀ msg, MessagePayloadInv (auth P hMac) () T msg →
      MessagePayloadInv (auth P hMac) ()
        (Function.update T e { (T e) with keypair := some (pk, sk) }) msg := by
    intro msg h
    exact h.transport (auth P hMac) (hKeyMono msg.epoch)
      (fun _ hc => (hTe msg.epoch).trans hc) (hAuth (msg.epoch - 1))
      (fun _ _ => hAuth msg.epoch)
  have hep : ∀ who, (s.stateAt who).epoch = e := by
    intro who
    rcases Bool.eq_or_eq_not who party with rfl | rfl
    · rw [hst]; rfl
    · rw [hpeer]; rfl
  have hep' : ∀ who,
      ((sendSuccessor s party (keygenStep P hMac e a pk sk)).stateAt who).epoch =
        (s.stateAt who).epoch := fun who =>
    epoch_stateAt_sendSuccessor s party who _ (by rw [hst]; rfl)
  have hcomp' : ∀ who,
      ((sendSuccessor s party (keygenStep P hMac e a pk sk)).stateAt who).completedEpoch =
        (s.stateAt who).completedEpoch := fun who =>
    completedEpoch_stateAt_sendSuccessor s party who _ (by rw [hst]; rfl)
  have hLocal : ∀ who, LocalPayloadInv (auth P hMac) ()
      (Function.update T e { (T e) with keypair := some (pk, sk) })
        ((sendSuccessor s party (keygenStep P hMac e a pk sk)).stateAt who) := by
    intro who
    rcases Bool.eq_or_eq_not who party with rfl | rfl
    · simp only [stateAt_sendSuccessor, ↓reduceIte, keygenStep]
      exact ⟨haT, pk, hTke, rfl, rfl,
        congrArg (fun x => (P.inc.toHeader pk, (auth P hMac).macHeader x e (P.inc.toHeader pk)))
          haT⟩
    · simp only [stateAt_sendSuccessor, Bool.not_eq_self, ↓reduceIte]
      rw [hpeer]
      simp only [LocalPayloadInv, hTke]
      refine ⟨trivial, rfl, ∅, ?_⟩
      simp [DecoderState.empty]
  refine ⟨by simpa only [correct_sendSuccessor] using hcorr, hCP.1, hCP.2,
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
    obtain ⟨h0, hle, pk', sk', hkp'⟩ := hEncaps e' es ct1 key hc
    refine ⟨h0, ?_, pk', sk', by rw [hTk e' he]; exact hkp'⟩
    rw [← GameState.stateAt_encapsulator]
    rw [hcomp', GameState.stateAt_encapsulator]
    exact hle
  · intro who
    change ∀ n msg tsnd, (sendSuccessor s party (keygenStep P hMac e a pk sk)).messagesAt who n =
      some (msg, tsnd) → _
    rw [messagesAt_sendSuccessor]
    split_ifs with hwho
    · subst who
      apply (Function.forall_update_iff _
        (fun _ record => ∀ msg tsnd, record = some (msg, tsnd) →
          MessagePayloadInv (auth P hMac) ()
            (Function.update T e { (T e) with keypair := some (pk, sk) }) msg)).2
      refine ⟨?_, fun n _ msg tsnd hmsg =>
        hMsgOld msg (hMessages party n msg tsnd hmsg)⟩
      intro msg tsnd hmsg
      cases hmsg
      exact ⟨pk, sk, 0, hTke, congrArg (fun x => some (P.ecpHdr.encode
        (P.inc.toHeader pk, (auth P hMac).macHeader x e (P.inc.toHeader pk)) 0)) haT⟩
    · intro n msg tsnd hmsg
      exact hMsgOld msg (hMessages who n msg tsnd hmsg)
  · intro who e'
    change (sendSuccessor s party (keygenStep P hMac e a pk sk)).keysAt who e' = _
    rw [keysAt_sendSuccessor]
    simp only [keygenStep, ite_self]
    change s.keysAt who e' = if 0 < e' ∧
      e' ≤ ((sendSuccessor s party (keygenStep P hMac e a pk sk)).stateAt who).completedEpoch
      then _ else _
    rw [hcomp', hTe]
    exact hKeys who e'

/-- A first-stage encapsulation send records its sample and outputs the derived key, without
assuming actual decapsulation agreement. -/
private theorem sendEncaps1 (h : RepairInv hMac T s) (party : Bool) {e : ℕ} {a : Unit}
    {hdr : P.inc.PKheader} {dec : DecoderState P.inc.PKvector P.Sym}
    (hst : s.stateAt party = .headerReceived e a hdr dec)
    (es : P.inc.St) (ct1 : P.inc.C₁) (k : P.K)
    (hCP : ControlInv (sendSuccessor s party (encaps1Step P hMac e a hdr dec es ct1 k)) ∧
      StatePairInv (sendSuccessor s party (encaps1Step P hMac e a hdr dec es ct1 k))) :
    RepairInv hMac (Function.update T e { (T e) with encaps1 := some (es, ct1, k) })
      (sendSuccessor s party (encaps1Step P hMac e a hdr dec es ct1 k)) := by
  obtain ⟨pk, sk, b, enc, hkpT, hpeer, hhdr⟩ := h.peer_of_headerReceived party hst
  have hpos := h.control.epochKnowledge.keyPrefix.pos party
  rw [hst] at hpos
  simp only [State.epoch] at hpos
  have hRole := h.control.role party
  have hLs := h.local party
  have hLp := h.local (!party)
  obtain ⟨hcorr, hControl, -, h0k, h0e, hKeypair, hEncaps, -, -, hMessages, hKeys⟩ := h
  rw [hst] at hRole
  simp only [State.controlPosition, State.epoch] at hRole
  have hpar : ¬ e % 2 = if party then 1 else 0 := of_decide_eq_false hRole.symm
  rw [hst] at hLs
  rw [hpeer] at hLp
  simp only [LocalPayloadInv] at hLs hLp
  obtain ⟨-, hc0, _, _, -, -, hdec⟩ := hLs
  obtain ⟨-, pk', hkp', hvec, hecp, hpay⟩ := hLp
  subst hhdr hdec
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
  have hAuthLt : ∀ n, n < e → transcriptAuth (auth P hMac) ()
      (Function.update T e { (T e) with encaps1 := some (es, ct1, k) }) n =
      transcriptAuth (auth P hMac) () T n :=
    fun n hn => transcriptAuth_congr (auth P hMac) n (fun i hi => hTc i (by omega))
  have hMsgOld : ∀ msg : Message P.Sym, msg.epoch ≤ e →
      MessagePayloadInv (auth P hMac) () T msg →
      MessagePayloadInv (auth P hMac) ()
        (Function.update T e { (T e) with encaps1 := some (es, ct1, k) }) msg := by
    intro msg hle h
    have hlt : ∀ c, (T msg.epoch).encaps1 = some c → msg.epoch < e := by
      intro c hc
      have hne : msg.epoch ≠ e := by
        rintro he
        rw [he, hc0] at hc
        cases hc
      omega
    exact h.transport (auth P hMac) (fun _ hk => (hTk msg.epoch).trans hk)
      (fun c hc => (hTc msg.epoch (ne_of_lt (hlt c hc))).trans hc)
      (hAuthLt (msg.epoch - 1) (by omega)) (fun c hc => hAuthLt msg.epoch (hlt c hc))
  have hcomp : ∀ who, (s.stateAt who).completedEpoch = e - 1 := by
    intro who
    rcases Bool.eq_or_eq_not who party with rfl | rfl
    · rw [hst]; rfl
    · rw [hpeer]; rfl
  have hep' : ∀ who, ((sendSuccessor s party
      (encaps1Step P hMac e a (P.inc.toHeader pk) (DecoderState.empty P.ecpEk) es ct1 k)).stateAt
        who).epoch = (s.stateAt who).epoch := fun who =>
    epoch_stateAt_sendSuccessor s party who _ (by rw [hst]; rfl)
  have hcomp' : ∀ who, ((sendSuccessor s party
      (encaps1Step P hMac e a (P.inc.toHeader pk) (DecoderState.empty P.ecpEk) es ct1 k)).stateAt
        who).completedEpoch = if who = party then e else e - 1 := by
    intro who
    simp only [stateAt_sendSuccessor]
    split_ifs
    · rfl
    · exact hcomp who
  have hBnd : ∀ (who : Bool) n msg tsnd,
      s.messagesAt who n = some (msg, tsnd) → msg.epoch ≤ e := by
    intro who n msg tsnd h
    have h2 := ((hControl.roles who).2.2 n msg tsnd h).2.1
    have hepw : (s.stateAt who).epoch = e := by
      rcases Bool.eq_or_eq_not who party with rfl | rfl
      · rw [hst]; rfl
      · rw [hpeer]; rfl
    exact h2.trans_eq hepw
  have hempty : (DecoderState.empty P.ecpEk).chunks =
      ErasureCodePayload.payloadChunks P.ecpEk (P.inc.toVector pk) ∅ := by
    simp [DecoderState.empty]
  have hLocal : ∀ who, LocalPayloadInv (auth P hMac) ()
      (Function.update T e { (T e) with encaps1 := some (es, ct1, k) })
        ((sendSuccessor s party (encaps1Step P hMac e a (P.inc.toHeader pk)
          (DecoderState.empty P.ecpEk) es ct1 k)).stateAt who) := by
    intro who
    rcases Bool.eq_or_eq_not who party with rfl | rfl
    · simp only [stateAt_sendSuccessor, ↓reduceIte, encaps1Step]
      exact ⟨Subsingleton.elim _ _, pk, sk, k, by rw [hTk]; exact hkpT, hTce, rfl, ⟨rfl, rfl⟩,
        rfl, ∅, hempty⟩
    · simp only [stateAt_sendSuccessor, Bool.not_eq_self, ↓reduceIte]
      rw [hpeer]
      refine ⟨Subsingleton.elim _ _, pk', by rw [hTk]; exact hkp', hvec, hecp, ?_⟩
      rw [hAuthLt (e - 1) (by omega)]
      exact hpay
  have howner : decide (e % 2 = 1) = !party := by
    cases party
    · apply decide_eq_true
      simp only [Bool.false_eq_true, ↓reduceIte] at hpar
      omega
    · exact decide_eq_false hpar
  refine ⟨by simpa only [correct_sendSuccessor] using hcorr, hCP.1, hCP.2, ?_, ?_, ?_, ?_,
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
      refine ⟨hpos, ?_, pk, sk, by rw [hTk]; exact hkpT⟩
      rw [← GameState.stateAt_encapsulator]
      rw [hcomp', howner]
      simp
    · rw [hTc e' he] at hc'
      obtain ⟨h0, hle, pk'', sk'', hkp''⟩ := hEncaps e' es' ct1' key' hc'
      have hleOld : e' ≤ e - 1 := by
        rw [← GameState.stateAt_encapsulator] at hle
        rwa [hcomp] at hle
      refine ⟨h0, ?_, pk'', sk'', by rw [hTk]; exact hkp''⟩
      rw [← GameState.stateAt_encapsulator]
      rw [hcomp']; split_ifs <;> omega
  · intro who
    change ∀ n msg tsnd, (sendSuccessor s party (encaps1Step P hMac e a (P.inc.toHeader pk)
      (DecoderState.empty P.ecpEk) es ct1 k)).messagesAt who n = some (msg, tsnd) → _
    rw [messagesAt_sendSuccessor]
    split_ifs with hwho
    · subst who
      apply (Function.forall_update_iff _
        (fun _ record => ∀ msg tsnd, record = some (msg, tsnd) →
          MessagePayloadInv (auth P hMac) ()
            (Function.update T e { (T e) with encaps1 := some (es, ct1, k) }) msg)).2
      refine ⟨?_, fun n _ msg tsnd hmsg =>
        hMsgOld msg (hBnd party n msg tsnd hmsg) (hMessages party n msg tsnd hmsg)⟩
      intro msg tsnd hmsg
      cases hmsg
      exact ⟨es, ct1, k, 0, hTce, rfl⟩
    · intro n msg tsnd hmsg
      exact hMsgOld msg (hBnd who n msg tsnd hmsg) (hMessages who n msg tsnd hmsg)
  · intro who e'
    change (sendSuccessor s party (encaps1Step P hMac e a (P.inc.toHeader pk)
      (DecoderState.empty P.ecpEk) es ct1 k)).keysAt who e' = _
    rw [keysAt_sendSuccessor]
    change (if who = party then Function.update (s.keysAt who) e (some (P.kdfOK k e))
      else s.keysAt who) e' = if 0 < e' ∧ e' ≤ ((sendSuccessor s party (encaps1Step P hMac e a
        (P.inc.toHeader pk) (DecoderState.empty P.ecpEk) es ct1 k)).stateAt who).completedEpoch
        then _ else _
    rw [hcomp']
    have hK : s.keysAt who e' =
        if 0 < e' ∧ e' ≤ (s.stateAt who).completedEpoch then
          (T e').encaps1.map (fun (_, _, key) => P.kdfOK key e') else none := hKeys who e'
    rw [hcomp] at hK
    by_cases hwho : who = party
    · rw [ite_eq_left hwho, ite_eq_left hwho]
      by_cases he : e' = e
      · subst e'
        rw [Function.update_self, ite_eq_left ⟨hpos, le_rfl⟩, hTce]
        rfl
      · rw [Function.update_of_ne he, hK, hTc e' he]
        by_cases h1 : 0 < e' ∧ e' ≤ e - 1
        · rw [ite_eq_left h1, ite_eq_left ⟨h1.1, by omega⟩]
        · rw [ite_eq_right h1, ite_eq_right (by omega)]
    · rw [ite_eq_right hwho, ite_eq_right hwho, hK]
      by_cases he : e' = e
      · subst e'
        simp [show ¬ (0 < e ∧ e ≤ e - 1) by omega]
      · rw [hTc e' he]

end RepairInv

variable [DecidableEq P.EpochKey] (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)

/-- A committed trace send keeps the repaired invariant for its extended transcript, and keeps
decapsulation agreement whenever its bad flag stays false. -/
theorem traceSend_preserves (party leaking : Bool) (s : TraceState P)
    (h : RepairInv hMac s.transcript s.game)
    {z : Option (ℕ × Option ℕ × Message P.Sym × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      TraceState P}
    (hz : z ∈ support ((traceSend P hMac irl party leaking).run s)) :
    RepairInv hMac z.2.transcript z.2.game ∧
      (DecapsGood s.transcript → z.2.bad = false → DecapsGood z.2.transcript) := by
  classical
  rcases mem_support_traceSend hMac irl hz with hz | ⟨⟨⟨r, rand⟩, T', bad'⟩, hw, -, hz⟩
  · rw [hz]
    exact ⟨h, fun hg _ => hg⟩
  rw [hz]
  dsimp only
  have hCPgen : ∀ r', r' ∈ support (send P (auth P hMac) (s.game.stateAt party)) →
      ControlInv (sendUpdate s.game party r') ∧ StatePairInv (sendUpdate s.game party r') := by
    intro r' hr'
    cases party
    · exact correctnessImpl_preserves_controlInv_statePairInv (auth P hMac) irl (pure ())
        (OSendB (Rho := Message P.Sym)) s.game ⟨h.control, h.statePair⟩ _
        ((mem_support_oracleSend_run_iff (auth P hMac) irl (pure ()) s.game false _).2
          ⟨r', hr', rfl⟩)
    · exact correctnessImpl_preserves_controlInv_statePairInv (auth P hMac) irl (pure ())
        (OSendA (Rho := Message P.Sym)) s.game ⟨h.control, h.statePair⟩ _
        ((mem_support_oracleSend_run_iff (auth P hMac) irl (pure ()) s.game true _).2
          ⟨r', hr', rfl⟩)
  obtain ⟨htcur, hkeys⟩ := h.control.send_prefix party
  cases hst : s.game.stateAt party with
  | keysUnsampled e a =>
      rw [sampledSend_eq_keygen hMac irl s party hst, support_map] at hw
      obtain ⟨⟨⟨pk, sk⟩, rand₀⟩, hkr, heq⟩ := hw
      simp only [Prod.mk.injEq] at heq
      obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := heq
      have hkg : (pk, sk) ∈ support P.kem.keygen := by
        rw [keygen_eq_map irl, support_map]
        exact ⟨_, hkr, rfl⟩
      have hr : keygenStep P hMac e a pk sk ∈
          support (send P (auth P hMac) (s.game.stateAt party)) := by
        rw [hst, mem_support_send_iff]
        exact .keygen e a pk sk hkg
      rw [hst] at htcur hkeys
      simp only [State.epoch] at htcur hkeys
      have hflag : (sendUpdate s.game party (keygenStep P hMac e a pk sk)).correct = true := by
        rw [sendUpdate_correct]
        simp only [keygenStep, Bool.and_eq_true]
        exact ⟨⟨h.correct, decide_eq_true htcur⟩, SCKAScheme.knownPrefix_eq_true hkeys⟩
      have hsucc := sendUpdate_eq_successor_of_correct s.game party _ h.correct hflag
      have hCP := hCPgen _ hr
      rw [hsucc] at hCP ⊢
      refine ⟨(RepairInv.sendKeygen h party hst pk sk hCP).setFlags _ _, fun hg _ => ?_⟩
      have hc0 : (s.transcript e).encaps1 = none := by
        have hL := h.local party
        rw [hst] at hL
        exact hL.2.2
      intro e' pk' sk' es ct1 key hk hc
      by_cases he : e' = e
      · subst e'
        simp [Function.update_self, hc0] at hc
      · rw [Function.update_of_ne he] at hk hc
        exact hg e' pk' sk' es ct1 key hk hc
  | headerReceived e a hdr dec =>
      rw [sampledSend_eq_encaps1 hMac irl s party hst, support_map] at hw
      obtain ⟨⟨⟨es, ct1, k⟩, rand₀⟩, hkr, heq⟩ := hw
      simp only [Prod.mk.injEq] at heq
      obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := heq
      have hek : (es, ct1, k) ∈ support (P.inc.encaps1 hdr) := by
        rw [encaps1_eq_map irl, support_map]
        exact ⟨_, hkr, rfl⟩
      have hr : encaps1Step P hMac e a hdr dec es ct1 k ∈
          support (send P (auth P hMac) (s.game.stateAt party)) := by
        rw [hst, mem_support_send_iff]
        exact .encaps1 e a hdr dec es ct1 k hek
      obtain ⟨pk, sk, b, enc, hkpT, hpeer, hhdr⟩ := h.peer_of_headerReceived party hst
      rw [hst] at htcur hkeys
      simp only [State.epoch] at htcur hkeys
      have hnone : ∀ who, s.game.keysAt who e = none := by
        intro who
        have hprefix := h.control.epochKnowledge.keyPrefix.keys who e
        by_contra hne
        obtain ⟨hpos', hbound⟩ := hprefix.1 hne
        rcases Bool.eq_or_eq_not who party with rfl | rfl
        · rw [hst] at hbound
          simp only [State.completedEpoch, State.epoch] at hbound
          omega
        · rw [hpeer] at hbound
          simp only [State.completedEpoch, State.epoch] at hbound
          omega
      have hflag : (sendUpdate s.game party (encaps1Step P hMac e a hdr dec es ct1 k)).correct =
          true := by
        rw [sendUpdate_correct]
        simp only [encaps1Step, Bool.and_eq_true]
        exact ⟨⟨⟨⟨h.correct, decide_eq_true htcur⟩, by simp [hnone]⟩, by simp [hnone]⟩,
          SCKAScheme.knownPrefix_update_some (SCKAScheme.knownPrefix_eq_true hkeys) e _⟩
      have hsucc := sendUpdate_eq_successor_of_correct s.game party _ h.correct hflag
      have hCP := hCPgen _ hr
      rw [hsucc] at hCP ⊢
      refine ⟨(RepairInv.sendEncaps1 h party hst es ct1 k hCP).setFlags _ _, fun hg hbad => ?_⟩
      simp only [encaps1Bad, hkpT, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_not] at hbad
      obtain ⟨-, hdk⟩ := hbad
      intro e' pk' sk' es' ct1' key' hk hc
      by_cases he : e' = e
      · subst e'
        simp only [Function.update_self] at hk hc
        rw [hkpT] at hk
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hk)
        obtain ⟨rfl, rfl, rfl⟩ : es = es' ∧ ct1 = ct1' ∧ k = key' := by simpa using hc
        exact hdk
      · rw [Function.update_of_ne he] at hk hc
        exact hg e' pk' sk' es' ct1' key' hk hc
  | _ =>
      have hsteady : (s.game.stateAt party).SendsNoSample := by rw [hst]; trivial
      rw [sampledSend_of_noSample hMac irl s party (by simp [hst]) (by simp [hst]),
        support_map] at hw
      obtain ⟨out, hout, heq⟩ := hw
      simp only [Prod.mk.injEq] at heq
      obtain ⟨⟨hrEq, -⟩, hTEq, hBEq⟩ := heq
      rw [hrEq] at hout
      subst T'
      subst bad'
      have hr : r ∈ support (send P (auth P hMac) (s.game.stateAt party)) := hout
      have hedge := (mem_support_send_iff (auth P hMac)).mp hr
      have hkey : r.outputKey = none := hedge.outputKey_eq_none fun e a hdr dec h' => by
        rw [h'] at hsteady
        exact hsteady
      have hflag : (sendUpdate s.game party r).correct = true := by
        rw [sendUpdate_correct, hkey, hedge.sendingEpoch_eq]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨h.correct, htcur⟩, SCKAScheme.knownPrefix_eq_true hkeys⟩
      have hsucc := sendUpdate_eq_successor_of_correct s.game party _ h.correct hflag
      have hCP := hCPgen _ hr
      rw [hsucc] at hCP ⊢
      exact ⟨(RepairInv.sendSteady h party hr hsteady hCP).setFlags _ _, fun hg _ => hg⟩

end MLKEMBraid.NoAuth
