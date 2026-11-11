/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.MLKEMBraid.Security.Auth.Invariant.Send
public import SecureMessaging.SCKA.MLKEMBraid.Correctness.ReceiveInvariant

/-!
# Receives preserve the record-based invariant

A recorded message either advances a receive without an output key, or completes the decoder of
the second ciphertext component at the key generator. In the second case the repaired receive
outputs the recorded epoch key and installs the recorded authenticator value, whatever
decapsulation gives. The invariant `RepairInv` holds after both kinds of receive, for every table
and every mode.

At the real instance (empty table, real modes) with decapsulation agreement, the real receive and
the repaired receive are the same function on recorded messages: decapsulation gives the recorded
key, the schedule gives the recorded authenticator value, and the recorded tag verifies.
-/

@[expose] public section

open OracleSpec OracleComp
open ErasureCodePayload.Streaming

namespace MLKEMBraid.Auth

open Braid

variable {P : Parameters ProbComp} {Root MacKey : Type}

/-- Outside the generator's `ct₂` states, `repairedRecv` runs `recvSCKA`. -/
theorem repairedRecv_eq_of_not_ekSent {AS : Type}
    (view : RatchetedAuthenticator P.EpochKey P.EpochKey AS
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (repair : Bool) (T : ℕ → EpochRecord P AS) {st : State P AS} (msg : Message P.Sym)
    (hst : ∀ t a sk ct1 dec, st ≠ .ekSentCt1Received t a sk ct1 dec) :
    repairedRecv view repair T st msg = Braid.recvSCKA P view st msg := by
  cases repair
  · rfl
  · cases st <;> first | rfl | exact absurd rfl (hst _ _ _ _ _)

/-- The current game epoch of `who` after a receive by `party`. -/
theorem tcurAt_recvSuccessor {AS : Type} (s : GameState P AS) (party who : Bool)
    (r : RecvResult P AS) (trcv : ℕ) :
    (recvSuccessor s party r trcv).tcurAt who =
      if who = party then max (s.tcurAt who) trcv else s.tcurAt who := by
  cases party <;> cases who <;> rfl

/-- The game-state message bound needed by the known-prefix check of a receive. -/
theorem knownPrefix_recv [DecidableEq P.Mac] {irl : P.kem.IncrementalRandLeak P.inc}
    {S : ScheduledAuthenticator P Root MacKey} {tbl : Installed P irl (Root × MacKey)}
    {modes : Modes} {ik : P.EpochKey} {T : ℕ → EpochRecord P (Root × MacKey)}
    {s : GameState P (Root × MacKey)} (h : RepairInv S tbl modes ik T s) (party : Bool) {n : ℕ}
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

/-- Under `RepairInv`, a recorded message either completes the `ct₂` decoder of the generator's
epoch, or `receive` accepts it without an output key, keeps the local invariant, and
`repairedRecv` runs it unchanged. -/
theorem receive_cases [DecidableEq P.Mac] {irl : P.kem.IncrementalRandLeak P.inc}
    {S : ScheduledAuthenticator P Root MacKey} {tbl : Installed P irl (Root × MacKey)}
    {modes : Modes} {ik : P.EpochKey} {T : ℕ → EpochRecord P (Root × MacKey)}
    {s : GameState P (Root × MacKey)}
    (hHdrSound : P.decHdr.Sound P.ecpHdr) (hEkSound : P.decEk.Sound P.ecpEk)
    (hCt1Sound : P.decCt1.Sound P.ecpCt1) (hCt2Sound : P.decCt2.Sound P.ecpCt2)
    (h : RepairInv S tbl modes ik T s) (party : Bool) {n : ℕ} {msg : Message P.Sym} {tsnd : ℕ}
    (hmsg : s.messagesAt (!party) n = some (msg, tsnd)) :
    (∃ t a sk ct1 dec chunk pk es k tag,
      s.stateAt party = .ekSentCt1Received t a sk ct1 dec ∧
      msg = ⟨t, .ct2, some chunk⟩ ∧ (T t).keypair = some (pk, sk) ∧
      (T t).encaps1 = some (es, ct1, k) ∧
      P.decCt2.decodedPayload (P.decCt2.addChunk dec chunk) =
        some (P.hEnc2.encaps2Det es (P.inc.toHeader pk) (P.inc.toVector pk), tag)) ∨
    (∃ r, receive P S.toRatcheted (s.stateAt party) msg = .ok r ∧ r.outputKey = none ∧
      LocalPayloadInv (recorded S T) ik (EpochRecord.toTranscript ∘ T) r.state ∧
      ∀ repair, repairedRecv S.toRatcheted repair T (s.stateAt party) msg =
        Braid.recvSCKA P S.toRatcheted (s.stateAt party) msg) := by
  have hRole := h.control.role party
  have hLocal := h.local party
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
  have hconv : ∀ (st : State P (Root × MacKey)) (m : Message P.Sym),
      (∀ t a sk ct1 dec, st ≠ .ekSentCt1Received t a sk ct1 dec) →
      receive P (recorded S T) st m = receive P S.toRatcheted st m := by
    intro st m hne
    cases st <;> first | rfl | exact absurd rfl (hne _ _ _ _ _)
  obtain ⟨st, hst⟩ : ∃ st, s.stateAt party = st := ⟨_, rfl⟩
  rw [hst] at hLocal hF ⊢
  have hplain : ∀ r, receive P (recorded S T) st msg = .ok r → r.outputKey = none →
      LocalPayloadInv (recorded S T) ik (EpochRecord.toTranscript ∘ T) r.state →
      (∀ t a sk ct1 dec, st ≠ .ekSentCt1Received t a sk ct1 dec) →
      ∃ r, receive P S.toRatcheted st msg = .ok r ∧ r.outputKey = none ∧
        LocalPayloadInv (recorded S T) ik (EpochRecord.toTranscript ∘ T) r.state ∧
        ∀ repair, repairedRecv S.toRatcheted repair T st msg =
          Braid.recvSCKA P S.toRatcheted st msg :=
    fun r hr hnone hinv hne =>
      ⟨r, (hconv st msg hne).symm.trans hr, hnone, hinv,
        fun repair => repairedRecv_eq_of_not_ekSent S.toRatcheted repair T msg hne⟩
  cases st
  case keysUnsampled e a =>
    have hsame : receive P S.toRatcheted (.keysUnsampled e a) msg =
        .ok ⟨e - 1, none, .keysUnsampled e a⟩ := by
      rcases msg with ⟨me, mt, md⟩
      cases mt <;> cases md <;> rfl
    exact Or.inr ⟨_, hsame, rfl, hLocal, fun repair =>
      repairedRecv_eq_of_not_ekSent S.toRatcheted repair T msg (by intros; simp)⟩
  case keysSampled e a sk vec enc =>
    obtain ⟨r, hr, hnone, hinv⟩ :=
      receive_keysSampled_payload (recorded S T) ik (EpochRecord.toTranscript ∘ T) e a sk vec enc
        msg hLocal hPayload
    exact Or.inr (hplain r hr hnone hinv (by intros; simp))
  case headerSent e a sk dec enc =>
    obtain ⟨r, hr, hnone, hinv⟩ := receive_headerSent_payload (recorded S T) hCt1Sound ik
      (EpochRecord.toTranscript ∘ T) e a sk dec enc msg hLocal hPayload
    exact Or.inr (hplain r hr hnone hinv (by intros; simp))
  case ct1Received e a sk ct1 enc =>
    obtain ⟨r, hr, hnone, hinv⟩ :=
      receive_ct1Received_payload (recorded S T) ik (EpochRecord.toTranscript ∘ T) e a sk ct1 enc
        msg hLocal hPayload
    exact Or.inr (hplain r hr hnone hinv (by intros; simp))
  case ekSentCt1Received e a sk ct1 dec =>
    have hold := hLocal
    obtain ⟨ha, pk, es, key, hkp, hc, hdec⟩ := hLocal
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
              have hC := hCt2Sound.received_addChunk hdec i
              rw [← hch] at hC
              obtain ⟨hhon, hnone | hsome⟩ := hC
              · refine Or.inr ⟨⟨e - 1, none,
                    .ekSentCt1Received e a sk ct1 (P.decCt2.addChunk dec chunk)⟩,
                  by simp [receive, Message.wellFormed, hnone], rfl,
                  ⟨ha, pk, es, key, hkp, hc, hhon⟩, fun repair => ?_⟩
                cases repair
                · rfl
                · simp [repairedRecv, Message.wellFormed, hnone]
              · exact Or.inl ⟨e, a, sk, ct1, dec, chunk, pk, es, key, _, rfl, rfl, hkp, hc, hsome⟩
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
    have hNoEncaps : ((EpochRecord.toTranscript ∘ T) e).encaps1 = none := by
      cases hce : (T e).encaps1 with
      | none => exact hce
      | some c =>
          obtain ⟨hpos, hle, -⟩ := h.encaps e c.1 c.2.1 c.2.2 hce
          rw [(hF rfl e rfl).1] at hle
          have hcomp : (State.noHeaderReceived e a dec : State P (Root × MacKey)).completedEpoch =
              e - 1 := rfl
          omega
    obtain ⟨r, hr, hnone, hinv⟩ := receive_noHeaderReceived_payload (recorded S T) ik
      (EpochRecord.toTranscript ∘ T) hHdrSound e a dec msg hLocal hPayload hNoEncaps
    exact Or.inr (hplain r hr hnone hinv (by intros; simp))
  case headerReceived e a hdr dec =>
    exact Or.inr ⟨⟨e - 1, none, .headerReceived e a hdr dec⟩, by simp [receive, State.epoch],
      rfl, hLocal, fun repair =>
        repairedRecv_eq_of_not_ekSent S.toRatcheted repair T msg (by intros; simp)⟩
  case ct1Sampled e a hdr encapsState ct1 enc dec =>
    obtain ⟨r, hr, hnone, hinv⟩ := receive_ct1Sampled_payload (recorded S T) ik
      (EpochRecord.toTranscript ∘ T) hEkSound e a hdr encapsState ct1 enc dec msg hLocal hPayload
    exact Or.inr (hplain r hr hnone hinv (by intros; simp))
  case ekReceivedCt1Sampled e a encapsState ct1 hdr vec enc =>
    obtain ⟨r, hr, hnone, hinv⟩ := receive_ekReceivedCt1Sampled_payload (recorded S T) ik
      (EpochRecord.toTranscript ∘ T) e a encapsState ct1 hdr vec enc msg hLocal
    exact Or.inr (hplain r hr hnone hinv (by intros; simp))
  case ct1Acknowledged e a hdr encapsState ct1 dec =>
    obtain ⟨r, hr, hnone, hinv⟩ := receive_ct1Acknowledged_payload (recorded S T) ik
      (EpochRecord.toTranscript ∘ T) hEkSound e a hdr encapsState ct1 dec msg hLocal hPayload
    exact Or.inr (hplain r hr hnone hinv (by intros; simp))
  case ct2Sampled e a enc =>
    have hkp : (T (e + 1)).keypair = none := by
      cases hk : (T (e + 1)).keypair with
      | none => rfl
      | some kp =>
          obtain ⟨-, hle⟩ := h.keypair (e + 1) kp.1 kp.2 hk
          rw [(hF rfl e rfl).2] at hle
          have hep : (State.ct2Sampled e a enc : State P (Root × MacKey)).epoch = e := rfl
          omega
    have hce : (T (e + 1)).encaps1 = none := by
      cases hc : (T (e + 1)).encaps1 with
      | none => rfl
      | some c =>
          obtain ⟨-, -, pk, sk, hkp'⟩ := h.encaps (e + 1) c.1 c.2.1 c.2.2 hc
          rw [hkp] at hkp'
          cases hkp'
    obtain ⟨r, hr, hnone, hinv⟩ :=
      receive_ct2Sampled_payload (recorded S T) ik (EpochRecord.toTranscript ∘ T) e a enc msg
        hLocal ⟨hkp, hce⟩
    exact Or.inr (hplain r hr hnone hinv (by intros; simp))

/-- An accepted receive without output key keeps the invariant for the same records. -/
theorem recvNoKey_preserves [DecidableEq P.Mac] [DecidableEq P.EpochKey]
    {irl : P.kem.IncrementalRandLeak P.inc} {S : ScheduledAuthenticator P Root MacKey}
    {tbl : Installed P irl (Root × MacKey)} {modes : Modes} {ik : P.EpochKey}
    {T : ℕ → EpochRecord P (Root × MacKey)} {s : GameState P (Root × MacKey)}
    (h : RepairInv S tbl modes ik T s) (party : Bool) {n : ℕ} {msg : Message P.Sym} {tsnd : ℕ}
    (hmsg : s.messagesAt (!party) n = some (msg, tsnd))
    {r : RecvResult P (Root × MacKey)} (hr : receive P S.toRatcheted (s.stateAt party) msg = .ok r)
    (hnone : r.outputKey = none)
    (hLocalNew : LocalPayloadInv (recorded S T) ik (EpochRecord.toTranscript ∘ T) r.state) :
    RepairInv S tbl modes ik T (recvUpdate s party tsnd r (msg.epoch - 1)) := by
  have hrep := h.control.recordedReport.report (!party) n msg tsnd hmsg
  have hzc : (recvUpdate s party tsnd r (msg.epoch - 1)).correct = true := by
    rw [recvUpdate_correct, hnone]
    simp only [Bool.and_eq_true]
    exact ⟨⟨h.correct, by simp [hrep]⟩, knownPrefix_recv h party hmsg⟩
  have hCP : ControlInv (recvUpdate s party tsnd r (msg.epoch - 1)) ∧
      StatePairInv (recvUpdate s party tsnd r (msg.epoch - 1)) := by
    have hsupp : (some (msg.epoch - 1, r.outputKey.map Prod.fst),
        recvUpdate s party tsnd r (msg.epoch - 1)) ∈
        support ((oracleRecv S.toRatcheted irl (pure ik) party n).run s) := by
      cases party
      · rw [oracleRecv, ite_eq_right Bool.false_ne_true,
          oracleRecvB_run_eq_of_ok S.toRatcheted irl (pure ik) hmsg hr]
        simp [recvUpdate]
      · rw [oracleRecv, ite_eq_left rfl,
          oracleRecvA_run_eq_of_ok S.toRatcheted irl (pure ik) hmsg hr]
        simp [recvUpdate]
    cases party
    · exact correctnessImpl_preserves_controlInv_statePairInv S.toRatcheted irl (pure ik)
        (SCKAScheme.sckaCorrectnessSpec.ORecvB (Rho := Message P.Sym) n) s
        ⟨h.control, h.statePair⟩ _ hsupp
    · exact correctnessImpl_preserves_controlInv_statePairInv S.toRatcheted irl (pure ik)
        (SCKAScheme.sckaCorrectnessSpec.ORecvA (Rho := Message P.Sym) n) s
        ⟨h.control, h.statePair⟩ _ hsupp
  have hsucc := recvUpdate_eq_successor_of_correct s party tsnd r (msg.epoch - 1) h.correct hzc
  rw [hsucc] at hzc hCP ⊢
  have hedge := ReceiveEdge.of_eq_ok S.toRatcheted hr
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
    · exact h.local who
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

/-- Completing epoch `t` at the generator keeps the control and state-pair invariants: the
generator advances from `ekSentCt1Received t` to `noHeaderReceived (t + 1)`, its peer is
`ct2Sampled t`, and its key table gains epoch `t`. -/
theorem completion_control [DecidableEq P.Mac]
    {irl : P.kem.IncrementalRandLeak P.inc} {S : ScheduledAuthenticator P Root MacKey}
    {tbl : Installed P irl (Root × MacKey)} {modes : Modes} {ik : P.EpochKey}
    {T : ℕ → EpochRecord P (Root × MacKey)} {s : GameState P (Root × MacKey)}
    (h : RepairInv S tbl modes ik T s) (party : Bool) {t : ℕ} {a : Root × MacKey}
    {sk : P.SK} {ct1 : P.inc.C₁} {dec : P.decCt2.D}
    (hst : s.stateAt party = .ekSentCt1Received t a sk ct1 dec)
    (key : P.EpochKey) (p : Root × MacKey) :
    let s' := recvSuccessor s party
      ⟨t - 1, some (t, key), .noHeaderReceived (t + 1) p P.decHdr.empty⟩ (t - 1)
    ControlInv s' ∧ StatePairInv s' := by
  intro s'
  obtain ⟨h1, h2, hpos, hposP, hcross, hcrossP, -⟩ := h.pairBounds party
  obtain ⟨b, enc, hpeer⟩ :=
    PairInv.peer_of_ekSentCt1Received h1 h2 hpos hposP hcross hcrossP hst
  have he0 : 0 < t := by rw [hst] at hpos; exact hpos
  have hC := h.control
  have hE := hC.epochKnowledge
  have hcompS : (s.stateAt party).completedEpoch = t - 1 := by rw [hst]; rfl
  have hepS : (s.stateAt party).epoch = t := by rw [hst]; rfl
  have hcompP : (s.stateAt (!party)).completedEpoch = t := by rw [hpeer]; rfl
  have hepP : (s.stateAt (!party)).epoch = t := by rw [hpeer]; rfl
  have hst' : s'.stateAt party = .noHeaderReceived (t + 1) p P.decHdr.empty := by
    simp [s']
  have hpeer' : s'.stateAt (!party) = s.stateAt (!party) := by simp [s']
  have hkeys' : s'.keysAt party = Function.update (s.keysAt party) t (some key) := by simp [s']
  have hkeysP' : s'.keysAt (!party) = s.keysAt (!party) := by simp [s']
  have hmsgs' : ∀ who, s'.messagesAt who = s.messagesAt who := fun who => by simp [s']
  have htcur' : s'.tcurAt party = max (s.tcurAt party) (t - 1) := by
    simp [s', tcurAt_recvSuccessor]
  have htcurP' : s'.tcurAt (!party) = s.tcurAt (!party) := by
    simp [s', tcurAt_recvSuccessor]
  have hcomp' : (s'.stateAt party).completedEpoch = t := by rw [hst']; rfl
  have hep' : (s'.stateAt party).epoch = t + 1 := by rw [hst']; rfl
  have hRole : true = decide (t % 2 = if party then 1 else 0) := by
    have := hC.role party
    rwa [hst] at this
  have hpar : t % 2 = if party then 1 else 0 := of_decide_eq_true hRole.symm
  have hK : KeyPrefixInv s' := by
    have hpos' : ∀ who, 0 < (s'.stateAt who).epoch := by
      intro who
      rcases Bool.eq_or_eq_not who party with rfl | rfl
      · rw [hep']; omega
      · rw [hpeer']; exact hE.keyPrefix.pos (!party)
    have hkeys : ∀ who u, s'.keysAt who u ≠ none ↔
        0 < u ∧ u ≤ (s'.stateAt who).completedEpoch := by
      intro who u
      rcases Bool.eq_or_eq_not who party with rfl | rfl
      · rw [hkeys', hcomp']
        have hold : ∀ u, s.keysAt who u ≠ none ↔ 0 < u ∧ u ≤ t - 1 := fun u => by
          rw [← hcompS]; exact hE.keyPrefix.keys who u
        have := SCKAScheme.update_succ_ne_none_iff hold key u
        rwa [Nat.sub_add_cancel he0] at this
      · rw [hkeysP', hpeer']
        exact hE.keyPrefix.keys (!party) u
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

/-- Completing epoch `t` at the generator with the recorded epoch key and authenticator value keeps
the invariant for the same records. -/
theorem repairedRecv_preserves [DecidableEq P.Mac] [DecidableEq P.EpochKey]
    {irl : P.kem.IncrementalRandLeak P.inc} {S : ScheduledAuthenticator P Root MacKey}
    {tbl : Installed P irl (Root × MacKey)} {modes : Modes} {ik : P.EpochKey}
    {T : ℕ → EpochRecord P (Root × MacKey)} {s : GameState P (Root × MacKey)}
    (h : RepairInv S tbl modes ik T s) (party : Bool) {t : ℕ} {a : Root × MacKey}
    {sk : P.SK} {ct1 : P.inc.C₁} {dec : P.decCt2.D}
    (hst : s.stateAt party = .ekSentCt1Received t a sk ct1 dec)
    {es : P.inc.St} {k : P.K} (hc : (T t).encaps1 = some (es, ct1, k))
    {x : P.EpochKey} (hk : (T t).key = some x) {p : Root × MacKey} (hp : (T t).pair = some p) :
    RepairInv S tbl modes ik T (recvUpdate s party (t - 1)
      ⟨t - 1, some (t, x), .noHeaderReceived (t + 1) p P.decHdr.empty⟩ (t - 1)) := by
  obtain ⟨h1, h2, hpos, hposP, hcross, hcrossP, -⟩ := h.pairBounds party
  obtain ⟨b, enc, hpeer⟩ :=
    PairInv.peer_of_ekSentCt1Received h1 h2 hpos hposP hcross hcrossP hst
  have he0 : 0 < t := by rw [hst] at hpos; exact hpos
  have hE := h.control.epochKnowledge
  have hcompS : (s.stateAt party).completedEpoch = t - 1 := by rw [hst]; rfl
  have hcompP : (s.stateAt (!party)).completedEpoch = t := by rw [hpeer]; rfl
  have hkeysS : ∀ u, s.keysAt party u = if 0 < u ∧ u ≤ t - 1 then (T u).key else none := by
    intro u; rw [← hcompS]; exact h.keys party u
  have hkeysP : ∀ u, s.keysAt (!party) u = if 0 < u ∧ u ≤ t then (T u).key else none := by
    intro u; rw [← hcompP]; exact h.keys (!party) u
  have hnone : s.keysAt party t = none := by rw [hkeysS, ite_eq_right (by omega)]
  have hpeerKey : s.keysAt (!party) t = some x := by
    rw [hkeysP, ite_eq_left ⟨he0, le_rfl⟩, hk]
  have hknown : SCKAScheme.knownPrefix (s.keysAt party) (max (s.tcurAt party) (t - 1)) = true := by
    apply SCKAScheme.knownPrefix_eq_true
    intro u hu hle
    have htcur := hE.tcur_le party
    rw [hcompS] at htcur
    exact (hE.keyPrefix.keys party u).2 ⟨hu, by rw [hcompS]; omega⟩
  have hzc : (recvUpdate s party (t - 1) ⟨t - 1, some (t, x),
      .noHeaderReceived (t + 1) p P.decHdr.empty⟩ (t - 1)).correct = true := by
    rw [recvUpdate_correct]
    simp only [hnone, hpeerKey, h.correct, Bool.and_eq_true, beq_self_eq_true,
      Option.isNone_none, Option.isNone_some, Bool.false_or, and_self, true_and]
    exact SCKAScheme.knownPrefix_update_some hknown t _
  have hsucc := recvUpdate_eq_successor_of_correct s party (t - 1) _ (t - 1) h.correct hzc
  rw [hsucc] at hzc ⊢
  obtain ⟨hC', hP'⟩ := completion_control h party hst x p
  have hSome : (T t).encaps1.isSome := by simp [hc]
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
    · refine ⟨(transcriptAuth_recorded S T ik hp (Or.inr hSome)).symm, ?_⟩
      cases hkp : ((EpochRecord.toTranscript ∘ T) (t + 1)).keypair with
      | none => exact rfl
      | some kp => exact P.decHdr.received_empty P.ecpHdr _
    · exact h.local who
  · intro who n' msg' tsnd' hmsg'
    exact h.messages who n' msg' tsnd'
      ((congrFun (messagesAt_recvSuccessor s party who _ (t - 1)) n').symm.trans hmsg')
  · intro who u
    rw [keysAt_recvSuccessor, stateAt_recvSuccessor]
    by_cases hwho : who = party
    · subst who
      rw [ite_eq_left rfl, ite_eq_left rfl]
      simp only [State.completedEpoch, State.epoch, Nat.add_sub_cancel]
      by_cases hu : u = t
      · subst u
        rw [Function.update_self, ite_eq_left ⟨he0, le_rfl⟩, hk]
      · rw [Function.update_of_ne hu, hkeysS]
        by_cases h1 : 0 < u ∧ u ≤ t - 1
        · rw [ite_eq_left h1, ite_eq_left ⟨h1.1, by omega⟩]
        · rw [ite_eq_right h1, ite_eq_right (by omega)]
    · rw [ite_eq_right hwho, ite_eq_right hwho]
      exact h.keys who u

/-- Under `RepairInv`, a recorded message gets an accepted result from the repaired receive, and the
successor keeps the invariant for the same records. -/
theorem recv_outcome [DecidableEq P.Mac] [DecidableEq P.EpochKey]
    {irl : P.kem.IncrementalRandLeak P.inc} {S : ScheduledAuthenticator P Root MacKey}
    {tbl : Installed P irl (Root × MacKey)} {modes : Modes} {ik : P.EpochKey}
    {T : ℕ → EpochRecord P (Root × MacKey)} {s : GameState P (Root × MacKey)}
    (hHdrSound : P.decHdr.Sound P.ecpHdr) (hEkSound : P.decEk.Sound P.ecpEk)
    (hCt1Sound : P.decCt1.Sound P.ecpCt1) (hCt2Sound : P.decCt2.Sound P.ecpCt2)
    (h : RepairInv S tbl modes ik T s) (party : Bool) {n : ℕ} {msg : Message P.Sym} {tsnd : ℕ}
    (hmsg : s.messagesAt (!party) n = some (msg, tsnd)) :
    ∃ key? st', repairedRecv S.toRatcheted true T (s.stateAt party) msg =
        some (key?, msg.epoch - 1, st') ∧
      RepairInv S tbl modes ik T (recvUpdate s party tsnd ⟨msg.epoch - 1, key?, st'⟩
        (msg.epoch - 1)) := by
  rcases receive_cases hHdrSound hEkSound hCt1Sound hCt2Sound h party hmsg with
    ⟨t, a, sk, ct1, dec, chunk, pk, es, k, tag, hst, rfl, hkp, hc, hdecode⟩ |
      ⟨r, hr, hnone, hinv, hrep⟩
  · have he0 : 0 < t := (h.encaps t es ct1 k hc).1
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp ((h.key_some t).2 (by simp [hc]))
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp ((h.pair_some t he0).2 (by simp [hc]))
    have hrep_true : repairedRecv S.toRatcheted true T (s.stateAt party) ⟨t, .ct2, some chunk⟩ =
        some (some (t, x), t - 1, .noHeaderReceived (t + 1) p P.decHdr.empty) := by
      rw [hst]
      simp [repairedRecv, Message.wellFormed, hdecode, hx, hp]
    have htsnd : tsnd = t - 1 := h.control.recordedReport.report (!party) n _ tsnd hmsg
    subst htsnd
    exact ⟨some (t, x), .noHeaderReceived (t + 1) p P.decHdr.empty, hrep_true,
      repairedRecv_preserves h party hst hc hx hp⟩
  · have hscka : Braid.recvSCKA P S.toRatcheted (s.stateAt party) msg =
        some (none, msg.epoch - 1, r.state) := by
      simp [Braid.recvSCKA, hr, hnone]
    have hupd : recvUpdate s party tsnd ⟨msg.epoch - 1, none, r.state⟩ (msg.epoch - 1) =
        recvUpdate s party tsnd r (msg.epoch - 1) := by
      rcases r with ⟨re, rk, rs⟩
      simp only at hnone
      subst hnone
      rfl
    exact ⟨none, r.state, (hrep true).trans hscka,
      hupd ▸ recvNoKey_preserves h party hmsg hr hnone hinv⟩

/-- At the real instance, with decapsulation agreement, the real receive and the repaired receive
are the same on a recorded message. -/
theorem recv_outcome_real [DecidableEq P.Mac]
    {irl : P.kem.IncrementalRandLeak P.inc} {S : ScheduledAuthenticator P Root MacKey}
    {ik : P.EpochKey} {T : ℕ → EpochRecord P (Root × MacKey)} {s : GameState P (Root × MacKey)}
    (hHdrSound : P.decHdr.Sound P.ecpHdr) (hEkSound : P.decEk.Sound P.ecpEk)
    (hCt1Sound : P.decCt1.Sound P.ecpCt1) (hCt2Sound : P.decCt2.Sound P.ecpCt2)
    (h : RepairInv S (Installed.empty (irl := irl)) Modes.real ik T s)
    (hgood : Braid.NoAuth.DecapsGood (EpochRecord.toTranscript ∘ T)) (party : Bool) {n : ℕ}
    {msg : Message P.Sym} {tsnd : ℕ} (hmsg : s.messagesAt (!party) n = some (msg, tsnd)) :
    repairedRecv S.toRatcheted false T (s.stateAt party) msg =
      repairedRecv S.toRatcheted true T (s.stateAt party) msg := by
  rcases receive_cases hHdrSound hEkSound hCt1Sound hCt2Sound h party hmsg with
    ⟨t, a, sk, ct1, dec, chunk, pk, es, k, tag, hst, rfl, hkp, hc, hdecode⟩ |
      ⟨r, hr, hnone, hinv, hrep⟩
  · have hLocal := h.local party
    rw [hst] at hLocal
    obtain ⟨ha, pk₁, es₁, key₁, hkp₁, hc₁, hdec⟩ := hLocal
    have hPayload := h.messages (!party) n _ tsnd hmsg
    simp only [MessagePayloadInv] at hPayload
    obtain ⟨pk₂, sk₂, es₂, ct1₂, key₂, i, hkp₂, hc₂, hchunk⟩ := hPayload
    obtain rfl : pk = pk₁ := by simpa using hkp.symm.trans hkp₁
    obtain ⟨rfl, rfl⟩ : es = es₁ ∧ k = key₁ := by simpa using hc.symm.trans hc₁
    obtain ⟨rfl, rfl⟩ : pk = pk₂ ∧ sk = sk₂ := by simpa using hkp.symm.trans hkp₂
    obtain ⟨rfl, rfl, rfl⟩ : es = es₂ ∧ ct1 = ct1₂ ∧ k = key₂ := by
      simpa using hc.symm.trans hc₂
    have hC := hCt2Sound.received_addChunk hdec i
    rw [← Option.some.inj hchunk] at hC
    obtain ⟨-, hnone | hsome⟩ := hC
    · rw [hnone] at hdecode
      cases hdecode
    · have htag := (Prod.mk.inj (Option.some.inj (hdecode.symm.trans hsome))).2
      have he0 : 0 < t := (h.encaps t es ct1 k hc).1
      have hSome : (T t).encaps1.isSome := by simp [hc]
      have hx := h.keyReal t es ct1 k hc rfl rfl
      have hp := h.pairReal t (P.kdfOK k t) he0 hSome hx rfl rfl
      have hauth := transcriptAuth_recorded S T ik hp (Or.inr hSome)
      have hg := hgood t pk sk es ct1 k hkp hc
      unfold decapsEpochKey at hg
      cases hdk : P.hDet.decapsDet sk (P.inc.splitC.symm (ct1,
          P.hEnc2.encaps2Det es (P.inc.toHeader pk) (P.inc.toVector pk))) with
      | none => rw [hdk] at hg; cases hg
      | some k' =>
          rw [hdk] at hg
          have hk' : P.kdfOK k' t = P.kdfOK k t := Option.some.inj hg
          have hmac : ∀ (x : Root × MacKey) e c,
              (recorded S T).macCiphertext x e c = S.macCiphertext x.2 e c := fun _ _ _ => rfl
          subst ha
          rw [hst]
          simp [repairedRecv, Braid.recvSCKA, receive, Message.wellFormed, hdecode, hdk,
            hk', hx, hp, ScheduledAuthenticator.toRatcheted, htag, hauth, hmac]
  · exact (hrep false).trans (hrep true).symm

/-- The trace receive is the receive oracle of `recvScheme` on the game state. -/
theorem traceReceive_run [DecidableEq P.EpochKey] [SampleableType P.EpochKey] {AS : Type}
    (view : RatchetedAuthenticator P.EpochKey P.EpochKey AS
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc) (repair party : Bool) (n : ℕ)
    (s : TraceState P AS) :
    (traceReceive view irl repair party n).run s =
      (liftGame (if party then
          SCKAScheme.oracleRecvA (recvScheme view irl repair s.transcript) n
        else SCKAScheme.oracleRecvB (recvScheme view irl repair s.transcript) n)).run s :=
  rfl

/-- Under `RepairInv`, the repaired trace receive keeps the records and the bad flag, and keeps the
invariant. -/
theorem traceReceive_outcome [DecidableEq P.Mac] [DecidableEq P.EpochKey]
    [SampleableType P.EpochKey]
    {irl : P.kem.IncrementalRandLeak P.inc} {S : ScheduledAuthenticator P Root MacKey}
    {tbl : Installed P irl (Root × MacKey)} {modes : Modes} {ik : P.EpochKey}
    (hHdrSound : P.decHdr.Sound P.ecpHdr) (hEkSound : P.decEk.Sound P.ecpEk)
    (hCt1Sound : P.decCt1.Sound P.ecpCt1) (hCt2Sound : P.decCt2.Sound P.ecpCt2)
    (party : Bool) (n : ℕ) (s : TraceState P (Root × MacKey))
    (h : RepairInv S tbl modes ik s.transcript s.game) :
    ∀ z ∈ support ((traceReceive S.toRatcheted irl true party n).run s),
      RepairInv S tbl modes ik z.2.transcript z.2.game ∧ z.2.transcript = s.transcript ∧
        z.2.bad = s.bad := by
  intro z hz
  cases hm : s.game.messagesAt (!party) n with
  | none =>
      have hpure : (traceReceive S.toRatcheted irl true party n).run s = pure (none, s) := by
        rw [traceReceive_run, liftGame_run]
        cases party
        · have hm' : s.game.msgA n = none := hm
          rw [ite_eq_right Bool.false_ne_true, SCKAScheme.oracleRecvB_run_eq_of_none _ _ hm',
            map_pure]
        · have hm' : s.game.msgB n = none := hm
          rw [ite_eq_left rfl, SCKAScheme.oracleRecvA_run_eq_of_none _ _ hm', map_pure]
      rw [hpure, mem_support_pure_iff] at hz
      subst hz
      exact ⟨h, rfl, rfl⟩
  | some entry =>
      obtain ⟨msg, tsnd⟩ := entry
      obtain ⟨key?, st', hrep, hinv⟩ :=
        recv_outcome hHdrSound hEkSound hCt1Sound hCt2Sound h party hm
      have hacc : (traceReceive S.toRatcheted irl true party n).run s =
          pure (some (msg.epoch - 1, key?.map Prod.fst),
            { s with game := (recvUpdate s.game party tsnd ⟨msg.epoch - 1, key?, st'⟩
              (msg.epoch - 1)) }) := by
        rw [traceReceive_run, liftGame_run]
        cases party
        · have hm' : s.game.msgA n = some (msg, tsnd) := hm
          rw [ite_eq_right Bool.false_ne_true,
            SCKAScheme.oracleRecvB_run_eq_of_accept
              (recvScheme S.toRatcheted irl true s.transcript) s.game hm' hrep, map_pure]
          rfl
        · have hm' : s.game.msgB n = some (msg, tsnd) := hm
          rw [ite_eq_left rfl,
            SCKAScheme.oracleRecvA_run_eq_of_accept
              (recvScheme S.toRatcheted irl true s.transcript) s.game hm' hrep, map_pure]
          rfl
      rw [hacc, mem_support_pure_iff] at hz
      subst hz
      exact ⟨hinv, rfl, rfl⟩

/-- At the real instance, with decapsulation agreement, the real and repaired trace receives are
equal. -/
theorem traceReceive_real_eq [DecidableEq P.Mac] [DecidableEq P.EpochKey]
    [SampleableType P.EpochKey]
    {irl : P.kem.IncrementalRandLeak P.inc} {S : ScheduledAuthenticator P Root MacKey}
    {ik : P.EpochKey}
    (hHdrSound : P.decHdr.Sound P.ecpHdr) (hEkSound : P.decEk.Sound P.ecpEk)
    (hCt1Sound : P.decCt1.Sound P.ecpCt1) (hCt2Sound : P.decCt2.Sound P.ecpCt2)
    (party : Bool) (n : ℕ) (s : TraceState P (Root × MacKey))
    (h : RepairInv S (Installed.empty (irl := irl)) Modes.real ik s.transcript s.game)
    (hgood : Braid.NoAuth.DecapsGood (EpochRecord.toTranscript ∘ s.transcript)) :
    (traceReceive S.toRatcheted irl false party n).run s =
      (traceReceive S.toRatcheted irl true party n).run s := by
  cases hm : s.game.messagesAt (!party) n with
  | none =>
      have hpure : ∀ rep, (traceReceive S.toRatcheted irl rep party n).run s =
          pure (none, s) := by
        intro rep
        rw [traceReceive_run, liftGame_run]
        cases party
        · have hm' : s.game.msgA n = none := hm
          rw [ite_eq_right Bool.false_ne_true, SCKAScheme.oracleRecvB_run_eq_of_none _ _ hm',
            map_pure]
        · have hm' : s.game.msgB n = none := hm
          rw [ite_eq_left rfl, SCKAScheme.oracleRecvA_run_eq_of_none _ _ hm', map_pure]
      rw [hpure, hpure]
  | some entry =>
      obtain ⟨msg, tsnd⟩ := entry
      obtain ⟨key?, st', htrue, -⟩ :=
        recv_outcome hHdrSound hEkSound hCt1Sound hCt2Sound h party hm
      have hfalse := (recv_outcome_real hHdrSound hEkSound hCt1Sound hCt2Sound h hgood party
        hm).trans htrue
      have hacc : ∀ rep, repairedRecv S.toRatcheted rep s.transcript (s.game.stateAt party) msg =
          some (key?, msg.epoch - 1, st') →
          (traceReceive S.toRatcheted irl rep party n).run s =
            pure (some (msg.epoch - 1, key?.map Prod.fst),
              { s with game := (recvUpdate s.game party tsnd ⟨msg.epoch - 1, key?, st'⟩
                (msg.epoch - 1)) }) := by
        intro rep hr
        rw [traceReceive_run, liftGame_run]
        cases party
        · have hm' : s.game.msgA n = some (msg, tsnd) := hm
          rw [ite_eq_right Bool.false_ne_true,
            SCKAScheme.oracleRecvB_run_eq_of_accept
              (recvScheme S.toRatcheted irl rep s.transcript) s.game hm' hr, map_pure]
          rfl
        · have hm' : s.game.msgB n = some (msg, tsnd) := hm
          rw [ite_eq_left rfl,
            SCKAScheme.oracleRecvA_run_eq_of_accept
              (recvScheme S.toRatcheted irl rep s.transcript) s.game hm' hr, map_pure]
          rfl
      rw [hacc false hfalse, hacc true htrue]

end MLKEMBraid.Auth
