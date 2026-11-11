/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.SPQR.Correspondence
public import SecureMessaging.SCKA.MLKEMBraid.Correctness

/-!
# The SPQR and ML-KEM Braid correctness games

`SPQR.Correspondence` compares single transitions of `SPQR.Chunked` and `Braid`. This module
compares the two SCKA correctness games. A game state records both party states, both key tables
and the messages that each party has sent. `GameState.toBraid` translates an SPQR game state
into a Braid game state: the party states by `PartyState.toBraid`, the recorded messages by
`Message.toBraid`, and every other field unchanged.

## Main results

* `sckaCorrectnessImpl_run_toBraid`: unless a query delivers a message in `RecvDivergence`,
  the translated SPQR successor state and the Braid successor state of the translated state have
  the same distribution.
* `DeliveryDivergence.ct1Acknowledged_ek`: if the translation of a state satisfies the Braid
  invariants `ControlInv` and `StatePairInv` and the state satisfies `Ct1AckInv`, a delivery in
  `RecvDivergence` is a plain vector chunk delivered to a party in `ct1Acknowledged`.
* `sckaCorrectnessImpl_run_toBraidAck`: for such a delivery, the translated SPQR successor
  state has the distribution of the Braid successor state of the translation in which the
  delivered record is an acknowledging vector chunk, once the record is restored.

`Ct1AckInv` is the one fact about SPQR that the Braid invariants cannot express. SPQR sends
`ct1Ack` only from `ekSentCt1Received`, and the translation turns every recorded `ct1Ack` into an
empty message. `Ct1AckInv` keeps the information that the translation forgets.

## The three divergent deliveries

Under these invariants, the first case of `RecvDivergence`, a future epoch outside the successor
epoch of `ct2Sampled`, cannot occur: a recorded message is at most one epoch ahead of its receiver,
and a sender one epoch ahead has a receiver in `ct2Sampled`. The second case, a standalone
`ct1Ack` in `ekReceivedCt1Sampled`, cannot occur either: its sender has received a chunk of `ct₂`,
so the receiver has already reached `ct2Sampled`.

The third case does occur. In the following run, A is the key generator of epoch `e` and B the
encapsulator.

```text
A (key generator, epoch e)                  B (encapsulator, epoch e)
headerSent:  ek chunk m₁ ─────────┐
ct1Received: ekCt1Ack chunk m₂ ───┼───────▶ ct1Sampled → ct1Acknowledged   (m₂ arrives first)
                                  └───────▶ m₁ arrives late:
                                              SPQR adds its chunk to the vector decoder;
                                              Braid ignores it
```

Both games answer the late delivery with the same receive report, but B's successor states differ,
and so do B's next messages. With this translation, the two games are not related step by step.
At the late delivery, however, A is in `ct1Received`, so A could have sent the same chunk as an
acknowledging vector chunk. B's SPQR step is the Braid step on that relabelled record.
`SPQR.Correctness` uses this to transport the Braid correctness bound to SPQR.
-/

@[expose] public section

open OracleSpec OracleComp
open ErasureCodePayload.Streaming

namespace SPQR

open Chunked

variable {P : SPQR.Parameters ProbComp} {InitKey AuthState : Type}

/-- The state of the correctness game played by two SPQR parties. -/
abbrev GameState (P : SPQR.Parameters ProbComp) (AuthState : Type) : Type :=
  SCKAScheme.GameState (Chunked.PartyState P AuthState) (Chunked.PartyState P AuthState)
    P.EpochKey (Chunked.Message P.Sym)

/-- The Braid game state with translated party states and recorded messages. The key tables,
counters, epochs and flags are unchanged. -/
-- ANCHOR: Relation_GameState_toMLKEMBraid
def GameState.toBraid (s : GameState P AuthState) :
    Braid.GameState P.toBraid AuthState where
  stA := s.stA.toBraid
  stB := s.stB.toBraid
  keyA := s.keyA
  keyB := s.keyB
  msgA := fun n => (s.msgA n).map fun e => (e.1.toBraid, e.2)
  msgB := fun n => (s.msgB n).map fun e => (e.1.toBraid, e.2)
  nA := s.nA
  nB := s.nB
  tcurA := s.tcurA
  tcurB := s.tcurB
  exposed := s.exposed
  challenged := s.challenged
  correct := s.correct
-- ANCHOR_END: Relation_GameState_toMLKEMBraid

/-- Every `ct1Ack` recorded by a party has an epoch below the party's epoch, or the party is still
in `ekSentCt1Received` at that epoch. -/
-- ANCHOR: Relation_Ct1AckInv
def Ct1AckInv (s : GameState P AuthState) : Prop :=
  ∀ (party : Bool) (n : ℕ) (msg : Chunked.Message P.Sym) (tsnd : ℕ),
    (if party then s.msgA else s.msgB) n = some (msg, tsnd) → msg.payload = .ct1Ack →
      msg.epoch < (if party then s.stA else s.stB).epoch ∨
        ∃ core dec, (if party then s.stA else s.stB) = .ekSentCt1Received core dec ∧
          core.ep = msg.epoch
-- ANCHOR_END: Relation_Ct1AckInv

/-- Query `t` delivers a recorded message in `RecvDivergence` for the receiver's state. -/
-- ANCHOR: Relation_DeliveryDivergence
def DeliveryDivergence (s : GameState P AuthState) :
    (SCKAScheme.sckaCorrectnessSpec (Chunked.Message P.Sym)).Domain → Prop
  | SCKAScheme.sckaCorrectnessSpec.ORecvA n =>
      ∃ msg tsnd, s.msgB n = some (msg, tsnd) ∧ RecvDivergence s.stA msg
  | SCKAScheme.sckaCorrectnessSpec.ORecvB n =>
      ∃ msg tsnd, s.msgA n = some (msg, tsnd) ∧ RecvDivergence s.stB msg
  | _ => False
-- ANCHOR_END: Relation_DeliveryDivergence

/-- The translation of `s` in which record `n` of the peer of `party` becomes an acknowledging
vector chunk. -/
-- ANCHOR: Relation_GameState_toMLKEMBraidAck
def GameState.toBraidAck (s : GameState P AuthState) (party : Bool) (n : ℕ) :
    Braid.GameState P.toBraid AuthState :=
  let relabel : Option (Braid.Message P.Sym × ℕ) → Option (Braid.Message P.Sym × ℕ) :=
    Option.map fun e => ({ e.1 with type := .ekCt1Ack }, e.2)
  if party then
    { s.toBraid with
      msgB := Function.update s.toBraid.msgB n (relabel (s.toBraid.msgB n)) }
  else
    { s.toBraid with
      msgA := Function.update s.toBraid.msgA n (relabel (s.toBraid.msgA n)) }
-- ANCHOR_END: Relation_GameState_toMLKEMBraidAck

/-! ### Translated game updates -/

/-- The translation of A's send update is the send update of the translation. -/
private theorem toBraid_sendAUpdate [DecidableEq P.EpochKey] (s : GameState P AuthState)
    (keyOpt : Option (ℕ × P.EpochKey)) (ρ : Chunked.Message P.Sym) (tsnd : ℕ)
    (stA' : PartyState P AuthState) :
    GameState.toBraid (SCKAScheme.sendAUpdate s keyOpt ρ tsnd stA') =
      SCKAScheme.sendAUpdate s.toBraid keyOpt ρ.toBraid tsnd stA'.toBraid := by
  have hmsg : (fun n => (Function.update s.msgA (s.nA + 1) (some (ρ, tsnd)) n).map
        fun e => (e.1.toBraid, e.2)) =
      Function.update s.toBraid.msgA (s.nA + 1) (some (ρ.toBraid, tsnd)) := by
    funext n
    by_cases hn : n = s.nA + 1
    · subst hn
      simp
    · simp [Function.update_of_ne hn, GameState.toBraid]
  rcases keyOpt with _ | ⟨tI, key⟩ <;>
    simp only [SCKAScheme.sendAUpdate, GameState.toBraid, hmsg] <;> rfl

/-- The version of `toBraid_sendAUpdate` for B. -/
private theorem toBraid_sendBUpdate [DecidableEq P.EpochKey] (s : GameState P AuthState)
    (keyOpt : Option (ℕ × P.EpochKey)) (ρ : Chunked.Message P.Sym) (tsnd : ℕ)
    (stB' : PartyState P AuthState) :
    GameState.toBraid (SCKAScheme.sendBUpdate s keyOpt ρ tsnd stB') =
      SCKAScheme.sendBUpdate s.toBraid keyOpt ρ.toBraid tsnd stB'.toBraid := by
  have hmsg : (fun n => (Function.update s.msgB (s.nB + 1) (some (ρ, tsnd)) n).map
        fun e => (e.1.toBraid, e.2)) =
      Function.update s.toBraid.msgB (s.nB + 1) (some (ρ.toBraid, tsnd)) := by
    funext n
    by_cases hn : n = s.nB + 1
    · subst hn
      simp
    · simp [Function.update_of_ne hn, GameState.toBraid]
  rcases keyOpt with _ | ⟨tI, key⟩ <;>
    simp only [SCKAScheme.sendBUpdate, GameState.toBraid, hmsg] <;> rfl

variable [DecidableEq P.EpochKey]
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
  (sampleInitKey : ProbComp InitKey)

/-! ### The relation of the two games -/

/-- Unless query `t` delivers a message in `RecvDivergence`, the translated SPQR successor state and
the Braid successor state of the translated state have the same distribution. -/
-- ANCHOR: Relation_sckaCorrectnessImpl_run_toMLKEMBraid
theorem sckaCorrectnessImpl_run_toBraid (s : GameState P AuthState)
    (t : (SCKAScheme.sckaCorrectnessSpec (Chunked.Message P.Sym)).Domain)
    (ht : ¬ DeliveryDivergence s t) :
    (fun z => GameState.toBraid z.2) <$>
        (SCKAScheme.sckaCorrectnessImpl (scheme P auth sampleInitKey) t).run s =
      (fun z => z.2) <$>
        (SCKAScheme.sckaCorrectnessImpl
          (Braid.scheme P.toBraid auth P.det.toRandLeak sampleInitKey) t).run
          s.toBraid
-- ANCHOR_END: Relation_sckaCorrectnessImpl_run_toMLKEMBraid
    := by
  rcases t with ((((n | u) | u) | n) | n)
  · simp [SCKAScheme.sckaCorrectnessImpl, SCKAScheme.oracleUnif, StateT.run_monadLift]
  · change (fun z => GameState.toBraid z.2) <$>
        (SCKAScheme.oracleSendA (scheme P auth sampleInitKey) ()).run s =
      (fun z => z.2) <$>
        (SCKAScheme.oracleSendA
          (Braid.scheme P.toBraid auth P.det.toRandLeak sampleInitKey) ()).run
          s.toBraid
    have hst : s.toBraid.stA = s.stA.toBraid := rfl
    rw [SCKAScheme.oracleSendA_run_eq,
      Braid.oracleSendA_run_eq (P := P.toBraid) auth P.det.toRandLeak sampleInitKey, hst,
      ← Chunked.send_toBraid]
    simp only [scheme, bind_pure_comp, Functor.map_map]
    congr 1
    funext r
    exact toBraid_sendAUpdate s r.outputKey r.msg r.sendingEpoch r.state
  · change (fun z => GameState.toBraid z.2) <$>
        (SCKAScheme.oracleSendB (scheme P auth sampleInitKey) ()).run s =
      (fun z => z.2) <$>
        (SCKAScheme.oracleSendB
          (Braid.scheme P.toBraid auth P.det.toRandLeak sampleInitKey) ()).run
          s.toBraid
    have hst : s.toBraid.stB = s.stB.toBraid := rfl
    rw [SCKAScheme.oracleSendB_run_eq,
      Braid.oracleSendB_run_eq (P := P.toBraid) auth P.det.toRandLeak sampleInitKey, hst,
      ← Chunked.send_toBraid]
    simp only [scheme, bind_pure_comp, Functor.map_map]
    congr 1
    funext r
    exact toBraid_sendBUpdate s r.outputKey r.msg r.sendingEpoch r.state
  · change (fun z => GameState.toBraid z.2) <$>
        (SCKAScheme.oracleRecvA (scheme P auth sampleInitKey) n).run s =
      (fun z => z.2) <$>
        (SCKAScheme.oracleRecvA
          (Braid.scheme P.toBraid auth P.det.toRandLeak sampleInitKey) n).run
          s.toBraid
    rcases hmsg : s.msgB n with _ | ⟨ρ, tsnd⟩
    · have hmsg' : s.toBraid.msgB n = none := by simp [GameState.toBraid, hmsg]
      rw [SCKAScheme.oracleRecvA_run_eq_of_none _ _ hmsg,
        SCKAScheme.oracleRecvA_run_eq_of_none _ _ hmsg']
      simp
    · have hmsg' : s.toBraid.msgB n = some (ρ.toBraid, tsnd) := by
        simp [GameState.toBraid, hmsg]
      have hdiv : ¬ RecvDivergence s.stA ρ := fun h => ht ⟨ρ, tsnd, hmsg, h⟩
      have hrecv := recvSCKA_toBraid P auth s.stA ρ hdiv
      rcases hS : recvSCKA P auth s.stA ρ with _ | ⟨keyOpt, trcv, stA'⟩
      · rw [hS] at hrecv
        rw [SCKAScheme.oracleRecvA_run_eq_of_refuse _ _ hmsg (by simpa [scheme] using hS),
          SCKAScheme.oracleRecvA_run_eq_of_refuse _ _ hmsg' hrecv.symm]
        simp [GameState.toBraid]
      · rw [hS] at hrecv
        rw [SCKAScheme.oracleRecvA_run_eq_of_accept _ _ hmsg (by simpa [scheme] using hS),
          SCKAScheme.oracleRecvA_run_eq_of_accept _ _ hmsg' hrecv.symm]
        rcases keyOpt with _ | ⟨tI, key⟩ <;>
          simp [SCKAScheme.recvAUpdate, GameState.toBraid]
  · change (fun z => GameState.toBraid z.2) <$>
        (SCKAScheme.oracleRecvB (scheme P auth sampleInitKey) n).run s =
      (fun z => z.2) <$>
        (SCKAScheme.oracleRecvB
          (Braid.scheme P.toBraid auth P.det.toRandLeak sampleInitKey) n).run
          s.toBraid
    rcases hmsg : s.msgA n with _ | ⟨ρ, tsnd⟩
    · have hmsg' : s.toBraid.msgA n = none := by simp [GameState.toBraid, hmsg]
      rw [SCKAScheme.oracleRecvB_run_eq_of_none _ _ hmsg,
        SCKAScheme.oracleRecvB_run_eq_of_none _ _ hmsg']
      simp
    · have hmsg' : s.toBraid.msgA n = some (ρ.toBraid, tsnd) := by
        simp [GameState.toBraid, hmsg]
      have hdiv : ¬ RecvDivergence s.stB ρ := fun h => ht ⟨ρ, tsnd, hmsg, h⟩
      have hrecv := recvSCKA_toBraid P auth s.stB ρ hdiv
      rcases hS : recvSCKA P auth s.stB ρ with _ | ⟨keyOpt, trcv, stB'⟩
      · rw [hS] at hrecv
        rw [SCKAScheme.oracleRecvB_run_eq_of_refuse _ _ hmsg (by simpa [scheme] using hS),
          SCKAScheme.oracleRecvB_run_eq_of_refuse _ _ hmsg' hrecv.symm]
        simp [GameState.toBraid]
      · rw [hS] at hrecv
        rw [SCKAScheme.oracleRecvB_run_eq_of_accept _ _ hmsg (by simpa [scheme] using hS),
          SCKAScheme.oracleRecvB_run_eq_of_accept _ _ hmsg' hrecv.symm]
        rcases keyOpt with _ | ⟨tI, key⟩ <;>
          simp [SCKAScheme.recvBUpdate, GameState.toBraid]

/-! ### Recorded acknowledgements -/

/-- The condition of `Ct1AckInv` for one party with state `st` and recorded messages `msgs`. -/
private def PartyCt1Ack (st : PartyState P AuthState)
    (msgs : ℕ → Option (Chunked.Message P.Sym × ℕ)) : Prop :=
  ∀ n msg tsnd, msgs n = some (msg, tsnd) → msg.payload = .ct1Ack →
    msg.epoch < st.epoch ∨ ∃ core dec, st = .ekSentCt1Received core dec ∧ core.ep = msg.epoch

omit [DecidableEq P.EpochKey] in
private theorem ct1AckInv_iff (s : GameState P AuthState) :
    Ct1AckInv s ↔ PartyCt1Ack s.stA s.msgA ∧ PartyCt1Ack s.stB s.msgB :=
  ⟨fun h => ⟨h true, h false⟩, fun h party => by cases party; exacts [h.2, h.1]⟩

omit [DecidableEq P.EpochKey] in
/-- A send keeps the epoch and stamps the message with it. It sends `ct1Ack` only from
`ekSentCt1Received`, which it keeps. -/
private theorem send_ct1Ack {st : PartyState P AuthState} {r : SendResult P AuthState}
    (hr : r ∈ support (send P auth st)) :
    r.state.epoch = st.epoch ∧ r.msg.epoch = st.epoch ∧
      (r.msg.payload = .ct1Ack → ∃ core dec, st = .ekSentCt1Received core dec) ∧
      ∀ core dec, st = .ekSentCt1Received core dec → r.state = st := by
  cases st
  case keysUnsampled core =>
    simp only [send, Chunked.send, EkSender.sendHeader, Parameters.generate, bind_assoc,
      pure_bind, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨r, -, rfl⟩ := hr
    simp [PartyState.epoch]
  case headerReceived core dec =>
    simp only [send, Chunked.send, CtSender.sendCt1, Parameters.encaps1, bind_assoc, pure_bind,
      mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨r, -, rfl⟩ := hr
    simp [PartyState.epoch]
  all_goals
    simp only [send, Chunked.send, mem_support_pure_iff] at hr
    subst hr
    simp [PartyState.epoch]

omit [DecidableEq P.EpochKey] in
/-- A successful second-ciphertext receive moves to the next epoch. -/
private theorem recvCt2_ep {core : EkSender.EkSentCt1Received P AuthState} {c2 : P.det.C₂}
    {tag : P.Mac} {next : CtSender.NoHeaderReceived AuthState} {key : ℕ × P.EpochKey}
    (h : EkSender.recvCt2 P auth core c2 tag = some (next, key)) :
    next.ep = core.ep + 1 := by
  unfold EkSender.recvCt2 at h
  split at h
  · cases h
  · simp only at h
    split_ifs at h
    cases h
    rfl

omit [DecidableEq P.EpochKey] in
/-- A receive never lowers the epoch. From `ekSentCt1Received` it stays in `ekSentCt1Received` at
the same epoch or moves to a later epoch. -/
private theorem recv_ct1Ack {st : PartyState P AuthState} {msg : Chunked.Message P.Sym}
    {r : RecvResult P AuthState} (hr : recv P auth st msg = .ok r) :
    st.epoch ≤ r.state.epoch ∧
      ∀ core dec, st = .ekSentCt1Received core dec →
        (∃ core' dec', r.state = .ekSentCt1Received core' dec' ∧ core'.ep = core.ep) ∨
          core.ep < r.state.epoch := by
  obtain ⟨e, payload⟩ := msg
  unfold recv at hr
  dsimp only at hr
  split_ifs at hr with hlt hgt
  · cases hr
    exact ⟨le_rfl, fun core dec hst => Or.inl ⟨core, dec, hst, rfl⟩⟩
  · cases st
    case ct2Sampled core enc =>
      simp only [CtSender.recvNextEpoch] at hr
      split_ifs at hr with hsucc
      cases hr
      exact ⟨by simp [PartyState.epoch], fun _ _ h => by cases h⟩
    all_goals cases hr
  · have heq : e = st.epoch := by omega
    subst heq
    cases st <;> cases payload <;>
      simp only [completeCt2, EkSender.sendEk, EkSender.recvCt1, CtSender.recvHeader,
        CtSender.recvEk] at hr <;>
      repeat' split at hr
    all_goals cases hr
    all_goals refine ⟨?_, fun core dec h => ?_⟩
    all_goals try split_ifs at *
    all_goals first
      | exact le_rfl
      | (cases h; done)
      | (cases h; exact Or.inl ⟨_, _, rfl, rfl⟩)
      | (simp_all [PartyState.epoch]; done)
      | (simp only [Option.some.injEq] at *; subst_vars; simp_all [PartyState.epoch]; done)
      | simp_all [PartyState.epoch, recvCt2_ep auth (by assumption)]

omit [DecidableEq P.EpochKey] in
private theorem partyCt1Ack_send {st : PartyState P AuthState}
    {msgs : ℕ → Option (Chunked.Message P.Sym × ℕ)} (h : PartyCt1Ack st msgs)
    {r : SendResult P AuthState} (hr : r ∈ support (send P auth st)) (k tsnd : ℕ) :
    PartyCt1Ack r.state (Function.update msgs k (some (r.msg, tsnd))) := by
  obtain ⟨hep, hmep, hack, hkeep⟩ := send_ct1Ack auth hr
  intro n msg tsnd' hn hpay
  by_cases hnk : n = k
  · subst hnk
    simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hn
    obtain ⟨rfl, -⟩ := hn
    obtain ⟨core, dec, hst⟩ := hack hpay
    refine Or.inr ⟨core, dec, (hkeep core dec hst).trans hst, ?_⟩
    rw [hmep, hst]
    rfl
  · rw [Function.update_of_ne hnk] at hn
    rcases h n msg tsnd' hn hpay with hlt | ⟨core, dec, hst, hep'⟩
    · exact Or.inl (hep ▸ hlt)
    · exact Or.inr ⟨core, dec, (hkeep core dec hst).trans hst, hep'⟩

omit [DecidableEq P.EpochKey] in
private theorem partyCt1Ack_recv {st : PartyState P AuthState}
    {msgs : ℕ → Option (Chunked.Message P.Sym × ℕ)} (h : PartyCt1Ack st msgs)
    {msg : Chunked.Message P.Sym} {r : RecvResult P AuthState}
    (hr : recv P auth st msg = .ok r) : PartyCt1Ack r.state msgs := by
  obtain ⟨hle, hekst⟩ := recv_ct1Ack auth hr
  intro n m tsnd hn hpay
  rcases h n m tsnd hn hpay with hlt | ⟨core, dec, hst, hep⟩
  · exact Or.inl (lt_of_lt_of_le hlt hle)
  · rcases hekst core dec hst with ⟨core', dec', hst', hep'⟩ | hlt
    · exact Or.inr ⟨core', dec', hst', hep'.trans hep⟩
    · exact Or.inl (hep ▸ hlt)

omit [DecidableEq P.EpochKey] in
private theorem partyCt1Ack_recvSCKA {st : PartyState P AuthState}
    {msgs : ℕ → Option (Chunked.Message P.Sym × ℕ)} (h : PartyCt1Ack st msgs)
    {msg : Chunked.Message P.Sym} {keyOpt : Option (ℕ × P.EpochKey)} {trcv : ℕ}
    {st' : PartyState P AuthState}
    (hr : recvSCKA P auth st msg = some (keyOpt, trcv, st')) : PartyCt1Ack st' msgs := by
  unfold recvSCKA at hr
  split at hr
  · cases hr
  · rename_i r hrecv
    cases hr
    exact partyCt1Ack_recv auth h hrecv

/-- Every query of the SPQR correctness game preserves `Ct1AckInv`. -/
-- ANCHOR: Relation_sckaCorrectnessImpl_preserves_ct1AckInv
theorem sckaCorrectnessImpl_preserves_ct1AckInv :
    QueryImpl.PreservesInv (SCKAScheme.sckaCorrectnessImpl (scheme P auth sampleInitKey))
      (Ct1AckInv (P := P) (AuthState := AuthState))
-- ANCHOR_END: Relation_sckaCorrectnessImpl_preserves_ct1AckInv
    := by
  refine SCKAScheme.sckaCorrectnessImpl_preservesInv _ ?_ ?_ ?_ ?_
  · intro _ s hs z hz
    obtain ⟨out, hout, rfl⟩ := (SCKAScheme.mem_support_oracleSendA_run_iff _ s z).1 hz
    simp only [scheme, mem_support_bind_iff, mem_support_pure_iff] at hout
    obtain ⟨r, hr, rfl⟩ := hout
    rw [ct1AckInv_iff] at hs ⊢
    have hA := partyCt1Ack_send auth hs.1 hr (s.nA + 1) r.sendingEpoch
    rcases r.outputKey with _ | ⟨tI, key⟩ <;> exact ⟨hA, hs.2⟩
  · intro _ s hs z hz
    obtain ⟨out, hout, rfl⟩ := (SCKAScheme.mem_support_oracleSendB_run_iff _ s z).1 hz
    simp only [scheme, mem_support_bind_iff, mem_support_pure_iff] at hout
    obtain ⟨r, hr, rfl⟩ := hout
    rw [ct1AckInv_iff] at hs ⊢
    have hB := partyCt1Ack_send auth hs.2 hr (s.nB + 1) r.sendingEpoch
    rcases r.outputKey with _ | ⟨tI, key⟩ <;> exact ⟨hs.1, hB⟩
  · intro n s hs z hz
    rcases (SCKAScheme.mem_support_oracleRecvA_run_iff _ s n z).1 hz with
      ⟨-, rfl⟩ | ⟨-, -, -, -, rfl⟩ | ⟨ρ, tsnd, keyOpt, trcv, stA', -, hr, rfl⟩
    · exact hs
    · exact hs
    · rw [ct1AckInv_iff] at hs ⊢
      have hA := partyCt1Ack_recvSCKA auth hs.1 hr
      rcases keyOpt with _ | ⟨tI, key⟩ <;> exact ⟨hA, hs.2⟩
  · intro n s hs z hz
    rcases (SCKAScheme.mem_support_oracleRecvB_run_iff _ s n z).1 hz with
      ⟨-, rfl⟩ | ⟨-, -, -, -, rfl⟩ | ⟨ρ, tsnd, keyOpt, trcv, stB', -, hr, rfl⟩
    · exact hs
    · exact hs
    · rw [ct1AckInv_iff] at hs ⊢
      have hB := partyCt1Ack_recvSCKA auth hs.2 hr
      rcases keyOpt with _ | ⟨tI, key⟩ <;> exact ⟨hs.1, hB⟩

/-! ### The divergent deliveries under the invariants -/

omit [DecidableEq P.EpochKey] in
private theorem toBraid_epoch (st : PartyState P AuthState) :
    st.toBraid.epoch = st.epoch := by
  cases st <;> rfl

omit [DecidableEq P.EpochKey] in
private theorem message_toBraid_epoch (msg : Chunked.Message P.Sym) :
    msg.toBraid.epoch = msg.epoch := by
  obtain ⟨e, payload⟩ := msg
  cases payload <;> rfl

omit [DecidableEq P.EpochKey] in
/-- Let `msg` be recorded by the peer of a receiver in state `st`, with the epoch bounds and the
pair invariant of the Braid correctness proof for the translated states. A delivery of `msg` in
`RecvDivergence` is then a plain vector chunk of the receiver's epoch, and the receiver is in
`ct1Acknowledged`. -/
private theorem recvDivergence_ct1Acknowledged_ek {st peer : PartyState P AuthState}
    {msg : Chunked.Message P.Sym}
    (hpair : Braid.PairInv st.toBraid peer.toBraid)
    (hpair' : Braid.PairInv peer.toBraid st.toBraid)
    (hpeer : peer.toBraid.epoch ≤ st.toBraid.completedEpoch + 1)
    (hmsg : msg.epoch ≤ peer.epoch)
    (hmsg' : msg.epoch ≤ st.toBraid.completedEpoch + 1)
    (hack : msg.payload = .ct1Ack →
      msg.epoch < peer.epoch ∨ ∃ core dec, peer = .ekSentCt1Received core dec ∧ core.ep = msg.epoch)
    (h : RecvDivergence st msg) :
    ∃ core dec chunk, st = .ct1Acknowledged core dec ∧ msg = ⟨core.ep, .ek chunk⟩ := by
  have hcomp := Braid.State.completedEpoch_le_epoch st.toBraid
  rw [toBraid_epoch] at hpeer hcomp
  rcases h with ⟨hlt, hnot⟩ | ⟨heq, ⟨core, enc, rfl⟩, hpay⟩ | ⟨heq, ⟨core, dec, rfl⟩, chunk, hpay⟩
  · -- A future message reaches a receiver one epoch behind its sender, which is in `ct2Sampled`.
    have hsucc : msg.epoch = st.epoch + 1 := by omega
    have hpos := (hpair.2 (by rw [toBraid_epoch, toBraid_epoch]; omega)).1
    exact absurd ⟨by cases st <;> simp_all [PartyState.toBraid,
      Braid.State.controlPosition], hsucc⟩ hnot
  · -- The sender of a `ct1Ack` has received a chunk of `ct₂`, so the receiver is in `ct2Sampled`.
    exfalso
    have hepE : (PartyState.ekReceivedCt1Sampled core enc).epoch = core.ep := rfl
    have hcompE :
        (PartyState.ekReceivedCt1Sampled core enc).toBraid.completedEpoch = core.ep := rfl
    rw [hepE] at heq
    rw [hcompE] at hpeer
    rcases hack hpay with hlt | ⟨core', dec', rfl, hep⟩
    · have := (hpair.2 (by rw [toBraid_epoch, toBraid_epoch, hepE]; omega)).1
      simp [PartyState.toBraid, Braid.State.controlPosition] at this
    · have := hpair'.1 (by simp [PartyState.toBraid, Braid.State.epoch]; omega)
        (by simp [PartyState.toBraid, Braid.State.controlPosition])
      simp [PartyState.toBraid, Braid.AllowedStatePair] at this
  · obtain ⟨e, payload⟩ := msg
    simp only [PartyState.epoch] at heq
    simp only at hpay
    subst heq hpay
    exact ⟨core, dec, chunk, rfl, rfl⟩

omit [DecidableEq P.EpochKey] in
/-- In a state whose translation satisfies the Braid control and pair invariants and that
satisfies `Ct1AckInv`, a divergent delivery is a plain vector chunk of the receiver's epoch
delivered to a party in `ct1Acknowledged`. -/
-- ANCHOR: Relation_DeliveryDivergence_ct1Acknowledged_ek
theorem DeliveryDivergence.ct1Acknowledged_ek {s : GameState P AuthState}
    {t : (SCKAScheme.sckaCorrectnessSpec (Chunked.Message P.Sym)).Domain}
    (hC : Braid.ControlInv s.toBraid) (hP : Braid.StatePairInv s.toBraid)
    (hack : Ct1AckInv s) (h : DeliveryDivergence s t) :
    ∃ (party : Bool) (n : ℕ) (core : CtSender.Ct1Sent P AuthState)
      (dec : P.decEk.D) (chunk : ℕ × P.Sym) (tsnd : ℕ),
      t = (if party then SCKAScheme.sckaCorrectnessSpec.ORecvA n
        else SCKAScheme.sckaCorrectnessSpec.ORecvB n) ∧
      (if party then s.stA else s.stB) = .ct1Acknowledged core dec ∧
      (if party then s.msgB else s.msgA) n = some (⟨core.ep, .ek chunk⟩, tsnd)
-- ANCHOR_END: Relation_DeliveryDivergence_ct1Acknowledged_ek
    := by
  rcases t with ((((n | u) | u) | n) | n)
  · exact h.elim
  · exact h.elim
  · exact h.elim
  · obtain ⟨msg, tsnd, hmsg, hdiv⟩ := h
    have hmsg' : s.toBraid.msgB n = some (msg.toBraid, tsnd) := by
      simp [GameState.toBraid, hmsg]
    have hctl := (hC.roles false).2.2 n _ tsnd hmsg'
    have hek := hC.epochKnowledge.msgB n _ tsnd hmsg'
    obtain ⟨core, dec, chunk, hst, rfl⟩ := recvDivergence_ct1Acknowledged_ek hP.1 hP.2
      hC.epochKnowledge.epochB_le
      (by simpa [Braid.GameState.stateAt, message_toBraid_epoch, toBraid_epoch,
        GameState.toBraid] using hctl.2.1)
      (by simpa [message_toBraid_epoch, GameState.toBraid] using hek.2.1)
      (hack false n msg tsnd hmsg) hdiv
    exact ⟨true, n, core, dec, chunk, tsnd, rfl, hst, hmsg⟩
  · obtain ⟨msg, tsnd, hmsg, hdiv⟩ := h
    have hmsg' : s.toBraid.msgA n = some (msg.toBraid, tsnd) := by
      simp [GameState.toBraid, hmsg]
    have hctl := (hC.roles true).2.2 n _ tsnd hmsg'
    have hek := hC.epochKnowledge.msgA n _ tsnd hmsg'
    obtain ⟨core, dec, chunk, hst, rfl⟩ := recvDivergence_ct1Acknowledged_ek hP.2 hP.1
      hC.epochKnowledge.epochA_le
      (by simpa [Braid.GameState.stateAt, message_toBraid_epoch, toBraid_epoch,
        GameState.toBraid] using hctl.2.1)
      (by simpa [message_toBraid_epoch, GameState.toBraid] using hek.2.1)
      (hack true n msg tsnd hmsg) hdiv
    exact ⟨false, n, core, dec, chunk, tsnd, rfl, hst, hmsg⟩

/-- For a plain vector chunk delivered to a party in `ct1Acknowledged`, the translated SPQR
successor state has the distribution of the Braid successor state of the translation in which that
record is an acknowledging vector chunk, once the record is restored. -/
-- ANCHOR: Relation_sckaCorrectnessImpl_run_toMLKEMBraidAck
theorem sckaCorrectnessImpl_run_toBraidAck (s : GameState P AuthState) (party : Bool)
    (n : ℕ) (core : CtSender.Ct1Sent P AuthState) (dec : P.decEk.D)
    (chunk : ℕ × P.Sym) (tsnd : ℕ)
    (hst : (if party then s.stA else s.stB) = .ct1Acknowledged core dec)
    (hmsg : (if party then s.msgB else s.msgA) n = some (⟨core.ep, .ek chunk⟩, tsnd)) :
    (fun z => GameState.toBraid z.2) <$>
        (SCKAScheme.sckaCorrectnessImpl (scheme P auth sampleInitKey)
          (if party then SCKAScheme.sckaCorrectnessSpec.ORecvA n
            else SCKAScheme.sckaCorrectnessSpec.ORecvB n)).run s =
      (fun z => if party then { z.2 with msgB := s.toBraid.msgB }
          else { z.2 with msgA := s.toBraid.msgA }) <$>
        (SCKAScheme.sckaCorrectnessImpl
          (Braid.scheme P.toBraid auth P.det.toRandLeak sampleInitKey)
          (if party then SCKAScheme.sckaCorrectnessSpec.ORecvA n
            else SCKAScheme.sckaCorrectnessSpec.ORecvB n)).run (s.toBraidAck party n)
-- ANCHOR_END: Relation_sckaCorrectnessImpl_run_toMLKEMBraidAck
    := by
  have hrecv := recvSCKA_ct1Acknowledged_ek_toBraid P auth core dec chunk
  cases party
  · simp only [Bool.false_eq_true, ↓reduceIte] at hst hmsg ⊢
    change (fun z => GameState.toBraid z.2) <$>
        (SCKAScheme.oracleRecvB (scheme P auth sampleInitKey) n).run s =
      (fun z => { z.2 with msgA := s.toBraid.msgA }) <$>
        (SCKAScheme.oracleRecvB
          (Braid.scheme P.toBraid auth P.det.toRandLeak sampleInitKey) n).run
          (s.toBraidAck false n)
    have hmsg' : (s.toBraidAck false n).msgA n =
        some (⟨core.ep, .ekCt1Ack, some chunk⟩, tsnd) := by
      simp [GameState.toBraidAck, GameState.toBraid, hmsg,
        Chunked.Message.toBraid]
    have hstB : (s.toBraidAck false n).stB =
        PartyState.toBraid (.ct1Acknowledged core dec) := by
      simp [GameState.toBraidAck, GameState.toBraid, hst]
    rcases hS : recvSCKA P auth (.ct1Acknowledged core dec) ⟨core.ep, .ek chunk⟩ with
      _ | ⟨keyOpt, trcv, stB'⟩
    · rw [hS] at hrecv
      rw [SCKAScheme.oracleRecvB_run_eq_of_refuse _ _ hmsg (by simpa [scheme, hst] using hS),
        SCKAScheme.oracleRecvB_run_eq_of_refuse _ _ hmsg' (by
          simpa [Braid.scheme, hstB] using hrecv.symm)]
      simp [GameState.toBraid, GameState.toBraidAck]
    · rw [hS] at hrecv
      rw [SCKAScheme.oracleRecvB_run_eq_of_accept _ _ hmsg (by simpa [scheme, hst] using hS),
        SCKAScheme.oracleRecvB_run_eq_of_accept _ _ hmsg' (by
          simpa [Braid.scheme, hstB] using hrecv.symm)]
      rcases keyOpt with _ | ⟨tI, key⟩ <;>
        simp [SCKAScheme.recvBUpdate, GameState.toBraid, GameState.toBraidAck]
  · simp only [↓reduceIte] at hst hmsg ⊢
    change (fun z => GameState.toBraid z.2) <$>
        (SCKAScheme.oracleRecvA (scheme P auth sampleInitKey) n).run s =
      (fun z => { z.2 with msgB := s.toBraid.msgB }) <$>
        (SCKAScheme.oracleRecvA
          (Braid.scheme P.toBraid auth P.det.toRandLeak sampleInitKey) n).run
          (s.toBraidAck true n)
    have hmsg' : (s.toBraidAck true n).msgB n =
        some (⟨core.ep, .ekCt1Ack, some chunk⟩, tsnd) := by
      simp [GameState.toBraidAck, GameState.toBraid, hmsg,
        Chunked.Message.toBraid]
    have hstA : (s.toBraidAck true n).stA =
        PartyState.toBraid (.ct1Acknowledged core dec) := by
      simp [GameState.toBraidAck, GameState.toBraid, hst]
    rcases hS : recvSCKA P auth (.ct1Acknowledged core dec) ⟨core.ep, .ek chunk⟩ with
      _ | ⟨keyOpt, trcv, stA'⟩
    · rw [hS] at hrecv
      rw [SCKAScheme.oracleRecvA_run_eq_of_refuse _ _ hmsg (by simpa [scheme, hst] using hS),
        SCKAScheme.oracleRecvA_run_eq_of_refuse _ _ hmsg' (by
          simpa [Braid.scheme, hstA] using hrecv.symm)]
      simp [GameState.toBraid, GameState.toBraidAck]
    · rw [hS] at hrecv
      rw [SCKAScheme.oracleRecvA_run_eq_of_accept _ _ hmsg (by simpa [scheme, hst] using hS),
        SCKAScheme.oracleRecvA_run_eq_of_accept _ _ hmsg' (by
          simpa [Braid.scheme, hstA] using hrecv.symm)]
      rcases keyOpt with _ | ⟨tI, key⟩ <;>
        simp [SCKAScheme.recvAUpdate, GameState.toBraid, GameState.toBraidAck]

end SPQR
