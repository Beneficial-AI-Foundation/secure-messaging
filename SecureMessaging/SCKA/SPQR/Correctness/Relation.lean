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
compares the two SCKA correctness games, one for each protocol:

* `SPQR.GameState` is the state of the game played by two SPQR parties;
* `Braid.GameState` is the state of the game played by two Braid parties.

In both, a game state records both party states, both key tables and the messages that each party
has sent. `GameState.toBraid` translates the first into the second. It translates the party states
by `PartyState.toBraid` and the recorded messages by `Message.toBraid`, and it keeps every other
field.

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

/-- The protocol state of `party`; `true` denotes A and `false` denotes B. -/
def GameState.stateAt (s : GameState P AuthState) (party : Bool) : PartyState P AuthState :=
  if party then s.stA else s.stB

/-- The messages sent by `party`, each stored with its reported epoch. -/
def GameState.messagesAt (s : GameState P AuthState) (party : Bool) :
    ℕ → Option (Chunked.Message P.Sym × ℕ) :=
  if party then s.msgA else s.msgB

/-- The Braid game state with translated party states and recorded messages. The key tables,
counters, epochs and flags are unchanged. -/
-- ANCHOR: Relation_GameState_toMLKEMBraid
def GameState.toBraid (s : GameState P AuthState) :
    Braid.GameState P.toBraid AuthState where
  stA := s.stA.toBraid
  stB := s.stB.toBraid
  keyA := s.keyA
  keyB := s.keyB
  msgA := fun n => (s.msgA n).map fun (msg, tsnd) => (msg.toBraid, tsnd)
  msgB := fun n => (s.msgB n).map fun (msg, tsnd) => (msg.toBraid, tsnd)
  nA := s.nA
  nB := s.nB
  tcurA := s.tcurA
  tcurB := s.tcurB
  exposed := s.exposed
  challenged := s.challenged
  correct := s.correct
-- ANCHOR_END: Relation_GameState_toMLKEMBraid

/-- Every `ct1Ack` among the messages `msgs` recorded by a party in state `st` has an epoch below
the epoch of `st`, or `st` is still in `ekSentCt1Received` at that epoch. -/
-- ANCHOR: Relation_PartyCt1Ack
def PartyCt1Ack (st : PartyState P AuthState)
    (msgs : ℕ → Option (Chunked.Message P.Sym × ℕ)) : Prop :=
  ∀ n msg tsnd, msgs n = some (msg, tsnd) → msg.payload = .ct1Ack →
    msg.epoch < st.epoch ∨ ∃ core dec, st = .ekSentCt1Received core dec ∧ core.ep = msg.epoch
-- ANCHOR_END: Relation_PartyCt1Ack

/-- Both parties satisfy `PartyCt1Ack` for their state and their recorded messages. -/
-- ANCHOR: Relation_Ct1AckInv
def Ct1AckInv (s : GameState P AuthState) : Prop :=
  ∀ party, PartyCt1Ack (s.stateAt party) (s.messagesAt party)
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
  s.toBraid.setMessages (!party)
    (Function.update (s.toBraid.messagesAt (!party)) n
      ((s.toBraid.messagesAt (!party) n).map fun (msg, tsnd) =>
        ({ msg with type := .ekCt1Ack }, tsnd)))
-- ANCHOR_END: Relation_GameState_toMLKEMBraidAck

/-! ### Translated game updates -/

/-- Translating a game state translates the state of each party. -/
@[simp] theorem GameState.toBraid_stateAt (s : GameState P AuthState) (party : Bool) :
    s.toBraid.stateAt party = (s.stateAt party).toBraid := by
  cases party <;> rfl

/-- Translating a game state translates each recorded message and keeps its report. -/
@[simp] theorem GameState.toBraid_messagesAt (s : GameState P AuthState) (party : Bool) (n : ℕ) :
    s.toBraid.messagesAt party n =
      (s.messagesAt party n).map fun (msg, tsnd) => (msg.toBraid, tsnd) := by
  cases party <;> rfl

/-- The translation of the send update of `party` is the send update of the translation. -/
private theorem toBraid_sendUpdate [DecidableEq P.EpochKey] (party : Bool)
    (s : GameState P AuthState) (keyOpt : Option (ℕ × P.EpochKey)) (ρ : Chunked.Message P.Sym)
    (tsnd : ℕ) (st' : PartyState P AuthState) :
    GameState.toBraid (if party then SCKAScheme.sendAUpdate s keyOpt ρ tsnd st'
        else SCKAScheme.sendBUpdate s keyOpt ρ tsnd st') =
      if party then SCKAScheme.sendAUpdate s.toBraid keyOpt ρ.toBraid tsnd st'.toBraid
      else SCKAScheme.sendBUpdate s.toBraid keyOpt ρ.toBraid tsnd st'.toBraid := by
  cases party
  · have hmsg : (fun n => (Function.update s.msgB (s.nB + 1) (some (ρ, tsnd)) n).map
          fun (msg, t) => (msg.toBraid, t)) =
        Function.update s.toBraid.msgB (s.nB + 1) (some (ρ.toBraid, tsnd)) :=
      Function.comp_update (Option.map (Prod.map Chunked.Message.toBraid id)) s.msgB
        (s.nB + 1) (some (ρ, tsnd))
    rcases keyOpt with _ | ⟨tI, key⟩ <;>
      simp only [Bool.false_eq_true, ↓reduceIte, SCKAScheme.sendBUpdate, GameState.toBraid,
        hmsg] <;> rfl
  · have hmsg : (fun n => (Function.update s.msgA (s.nA + 1) (some (ρ, tsnd)) n).map
          fun (msg, t) => (msg.toBraid, t)) =
        Function.update s.toBraid.msgA (s.nA + 1) (some (ρ.toBraid, tsnd)) :=
      Function.comp_update (Option.map (Prod.map Chunked.Message.toBraid id)) s.msgA
        (s.nA + 1) (some (ρ, tsnd))
    rcases keyOpt with _ | ⟨tI, key⟩ <;>
      simp only [↓reduceIte, SCKAScheme.sendAUpdate, GameState.toBraid, hmsg] <;> rfl

/-- The translation of the receive update of `party` is the receive update of the translation. -/
private theorem toBraid_recvUpdate [DecidableEq P.EpochKey] (party : Bool)
    (s : GameState P AuthState) (tsnd : ℕ) (keyOpt : Option (ℕ × P.EpochKey)) (trcv : ℕ)
    (st' : PartyState P AuthState) :
    GameState.toBraid (if party then SCKAScheme.recvAUpdate s tsnd keyOpt trcv st'
        else SCKAScheme.recvBUpdate s tsnd keyOpt trcv st') =
      if party then SCKAScheme.recvAUpdate s.toBraid tsnd keyOpt trcv st'.toBraid
      else SCKAScheme.recvBUpdate s.toBraid tsnd keyOpt trcv st'.toBraid := by
  cases party <;> rcases keyOpt with _ | ⟨tI, key⟩ <;>
    simp [SCKAScheme.recvAUpdate, SCKAScheme.recvBUpdate, GameState.toBraid]

variable (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
  (sampleInitKey : ProbComp InitKey)

/-! ### The relation of the two games -/

/-- The send query of `party` agrees with the Braid send query of the translation. -/
private theorem run_toBraid_send [DecidableEq P.EpochKey] (party : Bool)
    (s : GameState P AuthState) :
    (fun z => GameState.toBraid z.2) <$>
        (SCKAScheme.oracleSend (scheme P auth sampleInitKey) party ()).run s =
      (fun z => z.2) <$>
        (SCKAScheme.oracleSend (Braid.scheme P.toBraid auth P.det.toRandLeak sampleInitKey)
          party ()).run s.toBraid := by
  rw [SCKAScheme.oracleSend_run_eq (scheme P auth sampleInitKey) s rfl,
    SCKAScheme.oracleSend_run_eq (Braid.scheme P.toBraid auth P.det.toRandLeak sampleInitKey)
      s.toBraid rfl]
  simp only [scheme, Braid.scheme, bind_pure_comp, Functor.map_map]
  have hst : (if party then s.toBraid.stA else s.toBraid.stB) =
      (if party then s.stA else s.stB).toBraid := by
    cases party <;> rfl
  rw [hst, ← Chunked.send_toBraid]
  simp only [Functor.map_map]
  congr 1
  funext r
  exact toBraid_sendUpdate party s r.outputKey r.msg r.sendingEpoch r.state

/-- A receive query of `party` that delivers no message in `RecvDivergence` agrees with the Braid
receive query of the translation. -/
private theorem run_toBraid_recv [DecidableEq P.EpochKey] (party : Bool) (n : ℕ)
    (s : GameState P AuthState)
    (ht : ¬ ∃ msg tsnd, s.messagesAt (!party) n = some (msg, tsnd) ∧
      RecvDivergence (s.stateAt party) msg) :
    (fun z => GameState.toBraid z.2) <$>
        (SCKAScheme.oracleRecv (scheme P auth sampleInitKey) party n).run s =
      (fun z => z.2) <$>
        (SCKAScheme.oracleRecv (Braid.scheme P.toBraid auth P.det.toRandLeak sampleInitKey)
          party n).run s.toBraid := by
  rcases hmsg : s.messagesAt (!party) n with _ | ⟨ρ, tsnd⟩
  · have hmsg' : s.toBraid.messagesAt (!party) n = none := by simp [hmsg]
    rw [SCKAScheme.oracleRecv_run_eq_of_none _ _ hmsg,
      SCKAScheme.oracleRecv_run_eq_of_none _ _ hmsg']
    simp
  · have hmsg' : s.toBraid.messagesAt (!party) n = some (ρ.toBraid, tsnd) := by simp [hmsg]
    have hrecv := recvSCKA_toBraid P auth (s.stateAt party) ρ fun h => ht ⟨ρ, tsnd, hmsg, h⟩
    rw [← GameState.toBraid_stateAt] at hrecv
    rcases hS : recvSCKA P auth (s.stateAt party) ρ with _ | ⟨keyOpt, trcv, st'⟩
    · rw [hS] at hrecv
      rw [SCKAScheme.oracleRecv_run_eq_of_refuse _ _ rfl hmsg hS,
        SCKAScheme.oracleRecv_run_eq_of_refuse _ _ rfl hmsg' hrecv.symm]
      simp [GameState.toBraid]
    · rw [hS] at hrecv
      rw [SCKAScheme.oracleRecv_run_eq_of_accept _ _ rfl hmsg hS,
        SCKAScheme.oracleRecv_run_eq_of_accept _ _ rfl hmsg' hrecv.symm]
      simp [toBraid_recvUpdate]

/-- Unless query `t` delivers a message in `RecvDivergence`, the translated SPQR successor state and
the Braid successor state of the translated state have the same distribution. -/
-- ANCHOR: Relation_sckaCorrectnessImpl_run_toMLKEMBraid
theorem sckaCorrectnessImpl_run_toBraid [DecidableEq P.EpochKey] (s : GameState P AuthState)
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
  · exact run_toBraid_send auth sampleInitKey true s
  · exact run_toBraid_send auth sampleInitKey false s
  · exact run_toBraid_recv auth sampleInitKey true n s ht
  · exact run_toBraid_recv auth sampleInitKey false n s ht

/-! ### Recorded acknowledgements -/

/-- Let `s` satisfy `Ct1AckInv`. A state `U` satisfies `Ct1AckInv` if it has the state and messages
of `s` for the peer of `party` and satisfies the condition of `Ct1AckInv` for `party`. -/
theorem ct1AckInv_of_update {s U : GameState P AuthState} (party : Bool)
    (hs : Ct1AckInv s) (hst : U.stateAt (!party) = s.stateAt (!party))
    (hmsg : U.messagesAt (!party) = s.messagesAt (!party))
    (h : PartyCt1Ack (U.stateAt party) (U.messagesAt party)) : Ct1AckInv U := by
  intro who
  by_cases hw : who = party
  · subst hw
    exact h
  · obtain rfl : who = !party := by cases who <;> cases party <;> simp_all
    have hs' : PartyCt1Ack (s.stateAt (!party)) (s.messagesAt (!party)) := hs (!party)
    rw [← hst, ← hmsg] at hs'
    exact hs'

/-- A send keeps the epoch and stamps the message with it. It sends `ct1Ack` only from
`ekSentCt1Received`, which it keeps. -/
theorem send_ct1Ack {st : PartyState P AuthState} {r : SendResult P AuthState}
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

/-- A receive never lowers the epoch. From `ekSentCt1Received` it stays in `ekSentCt1Received` at
the same epoch or moves to a later epoch. -/
theorem recv_ct1Ack {st : PartyState P AuthState} {msg : Chunked.Message P.Sym}
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

/-- A send keeps `PartyCt1Ack` for the new state of the sender and its message table extended by
the sent message. -/
theorem partyCt1Ack_send {st : PartyState P AuthState}
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

/-- A receive that `recv` accepts keeps `PartyCt1Ack`. -/
theorem partyCt1Ack_recv {st : PartyState P AuthState}
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

/-- A receive that `recvSCKA` accepts keeps `PartyCt1Ack`. -/
theorem partyCt1Ack_recvSCKA {st : PartyState P AuthState}
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
theorem sckaCorrectnessImpl_preserves_ct1AckInv [DecidableEq P.EpochKey] :
    QueryImpl.PreservesInv (SCKAScheme.sckaCorrectnessImpl (scheme P auth sampleInitKey))
      (Ct1AckInv (P := P) (AuthState := AuthState))
    := by
  have hsend : ∀ party : Bool, QueryImpl.PreservesInv
      (SCKAScheme.oracleSend (scheme P auth sampleInitKey) party) Ct1AckInv := by
    intro party _ s hs z hz
    obtain ⟨out, hout, rfl⟩ := (SCKAScheme.mem_support_oracleSend_run_iff _ s rfl party z).1 hz
    simp only [scheme, mem_support_bind_iff, mem_support_pure_iff] at hout
    obtain ⟨r, hr, rfl⟩ := hout
    have hs' : PartyCt1Ack (GameState.stateAt s party) (GameState.messagesAt s party) := hs party
    have hr' : r ∈ support (send P auth (GameState.stateAt s party)) := hr
    refine ct1AckInv_of_update party hs ?_ ?_ ?_
    · cases party <;> rcases r.outputKey with _ | ⟨_, _⟩ <;> rfl
    · cases party <;> rcases r.outputKey with _ | ⟨_, _⟩ <;> rfl
    · cases party <;> rcases r.outputKey with _ | ⟨_, _⟩ <;>
        exact partyCt1Ack_send auth hs' hr' _ _
  have hrecv : ∀ party : Bool, QueryImpl.PreservesInv
      (SCKAScheme.oracleRecv (scheme P auth sampleInitKey) party) Ct1AckInv := by
    intro party n s hs z hz
    rcases (SCKAScheme.mem_support_oracleRecv_run_iff _ s rfl party n z).1 hz with
      ⟨-, rfl⟩ | ⟨-, -, -, -, rfl⟩ | ⟨ρ, tsnd, keyOpt, trcv, st', -, hr, rfl⟩
    · exact hs
    · exact hs
    · have hs' : PartyCt1Ack (GameState.stateAt s party) (GameState.messagesAt s party) := hs party
      have hr' : recvSCKA P auth (GameState.stateAt s party) ρ = some (keyOpt, trcv, st') := hr
      refine ct1AckInv_of_update party hs ?_ ?_ ?_
      · cases party <;> rcases keyOpt with _ | ⟨_, _⟩ <;> rfl
      · cases party <;> rcases keyOpt with _ | ⟨_, _⟩ <;> rfl
      · cases party <;> rcases keyOpt with _ | ⟨_, _⟩ <;>
          exact partyCt1Ack_recvSCKA auth hs' hr'
  exact SCKAScheme.sckaCorrectnessImpl_preservesInv _ (hsend true) (hsend false)
    (hrecv true) (hrecv false)

/-! ### The divergent deliveries under the invariants -/

/-- Let `msg` be recorded by the peer of a receiver in state `st`. Assume the Braid pair
invariants and epoch bounds, and the `ct1Ack` condition `hack` below. Then a delivery in
`RecvDivergence` is a plain vector chunk of the epoch of `st`, and `st` is in
`ct1Acknowledged`. -/
theorem recvDivergence_ct1Acknowledged_ek {st peer : PartyState P AuthState}
    {msg : Chunked.Message P.Sym}
    (hpair : Braid.PairInv st.toBraid peer.toBraid)
    (hpair' : Braid.PairInv peer.toBraid st.toBraid)
    (hpeer : peer.toBraid.epoch ≤ st.toBraid.completedEpoch + 1)
    (hmsg : msg.epoch ≤ peer.epoch)
    (hack : msg.payload = .ct1Ack →
      msg.epoch < peer.epoch ∨ ∃ core dec, peer = .ekSentCt1Received core dec ∧ core.ep = msg.epoch)
    (h : RecvDivergence st msg) :
    ∃ core dec chunk, st = .ct1Acknowledged core dec ∧ msg = ⟨core.ep, .ek chunk⟩ := by
  have hcomp := Braid.State.completedEpoch_le_epoch st.toBraid
  rw [PartyState.toBraid_epoch] at hpeer hcomp
  rcases h with ⟨hlt, hnot⟩ | ⟨heq, ⟨core, enc, rfl⟩, hpay⟩ | ⟨heq, ⟨core, dec, rfl⟩, chunk, hpay⟩
  · -- A future message reaches a receiver one epoch behind its sender, which is in `ct2Sampled`.
    have hsucc : msg.epoch = st.epoch + 1 := by omega
    have hpos := (hpair.2 (by rw [PartyState.toBraid_epoch, PartyState.toBraid_epoch]; omega)).1
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
    · have := (hpair.2 (by rw [PartyState.toBraid_epoch, PartyState.toBraid_epoch, hepE]; omega)).1
      simp [PartyState.toBraid, Braid.State.controlPosition] at this
    · have := hpair'.1 (by simp [PartyState.toBraid, Braid.State.epoch]; omega)
        (by simp [PartyState.toBraid, Braid.State.controlPosition])
      simp [PartyState.toBraid, Braid.AllowedStatePair] at this
  · obtain ⟨e, payload⟩ := msg
    simp only [PartyState.epoch] at heq
    simp only at hpay
    subst heq hpay
    exact ⟨core, dec, chunk, rfl, rfl⟩

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
      s.stateAt party = .ct1Acknowledged core dec ∧
      s.messagesAt (!party) n = some (⟨core.ep, .ek chunk⟩, tsnd)
-- ANCHOR_END: Relation_DeliveryDivergence_ct1Acknowledged_ek
    := by
  suffices key : ∀ (party : Bool) (n : ℕ),
      (∃ msg tsnd, s.messagesAt (!party) n = some (msg, tsnd) ∧
        RecvDivergence (s.stateAt party) msg) →
      ∃ (core : CtSender.Ct1Sent P AuthState) (dec : P.decEk.D) (chunk : ℕ × P.Sym) (tsnd : ℕ),
        s.stateAt party = .ct1Acknowledged core dec ∧
        s.messagesAt (!party) n = some (⟨core.ep, .ek chunk⟩, tsnd) by
    rcases t with ((((n | u) | u) | n) | n)
    · exact h.elim
    · exact h.elim
    · exact h.elim
    · obtain ⟨core, dec, chunk, tsnd, hst, hmsg⟩ := key true n h
      exact ⟨true, n, core, dec, chunk, tsnd, rfl, hst, hmsg⟩
    · obtain ⟨core, dec, chunk, tsnd, hst, hmsg⟩ := key false n h
      exact ⟨false, n, core, dec, chunk, tsnd, rfl, hst, hmsg⟩
  rintro party n ⟨msg, tsnd, hmsg, hdiv⟩
  have hmsg' : s.toBraid.messagesAt (!party) n = some (msg.toBraid, tsnd) := by simp [hmsg]
  have hctl := (hC.roles (!party)).2.2 n _ tsnd hmsg'
  obtain ⟨core, dec, chunk, hst, rfl⟩ := recvDivergence_ct1Acknowledged_ek
    (st := s.stateAt party) (peer := s.stateAt (!party))
    (by simpa using hP.pair party) (by simpa using hP.pair (!party))
    (by simpa using hC.epochKnowledge.epoch_le (!party))
    (by simpa using hctl.2.1)
    (hack (!party) n msg tsnd hmsg) hdiv
  exact ⟨core, dec, chunk, tsnd, hst, hmsg⟩

/-- For a plain vector chunk delivered to a party in `ct1Acknowledged`, the translated SPQR
successor state has the distribution of the Braid successor state of the translation in which that
record is an acknowledging vector chunk, once the record is restored. -/
-- ANCHOR: Relation_sckaCorrectnessImpl_run_toMLKEMBraidAck
theorem sckaCorrectnessImpl_run_toBraidAck [DecidableEq P.EpochKey] (s : GameState P AuthState)
    (party : Bool)
    (n : ℕ) (core : CtSender.Ct1Sent P AuthState) (dec : P.decEk.D)
    (chunk : ℕ × P.Sym) (tsnd : ℕ)
    (hst : s.stateAt party = .ct1Acknowledged core dec)
    (hmsg : s.messagesAt (!party) n = some (⟨core.ep, .ek chunk⟩, tsnd)) :
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
  suffices h : (fun z => GameState.toBraid z.2) <$>
        (SCKAScheme.oracleRecv (scheme P auth sampleInitKey) party n).run s =
      (fun z => if party then { z.2 with msgB := s.toBraid.msgB }
          else { z.2 with msgA := s.toBraid.msgA }) <$>
        (SCKAScheme.oracleRecv (Braid.scheme P.toBraid auth P.det.toRandLeak sampleInitKey)
          party n).run (s.toBraidAck party n) by
    cases party <;> exact h
  have hmsgAck : (s.toBraidAck party n).messagesAt (!party) n =
      some (⟨core.ep, .ekCt1Ack, some chunk⟩, tsnd) := by
    simp [GameState.toBraidAck, hmsg, Chunked.Message.toBraid]
  have hstAck : (if party then (s.toBraidAck party n).stA else (s.toBraidAck party n).stB) =
      (s.stateAt party).toBraid :=
    GameState.toBraid_stateAt s party
  have hrecv := recvSCKA_ct1Acknowledged_ek_toBraid P auth core dec chunk
  rw [← hst] at hrecv
  rcases hS : recvSCKA P auth (s.stateAt party) ⟨core.ep, .ek chunk⟩ with
    _ | ⟨keyOpt, trcv, st'⟩
  · rw [hS] at hrecv
    rw [SCKAScheme.oracleRecv_run_eq_of_refuse _ _ rfl hmsg hS,
      SCKAScheme.oracleRecv_run_eq_of_refuse _ _ rfl hmsgAck (by rw [hstAck]; exact hrecv.symm)]
    cases party <;> simp [GameState.toBraid, GameState.toBraidAck, Braid.GameState.setMessages]
  · rw [hS] at hrecv
    rw [SCKAScheme.oracleRecv_run_eq_of_accept _ _ rfl hmsg hS,
      SCKAScheme.oracleRecv_run_eq_of_accept _ _ rfl hmsgAck (by rw [hstAck]; exact hrecv.symm)]
    simp only [map_pure, toBraid_recvUpdate]
    cases party <;> rcases keyOpt with _ | ⟨tI, key⟩ <;>
      simp [SCKAScheme.recvAUpdate, SCKAScheme.recvBUpdate, GameState.toBraidAck,
        Braid.GameState.setMessages]

end SPQR
