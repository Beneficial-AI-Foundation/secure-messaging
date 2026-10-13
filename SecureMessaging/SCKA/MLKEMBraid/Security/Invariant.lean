/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.Games
import SecureMessaging.SCKA.MLKEMBraid.Correctness.SendInvariant
import SecureMessaging.SCKA.MLKEMBraid.Correctness.ReceiveInvariant

/-!
# The repaired transcript invariant of the no-authentication trace games

`RepairInv hMac T s` is `TranscriptConsistent` for the unit authenticator with only the final
actual-decapsulation implication of its `encaps` field removed. `DecapsGood T` states that actual
decapsulation agrees with every recorded first-stage encapsulation; together they give
`TranscriptConsistent`.

A committed trace send keeps `RepairInv` for its extended ghost transcript (`traceSend_preserves`).
A trace receive keeps it, including a repaired completion whose actual decapsulation would reject
or disagree; with `DecapsGood` the real and repaired receives coincide (`traceReceive_outcome`).

Several sampling-send steps adapt the private transcript proofs of
`MLKEMBraid.Correctness.SendInvariant` to `RepairInv`; the frozen originals are unchanged.
-/

open OracleSpec OracleComp
open ErasureCodePayload.Streaming

namespace MLKEMBraid.NoAuth

variable {P : Parameters ProbComp}

/-- `TranscriptConsistent` for the unit authenticator without the generator's actual
decapsulation agreement. -/
structure RepairInv (hMac : P.Mac = Unit) (T : ℕ → EpochTranscript P)
    (s : MLKEMBraid.GameState P Unit) : Prop where
  /-- The correctness flag is true. -/
  correct : s.correct = true
  /-- The control invariant holds. -/
  control : ControlInv s
  /-- The state-pair invariant holds. -/
  statePair : StatePairInv s
  /-- Epoch `0` has no key pair. -/
  keypair_zero : (T 0).keypair = none
  /-- Epoch `0` has no encapsulation. -/
  encaps_zero : (T 0).encaps1 = none
  /-- A recorded key pair belongs to a positive epoch its generator has reached. -/
  keypair : ∀ e pk sk, (T e).keypair = some (pk, sk) →
    0 < e ∧ e ≤ (if e % 2 = 1 then s.stA else s.stB).epoch
  /-- A recorded encapsulation belongs to a positive epoch its encapsulator has completed and
  that has a recorded key pair. -/
  encaps : ∀ e encapsState ct1 key,
    (T e).encaps1 = some (encapsState, ct1, key) →
    0 < e ∧ e ≤ (if e % 2 = 1 then s.stB else s.stA).completedEpoch ∧
      ∃ pk sk, (T e).keypair = some (pk, sk)
  /-- A's state agrees with the transcript. -/
  localA : LocalPayloadInv (auth P hMac) () T s.stA
  /-- B's state agrees with the transcript. -/
  localB : LocalPayloadInv (auth P hMac) () T s.stB
  /-- Every recorded message agrees with the transcript. -/
  messages : ∀ (party : Bool) n msg tsnd,
    (if party then s.msgA else s.msgB) n = some (msg, tsnd) →
      MessagePayloadInv (auth P hMac) () T msg
  /-- Each party's output keys are the transcript keys of its completed epochs. -/
  keys : ∀ (party : Bool) e,
    (if party then s.keyA else s.keyB) e =
      if 0 < e ∧ e ≤ (if party then s.stA else s.stB).completedEpoch then
        (T e).encaps1.map (fun (_, _, key) => P.kdfOK key e)
      else none

/-- Actual decapsulation of every recorded first-stage encapsulation gives its derived key. -/
def DecapsGood (T : ℕ → EpochTranscript P) : Prop :=
  ∀ e pk sk encapsState ct1 key, (T e).keypair = some (pk, sk) →
    (T e).encaps1 = some (encapsState, ct1, key) →
    decapsEpochKey e pk sk encapsState ct1 = some (P.kdfOK key e)

namespace RepairInv

variable {hMac : P.Mac = Unit} {T : ℕ → EpochTranscript P} {s : MLKEMBraid.GameState P Unit}

/-- Transcript consistency implies the repaired invariant. -/
theorem of_transcriptConsistent (h : TranscriptConsistent (auth P hMac) () T s) :
    RepairInv hMac T s :=
  ⟨h.correct, h.control, h.statePair, h.keypair_zero, h.encaps_zero, h.keypair,
    fun e es ct1 key hc => by
      obtain ⟨h0, hle, pk, sk, hkp, -⟩ := h.encaps e es ct1 key hc
      exact ⟨h0, hle, pk, sk, hkp⟩,
    h.localA, h.localB, h.messages, h.keys⟩

/-- With decapsulation agreement the repaired invariant is transcript consistency. -/
theorem transcriptConsistent (h : RepairInv hMac T s) (hgood : DecapsGood T) :
    TranscriptConsistent (auth P hMac) () T s :=
  ⟨h.correct, h.control, h.statePair, h.keypair_zero, h.encaps_zero, h.keypair,
    fun e es ct1 key hc => by
      obtain ⟨h0, hle, pk, sk, hkp⟩ := h.encaps e es ct1 key hc
      exact ⟨h0, hle, pk, sk, hkp, fun _ => hgood e pk sk es ct1 key hkp hc⟩,
    h.localA, h.localB, h.messages, h.keys⟩

/-- The state of either party agrees with the transcript. -/
theorem «local» (h : RepairInv hMac T s) (party : Bool) :
    LocalPayloadInv (auth P hMac) () T (s.stateAt party) := by
  cases party; exacts [h.localB, h.localA]

/-- The invariant reads neither the exposed nor the challenged epochs. -/
theorem setFlags (h : RepairInv hMac T s) (X Y : Finset ℕ) :
    RepairInv hMac T { s with exposed := X, challenged := Y } :=
  have hC := h.control
  have hE := hC.epochKnowledge
  ⟨h.correct,
    ⟨⟨⟨hE.keyPrefix.posA, hE.keyPrefix.posB, hE.keyPrefix.prefixA, hE.keyPrefix.prefixB⟩,
        hE.epochA_le, hE.epochB_le, hE.tcurA_le, hE.tcurB_le, hE.msgA, hE.msgB⟩,
      ⟨hC.recordedReport.msgA, hC.recordedReport.msgB⟩, hC.tcurA_le_sub_one,
      hC.tcurB_le_sub_one, hC.roles⟩,
    h.statePair, h.keypair_zero, h.encaps_zero, h.keypair, h.encaps, h.localA, h.localB,
    h.messages, h.keys⟩

/-- Build the invariant for the same transcript at a state with larger epochs and completed
epochs whose local states, messages and keys agree with the transcript. -/
theorem of_le (h : RepairInv hMac T s) {s' : MLKEMBraid.GameState P Unit}
    (hc : s'.correct = true) (hC : ControlInv s') (hP : StatePairInv s')
    (he : ∀ party, (s.stateAt party).epoch ≤ (s'.stateAt party).epoch)
    (hcomp : ∀ party, (s.stateAt party).completedEpoch ≤ (s'.stateAt party).completedEpoch)
    (hLocal : ∀ party, LocalPayloadInv (auth P hMac) () T (s'.stateAt party))
    (hMessages : ∀ party n msg tsnd, s'.messagesAt party n = some (msg, tsnd) →
      MessagePayloadInv (auth P hMac) () T msg)
    (hKeys : ∀ party e, s'.keysAt party e =
      if 0 < e ∧ e ≤ (s'.stateAt party).completedEpoch then
        (T e).encaps1.map (fun (_, _, key) => P.kdfOK key e) else none) :
    RepairInv hMac T s' := by
  refine ⟨hc, hC, hP, h.keypair_zero, h.encaps_zero, ?_, ?_, hLocal true, hLocal false,
    hMessages, hKeys⟩
  · intro e pk sk hk
    obtain ⟨h0, hle⟩ := h.keypair e pk sk hk
    refine ⟨h0, ?_⟩
    rw [← GameState.stateAt_generator] at hle ⊢
    exact hle.trans (he _)
  · intro e es ct1 key hc'
    obtain ⟨h0, hle, hkp⟩ := h.encaps e es ct1 key hc'
    refine ⟨h0, ?_, hkp⟩
    rw [← GameState.stateAt_encapsulator] at hle ⊢
    exact hle.trans (hcomp _)

/-- The pair and epoch bounds of the two parties. -/
theorem pairBounds (h : RepairInv hMac T s) (party : Bool) :
    let st := s.stateAt party
    let peer := s.stateAt (!party)
    PairInv st peer ∧ PairInv peer st ∧ 0 < st.epoch ∧ 0 < peer.epoch ∧
      st.epoch ≤ peer.completedEpoch + 1 ∧ peer.epoch ≤ st.completedEpoch + 1 ∧
      (st.epoch = peer.epoch →
        st.controlPosition.isGenerator = (!peer.controlPosition.isGenerator)) := by
  have hE := h.control.epochKnowledge
  refine ⟨h.statePair.pair party, by simpa using h.statePair.pair (!party),
    hE.keyPrefix.pos party, hE.keyPrefix.pos (!party), hE.epoch_le party,
    by simpa using hE.epoch_le (!party), ?_⟩
  cases party
  · intro heq
    simpa only [GameState.stateAt, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
      Bool.not_not] using (congrArg Bool.not (roles_opposite h.control heq.symm)).symm
  · exact roles_opposite h.control

/-- The peer of a key generator in `keysUnsampled` waits for the header of the same epoch. -/
theorem peer_of_keysUnsampled (h : RepairInv hMac T s) (party : Bool) {e : ℕ} {a : Unit}
    (hst : s.stateAt party = .keysUnsampled e a) :
    ∃ b dec, s.stateAt (!party) = .noHeaderReceived e b dec := by
  obtain ⟨h1, h2, hpos, hposP, hcross, hcrossP, -⟩ := h.pairBounds party
  exact PairInv.peer_of_keysUnsampled h1 h2 hpos hposP hcross hcrossP hst

/-- The peer of an encapsulator in `headerReceived` holds the recorded key pair of the epoch. -/
theorem peer_of_headerReceived (h : RepairInv hMac T s) (party : Bool) {e : ℕ} {a : Unit}
    {hdr : P.inc.PKheader} {dec : DecoderState P.inc.PKvector P.Sym}
    (hst : s.stateAt party = .headerReceived e a hdr dec) :
    ∃ pk sk b enc,
      (T e).keypair = some (pk, sk) ∧
      s.stateAt (!party) = .keysSampled e b sk (P.inc.toVector pk) enc ∧
      hdr = P.inc.toHeader pk := by
  obtain ⟨h1, h2, hpos, hposP, hcross, hcrossP, hroles⟩ := h.pairBounds party
  obtain ⟨b, sk', vec, enc, hpeer⟩ :=
    PairInv.peer_of_headerReceived h1 h2 hpos hposP hcross hcrossP hroles hst
  have hLs := h.local party
  have hLp := h.local (!party)
  rw [hst] at hLs
  rw [hpeer] at hLp
  obtain ⟨-, -, pk, sk, hkp, hhdr, -⟩ := hLs
  obtain ⟨-, pk', hkp', hvec, -⟩ := hLp
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hkp.symm.trans hkp'))
  exact ⟨pk, sk, b, enc, hkp, by rw [hpeer, hvec], hhdr⟩

end RepairInv

/-- At equal epochs a generator waiting for `ct₂` is paired with `ct2Sampled`. -/
private theorem PairInv.peer_of_ekSentCt1Received {st peer : State P Unit}
    (h : PairInv st peer) (h' : PairInv peer st)
    (hpos : 0 < st.epoch) (hposP : 0 < peer.epoch)
    (hcross : st.epoch ≤ peer.completedEpoch + 1) (hcrossP : peer.epoch ≤ st.completedEpoch + 1)
    {e : ℕ} {a : Unit} {sk : P.SK} {ct1 : P.inc.C₁}
    {dec : DecoderState (P.inc.C₂ × P.Mac) P.Sym}
    (hst : st = .ekSentCt1Received e a sk ct1 dec) :
    ∃ b enc, peer = .ct2Sampled e b enc := by
  subst hst
  cases peer <;>
    simp [PairInv, AllowedStatePair, State.controlPosition, State.epoch,
      State.completedEpoch] at * <;>
    omega

/-- If every message of a table and `msg` satisfy `MessagePayloadInv`, then so does every message of
the table after recording `msg`; adapted from the private `SendInvariant` helper. -/
private theorem messagePayloads_update (hMac : P.Mac = Unit) {T : ℕ → EpochTranscript P}
    {messages : ℕ → Option (Message P.Sym × ℕ)} {msg : Message P.Sym} {tsnd k : ℕ}
    (hOld : ∀ n m t, messages n = some (m, t) → MessagePayloadInv (auth P hMac) () T m)
    (hNew : MessagePayloadInv (auth P hMac) () T msg) :
    ∀ n m t, Function.update messages k (some (msg, tsnd)) n = some (m, t) →
      MessagePayloadInv (auth P hMac) () T m := by
  apply (Function.forall_update_iff messages
    (fun _ record => ∀ m t, record = some (m, t) → MessagePayloadInv (auth P hMac) () T m)).2
  refine ⟨?_, fun n _ => hOld n⟩
  intro m t h
  cases h
  exact hNew

/-- A send without sampling preserves epochs and the local payload invariant, outputs no key, and
emits a message satisfying `MessagePayloadInv`; adapted from the private `SendInvariant` step. -/
private theorem steady_step (hMac : P.Mac = Unit) {T : ℕ → EpochTranscript P}
    {st : State P Unit} {r : SendResult P Unit} (hedge : SendEdge (auth P hMac) st r)
    (hsteady : st.SendsNoSample) (hLocal : LocalPayloadInv (auth P hMac) () T st) :
    r.outputKey = none ∧ r.state.epoch = st.epoch ∧ r.state.completedEpoch = st.completedEpoch ∧
      LocalPayloadInv (auth P hMac) () T r.state ∧ MessagePayloadInv (auth P hMac) () T r.msg := by
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

/-- The send result of edge 1 for the key pair `(pk, sk)`. -/
private def keygenResult (hMac : P.Mac = Unit) (e : ℕ) (a : Unit) (pk : P.PK) (sk : P.SK) :
    SendResult P Unit :=
  ⟨⟨e, .hdr, some (EncoderState.init P.ecpHdr
      (P.inc.toHeader pk, (auth P hMac).macHeader a e (P.inc.toHeader pk))).nextChunk.1⟩,
    e - 1, none, .keysSampled e a sk (P.inc.toVector pk) (EncoderState.init P.ecpHdr
      (P.inc.toHeader pk, (auth P hMac).macHeader a e (P.inc.toHeader pk))).nextChunk.2⟩

/-- The send result of edge 7 for the first-stage encapsulation `(es, ct1, k)`. -/
private def encaps1Result (hMac : P.Mac = Unit) (e : ℕ) (a : Unit) (hdr : P.inc.PKheader)
    (dec : DecoderState P.inc.PKvector P.Sym) (es : P.inc.St) (ct1 : P.inc.C₁) (k : P.K) :
    SendResult P Unit :=
  ⟨⟨e, .ct1, some (EncoderState.init P.ecpCt1 ct1).nextChunk.1⟩, e - 1,
    some (e, P.kdfOK k e),
    .ct1Sampled e ((auth P hMac).update a e (P.kdfOK k e)) hdr es ct1
      (EncoderState.init P.ecpCt1 ct1).nextChunk.2 dec⟩

namespace RepairInv

variable {hMac : P.Mac = Unit} {T : ℕ → EpochTranscript P} {s : MLKEMBraid.GameState P Unit}

/-- A send without sampling keeps the invariant for the same transcript. -/
private theorem sendSteady (h : RepairInv hMac T s) (party : Bool) {r : SendResult P Unit}
    (hr : r ∈ support (send P (auth P hMac) (s.stateAt party)))
    (hsteady : (s.stateAt party).SendsNoSample)
    (hCP : ControlInv (sendSuccessor s party r) ∧ StatePairInv (sendSuccessor s party r)) :
    RepairInv hMac T (sendSuccessor s party r) := by
  obtain ⟨hnone, hep, hcomp, hLocalNew, hMsgNew⟩ :=
    steady_step hMac ((mem_support_send_iff (auth P hMac)).mp hr) hsteady (h.local party)
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
      exact messagePayloads_update hMac (h.messages party) hMsgNew
    · exact h.messages who
  · intro who e
    rw [keysAt_sendSuccessor, completedEpoch_stateAt_sendSuccessor s party who r hcomp]
    simp only [hnone, ite_self]
    exact h.keys who e

/-- A key-generation send records its key pair; adapted from the private `SendInvariant` proof. -/
private theorem sendKeygen (h : RepairInv hMac T s) (party : Bool) {e : ℕ} {a : Unit}
    (hst : s.stateAt party = .keysUnsampled e a) (pk : P.PK) (sk : P.SK)
    (hCP : ControlInv (sendSuccessor s party (keygenResult hMac e a pk sk)) ∧
      StatePairInv (sendSuccessor s party (keygenResult hMac e a pk sk))) :
    RepairInv hMac (Function.update T e { (T e) with keypair := some (pk, sk) })
      (sendSuccessor s party (keygenResult hMac e a pk sk)) := by
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
      ((sendSuccessor s party (keygenResult hMac e a pk sk)).stateAt who).epoch =
        (s.stateAt who).epoch := fun who =>
    epoch_stateAt_sendSuccessor s party who _ (by rw [hst]; rfl)
  have hcomp' : ∀ who,
      ((sendSuccessor s party (keygenResult hMac e a pk sk)).stateAt who).completedEpoch =
        (s.stateAt who).completedEpoch := fun who =>
    completedEpoch_stateAt_sendSuccessor s party who _ (by rw [hst]; rfl)
  have hLocal : ∀ who, LocalPayloadInv (auth P hMac) ()
      (Function.update T e { (T e) with keypair := some (pk, sk) })
        ((sendSuccessor s party (keygenResult hMac e a pk sk)).stateAt who) := by
    intro who
    rcases Bool.eq_or_eq_not who party with rfl | rfl
    · simp only [stateAt_sendSuccessor, ↓reduceIte, keygenResult]
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
    change ∀ n msg tsnd, (sendSuccessor s party (keygenResult hMac e a pk sk)).messagesAt who n =
      some (msg, tsnd) → _
    rw [messagesAt_sendSuccessor]
    split_ifs with hwho
    · subst who
      exact messagePayloads_update hMac
        (fun n msg tsnd hmsg => hMsgOld msg (hMessages party n msg tsnd hmsg))
        ⟨pk, sk, 0, hTke, congrArg (fun x => some (P.ecpHdr.encode
          (P.inc.toHeader pk, (auth P hMac).macHeader x e (P.inc.toHeader pk)) 0)) haT⟩
    · intro n msg tsnd hmsg
      exact hMsgOld msg (hMessages who n msg tsnd hmsg)
  · intro who e'
    change (sendSuccessor s party (keygenResult hMac e a pk sk)).keysAt who e' = _
    rw [keysAt_sendSuccessor]
    simp only [keygenResult, ite_self]
    change s.keysAt who e' = if 0 < e' ∧
      e' ≤ ((sendSuccessor s party (keygenResult hMac e a pk sk)).stateAt who).completedEpoch
      then _ else _
    rw [hcomp', hTe]
    exact hKeys who e'

/-- A first-stage encapsulation send records its sample and outputs the derived key; adapted from
the private `SendInvariant` proof without its decapsulation clause. -/
private theorem sendEncaps1 (h : RepairInv hMac T s) (party : Bool) {e : ℕ} {a : Unit}
    {hdr : P.inc.PKheader} {dec : DecoderState P.inc.PKvector P.Sym}
    (hst : s.stateAt party = .headerReceived e a hdr dec)
    (es : P.inc.St) (ct1 : P.inc.C₁) (k : P.K)
    (hCP : ControlInv (sendSuccessor s party (encaps1Result hMac e a hdr dec es ct1 k)) ∧
      StatePairInv (sendSuccessor s party (encaps1Result hMac e a hdr dec es ct1 k))) :
    RepairInv hMac (Function.update T e { (T e) with encaps1 := some (es, ct1, k) })
      (sendSuccessor s party (encaps1Result hMac e a hdr dec es ct1 k)) := by
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
      (encaps1Result hMac e a (P.inc.toHeader pk) (DecoderState.empty P.ecpEk) es ct1 k)).stateAt
        who).epoch = (s.stateAt who).epoch := fun who =>
    epoch_stateAt_sendSuccessor s party who _ (by rw [hst]; rfl)
  have hcomp' : ∀ who, ((sendSuccessor s party
      (encaps1Result hMac e a (P.inc.toHeader pk) (DecoderState.empty P.ecpEk) es ct1 k)).stateAt
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
        ((sendSuccessor s party (encaps1Result hMac e a (P.inc.toHeader pk)
          (DecoderState.empty P.ecpEk) es ct1 k)).stateAt who) := by
    intro who
    rcases Bool.eq_or_eq_not who party with rfl | rfl
    · simp only [stateAt_sendSuccessor, ↓reduceIte, encaps1Result]
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
    change ∀ n msg tsnd, (sendSuccessor s party (encaps1Result hMac e a (P.inc.toHeader pk)
      (DecoderState.empty P.ecpEk) es ct1 k)).messagesAt who n = some (msg, tsnd) → _
    rw [messagesAt_sendSuccessor]
    split_ifs with hwho
    · subst who
      exact messagePayloads_update hMac
        (fun n msg tsnd hmsg => hMsgOld msg (hBnd party n msg tsnd hmsg)
          (hMessages party n msg tsnd hmsg)) ⟨es, ct1, k, 0, hTce, rfl⟩
    · intro n msg tsnd hmsg
      exact hMsgOld msg (hBnd who n msg tsnd hmsg) (hMessages who n msg tsnd hmsg)
  · intro who e'
    change (sendSuccessor s party (encaps1Result hMac e a (P.inc.toHeader pk)
      (DecoderState.empty P.ecpEk) es ct1 k)).keysAt who e' = _
    rw [keysAt_sendSuccessor]
    change (if who = party then Function.update (s.keysAt who) e (some (P.kdfOK k e))
      else s.keysAt who) e' = if 0 < e' ∧ e' ≤ ((sendSuccessor s party (encaps1Result hMac e a
        (P.inc.toHeader pk) (DecoderState.empty P.ecpEk) es ct1 k)).stateAt who).completedEpoch
        then _ else _
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

end RepairInv

/-! ### Receives -/

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
      rw [if_pos (by omega), if_neg (by omega)]
      exact ⟨rfl, rfl⟩
    · simp only [GameState.stateAt, ↓reduceIte] at hRole hencapsulator ht ⊢
      rw [hencapsulator] at hRole
      have hne := of_decide_eq_false hRole.symm
      rw [if_neg (by omega), if_pos (by omega)]
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
          obtain ⟨-, -, pk, sk, hkp'⟩ := h.encaps (e + 1) c.1 c.2.1 c.2.2 hc
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
      · rw [oracleRecv, if_neg Bool.false_ne_true,
          oracleRecvB_run_eq_of_ok (auth P hMac) irl (pure ()) hmsg hr]
        simp [recvUpdate]
      · rw [oracleRecv, if_pos rfl,
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
    · exact h.local who
  · intro who n' msg' tsnd' hmsg'
    exact h.messages who n' msg' tsnd'
      ((congrFun (messagesAt_recvSuccessor s party who r (msg.epoch - 1)) n').symm.trans hmsg')
  · intro who e
    rw [keysAt_recvSuccessor, stateAt_recvSuccessor]
    by_cases hwho : who = party
    · subst who
      rw [if_pos rfl, if_pos rfl, hnone, hcompEq]
      exact h.keys party e
    · rw [if_neg hwho, if_neg hwho]
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
  obtain ⟨h1, h2, hpos, hposP, hcross, hcrossP, -⟩ := h.pairBounds party
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
  obtain ⟨h1, h2, hpos, hposP, hcross, hcrossP, -⟩ := h.pairBounds party
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
  have hnone : s.keysAt party e = none := by rw [hkeysS, if_neg (by omega)]
  have hpeerKey : s.keysAt (!party) e = some (P.kdfOK k e) := by
    rw [hkeysP, if_pos ⟨he0, le_rfl⟩, hc]; rfl
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
    · exact h.local who
  · intro who n' msg' tsnd' hmsg'
    exact h.messages who n' msg' tsnd'
      ((congrFun (messagesAt_recvSuccessor s party who _ (e - 1)) n').symm.trans hmsg')
  · intro who t
    rw [keysAt_recvSuccessor, stateAt_recvSuccessor]
    by_cases hwho : who = party
    · subst who
      rw [if_pos rfl, if_pos rfl]
      simp only [State.completedEpoch, State.epoch, Nat.add_sub_cancel]
      by_cases ht : t = e
      · subst t
        rw [Function.update_self, if_pos ⟨he0, le_rfl⟩, hc]
        rfl
      · rw [Function.update_of_ne ht, hkeysS]
        by_cases h1 : 0 < t ∧ t ≤ e - 1
        · rw [if_pos h1, if_pos ⟨h1.1, by omega⟩]
        · rw [if_neg h1, if_neg (by omega)]
    · rw [if_neg hwho, if_neg hwho]
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

/-! ### Trace steps -/

section TraceSteps

/-- `liftGame` runs a game oracle on the `game` field. -/
theorem liftGame_run {α : Type} (c : StateT (MLKEMBraid.GameState P Unit) ProbComp α)
    (s : TraceState P) :
    (liftGame c).run s = (fun z => (z.1, { s with game := z.2 })) <$> c.run s.game := rfl

/-- Projecting a lifted game oracle to its game state gives the game oracle. -/
theorem map_game_liftGame {α : Type} (c : StateT (MLKEMBraid.GameState P Unit) ProbComp α)
    (s : TraceState P) :
    Prod.map id TraceState.game <$> (liftGame c).run s = c.run s.game := by
  rw [liftGame_run, Functor.map_map]
  exact id_map (c.run s.game)

/-- Outcomes of a lifted game oracle keep the ghost records and bad flag. -/
theorem mem_support_liftGame {α : Type} {c : StateT (MLKEMBraid.GameState P Unit) ProbComp α}
    {s : TraceState P} {z : α × TraceState P} (hz : z ∈ support ((liftGame c).run s)) :
    ∃ w ∈ support (c.run s.game), z = (w.1, { s with game := w.2 }) := by
  rw [liftGame_run, support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact ⟨w, hw, rfl⟩

variable [DecidableEq P.EpochKey] (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)

/-- Outcomes of a trace send: a refused proposal, or the committed sampled proposal. -/
theorem mem_support_traceSend {party leaking : Bool} {s : TraceState P}
    {z : Option (ℕ × Option ℕ × Message P.Sym × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      TraceState P}
    (hz : z ∈ support ((traceSend P hMac irl party leaking).run s)) :
    z.2 = s ∨ ∃ w ∈ support (sampledSend P hMac irl s party),
      (leaking = true →
        (exposure P irl).send (s.game.stateAt party) w.1.1.state w.1.2 ∩ s.game.challenged = ∅) ∧
      z.2 = { game := { sendUpdate s.game party w.1.1 with
                exposed := if leaking then
                  s.game.exposed ∪ (exposure P irl).send (s.game.stateAt party) w.1.1.state w.1.2
                else s.game.exposed },
              transcript := w.2.1, bad := w.2.2 } := by
  change z ∈ support (traceSend P hMac irl party leaking s) at hz
  simp only [traceSend] at hz
  rw [support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  dsimp only
  by_cases hc : (leaking && decide ((exposure P irl).send (s.game.stateAt party) w.1.1.state
      w.1.2 ∩ s.game.challenged ≠ ∅)) = true
  · left
    rw [if_pos hc]
  · right
    refine ⟨w, hw, fun hl => ?_, by rw [if_neg hc]⟩
    subst hl
    simpa using hc

/-- The sample of a key-generation send. -/
private theorem sampledSend_keysUnsampled (s : TraceState P) (party : Bool) {e : ℕ} {a : Unit}
    (hst : s.game.stateAt party = .keysUnsampled e a) :
    sampledSend P hMac irl s party = (fun x : (P.PK × P.SK) × irl.KeygenRand =>
      ((keygenResult hMac e a x.1.1 x.1.2, SendRand.keygen x.2),
        Function.update s.transcript e { (s.transcript e) with keypair := some x.1 }, s.bad)) <$>
      irl.keygenRleak := by
  simp only [sampledSend, hst, map_eq_bind_pure_comp]
  exact bind_congr fun x => by obtain ⟨⟨pk, sk⟩, rand⟩ := x; rfl

/-- The sample of a first-stage encapsulation send, with its virtual decapsulation test. -/
private theorem sampledSend_headerReceived (s : TraceState P) (party : Bool) {e : ℕ} {a : Unit}
    {hdr : P.inc.PKheader} {dec : DecoderState P.inc.PKvector P.Sym}
    (hst : s.game.stateAt party = .headerReceived e a hdr dec) :
    sampledSend P hMac irl s party = (fun x : (P.inc.St × P.inc.C₁ × P.K) × irl.Encaps1Rand =>
      ((encaps1Result hMac e a hdr dec x.1.1 x.1.2.1 x.1.2.2, SendRand.encaps1 x.2),
        Function.update s.transcript e { (s.transcript e) with encaps1 := some x.1 },
        match (s.transcript e).keypair with
        | none => s.bad
        | some (pk, sk) => s.bad || decide (decapsEpochKey (P := P) e pk sk x.1.1 x.1.2.1 ≠
            some (P.kdfOK x.1.2.2 e)))) <$> irl.encaps1Rleak hdr := by
  simp only [sampledSend, hst, map_eq_bind_pure_comp]
  exact bind_congr fun x => by obtain ⟨⟨es, ct1, k⟩, rand⟩ := x; rfl

/-- A send that samples nothing keeps the ghost records and the bad flag. -/
private theorem sampledSend_steady (s : TraceState P) (party : Bool)
    (hsteady : (s.game.stateAt party).SendsNoSample) :
    sampledSend P hMac irl s party = (fun out => (out, s.transcript, s.bad)) <$>
      MLKEMBraid.sendRleak P irl (auth P hMac) (s.game.stateAt party) := by
  cases hst : s.game.stateAt party <;> rw [hst] at hsteady
  case keysUnsampled => exact False.elim hsteady
  case headerReceived => exact False.elim hsteady
  all_goals simp only [sampledSend, hst]

/-- A send never clears the bad flag. -/
private theorem sampledSend_bad {s : TraceState P} {party : Bool}
    {w : (SendResult P Unit × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      (ℕ → EpochTranscript P) × Bool}
    (hw : w ∈ support (sampledSend P hMac irl s party)) (hb : s.bad = true) : w.2.2 = true := by
  cases hst : s.game.stateAt party with
  | keysUnsampled e a =>
      rw [sampledSend_keysUnsampled hMac irl s party hst, support_map] at hw
      obtain ⟨x, -, rfl⟩ := hw
      exact hb
  | headerReceived e a hdr dec =>
      rw [sampledSend_headerReceived hMac irl s party hst, support_map] at hw
      obtain ⟨x, -, rfl⟩ := hw
      dsimp only
      split <;> simp [hb]
  | _ =>
      rw [sampledSend_steady hMac irl s party (by rw [hst]; trivial), support_map] at hw
      obtain ⟨x, -, rfl⟩ := hw
      exact hb

/-- A trace send never clears the bad flag. -/
theorem traceSend_bad {party leaking : Bool} {s : TraceState P} (hb : s.bad = true)
    {z : Option (ℕ × Option ℕ × Message P.Sym × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      TraceState P}
    (hz : z ∈ support ((traceSend P hMac irl party leaking).run s)) : z.2.bad = true := by
  rcases mem_support_traceSend hMac irl hz with hz | ⟨w, hw, -, hz⟩
  · rw [hz]; exact hb
  · rw [hz]; exact sampledSend_bad hMac irl hw hb

/-- The send update keeps the exposed and challenged epochs. -/
theorem sendUpdate_flags (g : MLKEMBraid.GameState P Unit) (party : Bool)
    (r : SendResult P Unit) :
    (sendUpdate g party r).exposed = g.exposed ∧
      (sendUpdate g party r).challenged = g.challenged := by
  cases party <;> rcases hk : r.outputKey with _ | ⟨e, k⟩ <;>
    simp [sendUpdate, SCKAScheme.sendAUpdate, SCKAScheme.sendBUpdate, hk]

/-- A trace send keeps the exposed and challenged epochs disjoint. -/
theorem traceSend_disjoint {party leaking : Bool} {s : TraceState P}
    (hs : s.game.exposed ∩ s.game.challenged = ∅)
    {z : Option (ℕ × Option ℕ × Message P.Sym × SendRand irl.KeygenRand irl.Encaps1Rand) ×
      TraceState P}
    (hz : z ∈ support ((traceSend P hMac irl party leaking).run s)) :
    z.2.game.exposed ∩ z.2.game.challenged = ∅ := by
  rcases mem_support_traceSend hMac irl hz with hz | ⟨w, -, hE, hz⟩
  · rw [hz]; exact hs
  rw [hz]
  obtain ⟨-, hch⟩ := sendUpdate_flags s.game party w.1.1
  dsimp only
  rw [hch]
  cases leaking
  · simpa using hs
  · simp only [if_true]
    rw [Finset.union_inter_distrib_right, Finset.union_eq_empty]
    exact ⟨hs, hE rfl⟩

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
      ControlInv (sendUpdate s.game party r') ∧ StatePairInv (sendUpdate s.game party r') :=
    fun r' hr' => oracleSend_preserves_controlInv_statePairInv (auth P hMac) irl (pure ()) party
      () s.game ⟨h.control, h.statePair⟩ _
      ((mem_support_oracleSend_run_iff (auth P hMac) irl (pure ()) s.game party _).2
        ⟨r', hr', rfl⟩)
  obtain ⟨htcur, hkeys⟩ := h.control.send_prefix party
  cases hst : s.game.stateAt party with
  | keysUnsampled e a =>
      rw [sampledSend_keysUnsampled hMac irl s party hst, support_map] at hw
      obtain ⟨⟨⟨pk, sk⟩, rand₀⟩, hkr, heq⟩ := hw
      simp only [Prod.mk.injEq] at heq
      obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := heq
      have hkg : (pk, sk) ∈ support P.kem.keygen := by
        rw [← irl.keygen_fst]
        simp only [mem_support_bind_iff, mem_support_pure_iff]
        exact ⟨_, hkr, rfl⟩
      have hr : keygenResult hMac e a pk sk ∈
          support (send P (auth P hMac) (s.game.stateAt party)) := by
        rw [hst, mem_support_send_iff]
        exact .keygen e a pk sk hkg
      rw [hst] at htcur hkeys
      simp only [State.epoch] at htcur hkeys
      have hflag : (sendUpdate s.game party (keygenResult hMac e a pk sk)).correct = true := by
        rw [sendUpdate_correct]
        simp only [keygenResult, Bool.and_eq_true]
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
      rw [sampledSend_headerReceived hMac irl s party hst, support_map] at hw
      obtain ⟨⟨⟨es, ct1, k⟩, rand₀⟩, hkr, heq⟩ := hw
      simp only [Prod.mk.injEq] at heq
      obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := heq
      have hek : (es, ct1, k) ∈ support (P.inc.encaps1 hdr) := by
        rw [← irl.encaps1_fst]
        simp only [mem_support_bind_iff, mem_support_pure_iff]
        exact ⟨_, hkr, rfl⟩
      have hr : encaps1Result hMac e a hdr dec es ct1 k ∈
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
      have hflag : (sendUpdate s.game party (encaps1Result hMac e a hdr dec es ct1 k)).correct =
          true := by
        rw [sendUpdate_correct]
        simp only [encaps1Result, Bool.and_eq_true]
        exact ⟨⟨⟨⟨h.correct, decide_eq_true htcur⟩, by simp [hnone]⟩, by simp [hnone]⟩,
          SCKAScheme.knownPrefix_update_some (SCKAScheme.knownPrefix_eq_true hkeys) e _⟩
      have hsucc := sendUpdate_eq_successor_of_correct s.game party _ h.correct hflag
      have hCP := hCPgen _ hr
      rw [hsucc] at hCP ⊢
      refine ⟨(RepairInv.sendEncaps1 h party hst es ct1 k hCP).setFlags _ _, fun hg hbad => ?_⟩
      simp only [hkpT, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_not] at hbad
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
      rw [sampledSend_steady hMac irl s party hsteady, support_map] at hw
      obtain ⟨out, hout, heq⟩ := hw
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      have hr : r ∈ support (send P (auth P hMac) (s.game.stateAt party)) := by
        rw [send_eq_map_sendRleak P irl, support_map]
        exact ⟨_, hout, rfl⟩
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

variable [DecidableEq P.Sym]

/-- The trace receive is the receive oracle of `recvScheme` on the game state. -/
theorem traceReceive_run (repair party : Bool) (n : ℕ) (s : TraceState P) :
    (traceReceive P hMac irl repair party n).run s =
      (liftGame (if party then
          SCKAScheme.oracleRecvA (recvScheme P hMac irl repair s.transcript) n
        else SCKAScheme.oracleRecvB (recvScheme P hMac irl repair s.transcript) n)).run s :=
  rfl

/-- Under the repaired invariant, and decapsulation agreement for the real receive, the real and
repaired trace receives coincide, keep the ghost records and keep the invariant. -/
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
          rw [if_neg Bool.false_ne_true, SCKAScheme.oracleRecvB_run_eq_of_none _ _ hm', map_pure]
        · have hm' : s.game.msgB n = none := hm
          rw [if_pos rfl, SCKAScheme.oracleRecvA_run_eq_of_none _ _ hm', map_pure]
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
          rw [if_neg Bool.false_ne_true,
            SCKAScheme.oracleRecvB_run_eq_of_accept (recvScheme P hMac irl rep s.transcript)
              s.game hm' hr, map_pure]
          rfl
        · have hm' : s.game.msgB n = some (msg, tsnd) := hm
          rw [if_pos rfl,
            SCKAScheme.oracleRecvA_run_eq_of_accept (recvScheme P hMac irl rep s.transcript)
              s.game hm' hr, map_pure]
          rfl
      refine ⟨by rw [hacc repair hrep, hacc true htrue], fun z hz => ?_⟩
      rw [hacc repair hrep, mem_support_pure_iff] at hz
      subst hz
      exact ⟨hinv, rfl, rfl⟩

end TraceSteps

end MLKEMBraid.NoAuth
