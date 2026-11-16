/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.SPQR.Security.Basic
public import SecureMessaging.SCKA.SPQR.Correctness.Relabel

/-!
# The invariant of the SPQR proof games

**Setting.** Let `auth` be a ratcheted authenticator and `s.toBraid` the translation of an SPQR
game state `s` into ML-KEM Braid (`SPQR.Correctness.Relation`). A game state `s` is
*sample-consistent* if `s.toBraid` satisfies the Braid transcript invariant `Braid.TranscriptInv`
(`MLKEMBraid.Correctness.Invariant`) with the trivial decapsulation condition `True` for some
initial key and transcript, and `s` satisfies `Ct1AckInv`; the proof games use it because their
receivers output recorded keys instead of decapsulating.

**Definitions.**

- `State.sentInEpoch st`: `0` in `keysUnsampled`, `noHeaderReceived` and `headerReceived`, `1` in
  the other states, which follow a send of the current epoch.
- `SendCountInv s`: for each party, `epoch - 1 + sentInEpoch ≤ countAt party`, where `countAt` is
  the party's send counter.
- `Inv auth s`: `s` is sample-consistent and `SendCountInv s`.
- `OpsPossible P ops`: every output of the samplers of `ops` is a possible output of
  `P.det.toKEM.keygen`, respectively of `P.det.toIncremental.encaps1`, and the second stage of
  `ops` is that of `P`.

**Main results.** Assume that the four stream decoders of `P` are sound for their erasure codes.

- `recvWith_ideal_outcome`: for `ops` whose second stage is that of `P`, delivering a recorded
  message to a party from a sample-consistent state `s` through `recvWith auth (idealOps ops s)`
  succeeds, reports the message epoch minus one, keeps the transcript, and outputs only the key
  recorded by the peer. After translation, its output key and new state are those of a Braid
  receive edge on the delivered message, except that a plain vector chunk delivered in
  `ct1Acknowledged` is received as the same chunk with the acknowledging type (`DeliveryEdge`).
- `idealCorrectness_preserves_at`: for `ops` with `OpsPossible P ops`, every correctness query of
  `schemeWith auth (idealOps ops s) sampleInitKey` from `s` preserves `Inv auth`; the case
  analysis over the queries holds for every predicate kept by the sends and the accepted receives
  (`schemeWith_correctness_preserves`).
- `Inv.keys_le_sends`: under `Inv auth s`, every epoch with a recorded key is positive and at most
  `s.nA + s.nB`.
- `recvWith_idealOps_eq_recv`: for `ops` whose second stage is that of `P`, if `s.toBraid`
  satisfies `TranscriptInv D` for a condition `D` and a transcript `T`, and decapsulation of the
  samples recorded in `T` at the receiver's epoch derives the transcript key, then the receive
  through `idealOps ops s` of a recorded message is that of `recv`.
-/

@[expose] public section

open OracleSpec OracleComp ErasureCodePayload.Streaming

namespace Braid

variable {P : Parameters ProbComp} {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)

/-- `0` in the states before a party's first send of its epoch (`keysUnsampled`,
`noHeaderReceived`, `headerReceived`), `1` otherwise. -/
def State.sentInEpoch : State P AuthState → ℕ
  | .keysUnsampled .. | .noHeaderReceived .. | .headerReceived .. => 0
  | _ => 1

/-- `completedEpoch ≤ epoch - 1 + sentInEpoch`. -/
private theorem State.completedEpoch_le_sent (st : State P AuthState) :
    st.completedEpoch ≤ st.epoch - 1 + st.sentInEpoch := by
  cases st <;> simp only [State.completedEpoch, State.epoch, State.sentInEpoch] <;> omega

/-- A send raises `epoch - 1 + sentInEpoch` by at most one. -/
private theorem SendEdge.sent_le {st : State P AuthState} {r : SendResult P AuthState}
    (h : SendEdge auth st r) :
    r.state.epoch - 1 + r.state.sentInEpoch ≤ st.epoch - 1 + st.sentInEpoch + 1 := by
  cases h <;> simp only [State.epoch, State.sentInEpoch] <;> omega

/-- A receive from a positive epoch keeps `epoch - 1 + sentInEpoch`. -/
private theorem ReceiveEdge.sent_eq {st : State P AuthState}
    {msg : Message P.Sym}
    {r : RecvResult P AuthState} (h : ReceiveEdge auth st msg r) (hpos : 0 < st.epoch) :
    r.state.epoch - 1 + r.state.sentInEpoch = st.epoch - 1 + st.sentInEpoch := by
  cases h <;> (try simp only [State.epoch, State.sentInEpoch] at hpos ⊢) <;> omega

end Braid

namespace SPQR

open Chunked

variable {P : SPQR.Parameters ProbComp} {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
  (sampleInitKey : ProbComp InitKey)
  (hHdrSound : P.decHdr.Sound P.ecpHdr) (hEkSound : P.decEk.Sound P.ecpEk)
  (hCt1Sound : P.decCt1.Sound P.ecpCt1) (hCt2Sound : P.decCt2.Sound P.ecpCt2)

/-- The number of messages sent by `party`. -/
def GameState.countAt (s : GameState P AuthState) (party : Bool) : ℕ :=
  if party then s.nA else s.nB

/-- For each party, `epoch - 1 + sentInEpoch` of its translated state is at most its send
counter. -/
def SendCountInv (s : GameState P AuthState) : Prop :=
  ∀ party, (s.toBraid.stateAt party).epoch - 1 +
    (s.toBraid.stateAt party).sentInEpoch ≤ s.countAt party

/-- `s` is sample-consistent (for some initial key and transcript, the translated game state
satisfies the transcript invariant with the trivial decapsulation condition, and `s` satisfies
`Ct1AckInv`), and the send counters bound the epochs (`SendCountInv s`). -/
def Inv (s : GameState P AuthState) : Prop :=
  (∃ (ik : InitKey) (T : ℕ → Braid.EpochTranscript P.toBraid),
    Braid.TranscriptInv (P := P.toBraid) auth (fun _ _ _ _ _ _ => True) ik T s.toBraid) ∧
    Ct1AckInv s ∧ SendCountInv s

/-- Every output of the samplers of `ops` is a possible output of `P.det.toKEM.keygen`,
respectively of `P.det.toIncremental.encaps1`, and the second stage of `ops` is that of `P`. -/
def OpsPossible (P : SPQR.Parameters ProbComp) (ops : Ops P) : Prop :=
  (∀ t out, out ∈ support (ops.keygenRleak t) → out.1 ∈ support P.det.toKEM.keygen) ∧
  (∀ t hdr out, out ∈ support (ops.encaps1Rleak t hdr) → out.1 ∈ support
    (P.det.toIncremental.encaps1 hdr)) ∧
  (∀ t, ops.encaps2 t = P.det.encaps2Det)

/-- The real operations are possible. -/
theorem opsPossible_real :
    OpsPossible P (Ops.real P) :=
  ⟨fun _ out hout => by
      rw [← P.det.toRandLeak.keygen_fst]
      exact (mem_support_bind_iff _ _ _).mpr ⟨out, hout, (mem_support_pure_iff _ _).mpr rfl⟩,
    fun _ hdr out hout => by
      rw [← P.det.toRandLeak.encaps1_fst hdr]
      exact (mem_support_bind_iff _ _ _).mpr ⟨out, hout, (mem_support_pure_iff _ _).mpr rfl⟩,
    fun _ => rfl⟩

/-- The samplers of `ops` at the state `st` of a sending party produce possible outputs: of
`P.det.toKEM.keygen` in `keysUnsampled`, and of `P.det.toIncremental.encaps1` at the stored
header in `headerReceived`. -/
def OpsPossibleAt (ops : Ops P) : PartyState P AuthState → Prop
  | .keysUnsampled core =>
      ∀ out ∈ support (ops.keygenRleak core.ep), out.1 ∈ support P.det.toKEM.keygen
  | .headerReceived core _ =>
      ∀ out ∈ support (ops.encaps1Rleak core.ep core.hdr), out.1 ∈ support
        (P.det.toIncremental.encaps1 core.hdr)
  | _ => True

/-- Possible operations are possible at every state. -/
private theorem OpsPossible.at {ops : Ops P} (h : OpsPossible P ops)
    (st : PartyState P AuthState) : OpsPossibleAt ops st := by
  cases st
  case keysUnsampled core => exact fun out hout => h.1 _ _ hout
  case headerReceived core dec => exact fun out hout => h.2.1 _ _ _ hout
  all_goals trivial

/-- Every possible result of `sendWith auth ops` from `st` is a possible result of `send` when
`ops` is possible at `st`. -/
theorem sendWith_mem_support_send {ops : Ops P}
    {st : PartyState P AuthState} (hposs : OpsPossibleAt ops st) {r : SendResult P AuthState}
    (hr : r ∈ support (sendWith auth ops st)) : r ∈ support (SPQR.send P auth st) := by
  cases st
  case keysUnsampled core =>
    simp only [sendWith, sendRleakWith, support_map, Set.mem_image, mem_support_bind_iff] at hr
    obtain ⟨x, ⟨⟨⟨pk, sk⟩, rnd⟩, hkg, hx⟩, rfl⟩ := hr
    simp only [mem_support_pure_iff] at hx
    subst hx
    have hg := hposs _ hkg
    change (pk, sk) ∈ support (P.det.keygenDet <$> P.det.sampleKeygen) at hg
    rw [support_map, Set.mem_image] at hg
    obtain ⟨coins, hcoins, hout⟩ := hg
    simp only [SPQR.send, Chunked.send, EkSender.sendHeader, Parameters.generate, bind_assoc,
      pure_bind, mem_support_bind_iff]
    exact ⟨coins, hcoins, by simp [hout]⟩
  case headerReceived core dec =>
    simp only [sendWith, sendRleakWith, support_map, Set.mem_image, mem_support_bind_iff] at hr
    obtain ⟨x, ⟨⟨⟨es, c1, k⟩, rnd⟩, henc, hx⟩, rfl⟩ := hr
    simp only [mem_support_pure_iff] at hx
    subst hx
    have hg := hposs _ henc
    change (es, c1, k) ∈ support (P.det.encaps1Det core.hdr <$> P.det.sampleEncaps1) at hg
    rw [support_map, Set.mem_image] at hg
    obtain ⟨coins, hcoins, hout⟩ := hg
    simp only [SPQR.send, Chunked.send, CtSender.sendCt1, Parameters.encaps1, bind_assoc,
      pure_bind, mem_support_bind_iff]
    exact ⟨coins, hcoins, by simp [hout]⟩
  all_goals
    simp only [sendWith, sendRleakWith, support_map, Set.mem_image] at hr
    obtain ⟨x, ⟨y, hy, rfl⟩, rfl⟩ := hr
    exact hy

/-- A possible result of an SPQR send is, after translation, a Braid send edge. -/
theorem sendEdge_toBraid {st : PartyState P AuthState} {r : SendResult P AuthState}
    (hr : r ∈ support (SPQR.send P auth st)) :
    Braid.SendEdge (P := P.toBraid) auth st.toBraid r.toBraid := by
  refine (Braid.mem_support_send_iff (P := P.toBraid) auth).mp ?_
  rw [← Chunked.send_toBraid, support_map]
  exact Set.mem_image_of_mem _ hr

/-- `Inv` ignores the exposed and challenged sets. -/
theorem Inv.with_bookkeeping {s : GameState P AuthState} (h : Inv auth s)
    (exposed challenged : Finset ℕ) :
    Inv auth { s with exposed := exposed, challenged := challenged } := by
  obtain ⟨⟨ik, T, hT⟩, hack, hcount⟩ := h
  exact ⟨⟨ik, T, hT.setFlags exposed challenged⟩, hack, hcount⟩

/-- The initial game state satisfies `Ct1AckInv`: it records no message. -/
theorem ct1AckInv_initGameState (ik : InitKey) :
    Ct1AckInv (SCKAScheme.initGameState (initA P auth ik) (initB P auth ik)) := by
  intro party n msg tsnd h
  cases party <;> simp [GameState.messagesAt, SCKAScheme.initGameState] at h

/-- The initial game state satisfies `Inv`. -/
theorem Inv_initGameState (ik : InitKey) :
    Inv auth (SCKAScheme.initGameState (initA P auth ik) (initB P auth ik)) := by
  refine ⟨⟨ik, fun _ => { keypair := none, encaps1 := none }, ?_⟩,
    ct1AckInv_initGameState auth ik, ?_⟩
  · rw [toBraid_initGameState]
    exact Braid.transcriptInv_initGameState (P := P.toBraid) auth ik
  · intro party
    cases party <;>
      simp [GameState.countAt, GameState.toBraid, Braid.GameState.stateAt,
        SCKAScheme.initGameState, toBraid_initA, toBraid_initB, Braid.initA, Braid.initB,
        Braid.State.epoch, Braid.State.sentInEpoch]

/-- Under `Inv auth s`, every epoch with a recorded key is positive and at most `s.nA + s.nB`. -/
theorem Inv.keys_le_sends {s : GameState P AuthState} (h : Inv auth s) (t : ℕ)
    (hk : (s.keyA t).isSome ∨ (s.keyB t).isSome) : 0 < t ∧ t ≤ s.nA + s.nB := by
  obtain ⟨⟨ik, T, hT⟩, -, hcount⟩ := h
  have hpref := hT.control.epochKnowledge.keyPrefix
  have key (party : Bool) (hk : (s.toBraid.keysAt party t).isSome) :
      0 < t ∧ t ≤ s.nA + s.nB := by
    obtain ⟨hpos, hle⟩ := (hpref.keys party t).1 (Option.isSome_iff_ne_none.mp hk)
    have h1 := (s.toBraid.stateAt party).completedEpoch_le_sent
    have h2 := hcount party
    refine ⟨hpos, ?_⟩
    cases party <;> simp only [GameState.countAt, Bool.false_eq_true, ↓reduceIte] at h2 <;> omega
  rcases hk with hk | hk
  · exact key true (by simpa [toBraid_keysAt] using hk)
  · exact key false (by simpa [toBraid_keysAt] using hk)

/-! ### The ideal receive -/

section Receive

variable {D : ℕ → P.toBraid.PK → P.toBraid.SK → P.toBraid.inc.St → P.toBraid.inc.C₁ →
  P.toBraid.K → Prop}

include hCt2Sound in
/-- Let `s.toBraid` satisfy `TranscriptInv D` for a transcript `T`, `party` be in
`ekSentCt1Received core dec`, and the peer have
recorded the `ct₂` chunk `⟨core.ep, .ct2 chunk⟩`. Then `party` generates `core.ep`; the transcript
records `core.sk` and `core.c1` at `core.ep` with some `pk`, `es` and KEM key `key`; the peer's key
table holds `P.kdfOK key core.ep`; and the decoder can complete only to the second ciphertext
component of the recorded samples. -/
private theorem ct2_cell_transcript {ik : InitKey}
    {T : ℕ → Braid.EpochTranscript P.toBraid} {s : GameState P AuthState}
    (hT : Braid.TranscriptInv (P := P.toBraid) auth D ik T s.toBraid) (party : Bool) {n
      tsnd : ℕ}
    {core : EkSender.EkSentCt1Received P AuthState}
    {dec : P.decCt2.D} {chunk : ℕ × P.Sym}
    (hst : s.stateAt party = .ekSentCt1Received core dec)
    (hentry : s.messagesAt (!party) n = some (⟨core.ep, .ct2 chunk⟩, tsnd)) :
    generatorOf core.ep = party ∧
    ∃ pk es key, (T core.ep).keypair = some (pk, core.sk) ∧
      (T core.ep).encaps1 = some (es, core.c1, key) ∧
      s.toBraid.keysAt (!party) core.ep = some (P.kdfOK key core.ep) ∧
      ∀ c2 tag, P.decCt2.decodedPayload (P.decCt2.addChunk dec chunk) = some (c2, tag) →
        c2 = P.det.encaps2Det es (P.det.toHeader pk) (P.det.toVector pk) := by
  have hentry' := GameState.toBraid_messagesAt_eq_some hentry
  have hPayload := hT.messages (!party) n _ tsnd hentry'
  have hLocal := hT.local (P := P.toBraid) auth party
  rw [GameState.toBraid_stateAt] at hLocal
  have hgen : (s.toBraid.stateAt party).controlPosition.isGenerator = true := by
    rw [GameState.toBraid_stateAt, hst]; rfl
  have hpeerKey := Braid.generator_peer_key (P := P.toBraid) auth hT party hgen
  simp only [GameState.toBraid_stateAt, hst, PartyState.toBraid, Braid.State.epoch]
    at hpeerKey
  have hparty : generatorOf core.ep = party := by
    have hRole := hT.control.role party
    rw [hgen, GameState.toBraid_stateAt, hst] at hRole
    simp only [PartyState.toBraid, Braid.State.epoch] at hRole
    have h := of_decide_eq_true hRole.symm
    cases party
    · simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact decide_eq_false (by omega)
    · exact decide_eq_true h
  rw [hst] at hLocal
  simp only [PartyState.toBraid, Braid.LocalPayloadInv] at hLocal
  obtain ⟨-, pk, es, key, hkp, hc, hrcv⟩ := hLocal
  simp only [Message.toBraid, Braid.MessagePayloadInv] at hPayload
  obtain ⟨pk', sk', es', ct1', key', i, hkp', hc', hchunk⟩ := hPayload
  obtain ⟨rfl, -⟩ : pk = pk' ∧ core.sk = sk' := by simpa using hkp.symm.trans hkp'
  obtain ⟨rfl, hc1, rfl⟩ : es = es' ∧ core.c1 = ct1' ∧ key = key' := by
    have heq := Option.some.inj (hc.symm.trans hc')
    exact ⟨congrArg Prod.fst heq, congrArg (fun x => x.2.1) heq,
      congrArg (fun x => x.2.2) heq⟩
  rw [← hc1] at hchunk
  have hch := Option.some.inj hchunk
  have hC := hCt2Sound.received_addChunk hrcv i
  erw [← hch] at hC
  refine ⟨hparty, pk, es, key, hkp, hc, hpeerKey es core.c1 key hc, fun c2 tag hdec => ?_⟩
  obtain ⟨-, hnone | hsome⟩ := hC
  · rw [hnone] at hdec
    cases hdec
  · rw [hsome] at hdec
    exact (congrArg Prod.fst (Option.some.inj hdec)).symm

/-- The translation of the delivery of `msg` to `party` with Braid result `r` is a Braid receive
edge: on `msg.toBraid`, or, for a plain vector chunk of the current epoch delivered in
`ct1Acknowledged`, on the same chunk with the acknowledging type, which is how `Braid` receives it
(`recvSCKA_ct1Acknowledged_ek_toBraid`). -/
def DeliveryEdge (s : GameState P AuthState) (party : Bool) (msg : Message P.Sym)
    (r : Braid.RecvResult P.toBraid AuthState) : Prop :=
  Braid.ReceiveEdge (P := P.toBraid) auth (s.toBraid.stateAt party) msg.toBraid r ∨
    ∃ core dec chunk, s.stateAt party = .ct1Acknowledged core dec ∧ msg = ⟨core.ep, .ek chunk⟩ ∧
      Braid.ReceiveEdge (P := P.toBraid) auth (s.toBraid.stateAt party)
        ⟨core.ep, .ekCt1Ack, some chunk⟩ r

/-- `PartyCt1Ack` passes to a state `st'` that does not lower the epoch and, from
`ekSentCt1Received`, stays there at the same epoch or moves to a later epoch. -/
private theorem partyCt1Ack_of_step {st st' : PartyState P AuthState}
    {msgs : ℕ → Option (Message P.Sym × ℕ)} (h : PartyCt1Ack st msgs)
    (hle : st.epoch ≤ st'.epoch)
    (hek : ∀ core dec, st = .ekSentCt1Received core dec →
      (∃ core' dec', st' = .ekSentCt1Received core' dec' ∧ core'.ep = core.ep) ∨
        core.ep < st'.epoch) :
    PartyCt1Ack st' msgs := by
  intro n m tsnd hn hpay
  rcases h n m tsnd hn hpay with hlt | ⟨core, dec, hst, hep⟩
  · exact Or.inl (lt_of_lt_of_le hlt hle)
  · rcases hek core dec hst with ⟨core', dec', hst', hep'⟩ | hlt
    · exact Or.inr ⟨core', dec', hst', hep'.trans hep⟩
    · exact Or.inl (hep ▸ hlt)

include hHdrSound hEkSound hCt1Sound in
/-- Let `s.toBraid` satisfy `TranscriptInv D` for a transcript `T`, `s` satisfy `Ct1AckInv`, and
`msg` be recorded by the peer of `party` at index `n`, other than a `ct₂` chunk of the current
epoch in `ekSentCt1Received`. Then `recv` accepts `msg` without a key, reporting `msg.epoch - 1`;
the new state agrees with `T`, has epoch at least `msg.epoch`, and its translation is the new
state of a `DeliveryEdge` without output key. -/
private theorem recv_recorded_outcome {ik : InitKey} {T : ℕ → Braid.EpochTranscript P.toBraid}
    {s : GameState P AuthState} (hT : Braid.TranscriptInv (P := P.toBraid) auth D ik T s.toBraid)
    (hack : Ct1AckInv s) (party : Bool) {n : ℕ} {msg : Message P.Sym} {tsnd : ℕ}
    (hentry : s.messagesAt (!party) n = some (msg, tsnd))
    (hcell : ¬ ∃ core dec chunk, s.stateAt party = .ekSentCt1Received core dec ∧
      msg = ⟨core.ep, .ct2 chunk⟩) :
    ∃ r : RecvResult P AuthState, recv P auth (s.stateAt party) msg = .ok r ∧
      r.outputKey = none ∧ r.receivingEpoch = msg.epoch - 1 ∧
      Braid.LocalPayloadInv (P := P.toBraid) auth ik T r.state.toBraid ∧
      msg.epoch ≤ r.state.epoch ∧
      ∃ trep, DeliveryEdge auth s party msg ⟨trep, none, r.state.toBraid⟩ := by
  -- The Braid game state and message of the delivery: the translation, except that a plain vector
  -- chunk delivered in `ct1Acknowledged` is relabelled as an acknowledging vector chunk.
  obtain ⟨B, msg', hTB, hstB, hentryB, hcellB, hep, hagree, hDE⟩ :
      ∃ (B : Braid.GameState P.toBraid AuthState) (msg' : Braid.Message P.Sym),
        Braid.TranscriptInv (P := P.toBraid) auth D ik T B ∧
        B.stateAt party = s.toBraid.stateAt party ∧
        B.messagesAt (!party) n = some (msg', tsnd) ∧
        (∀ e a sk ct1 dec chunk, B.stateAt party = .ekSentCt1Received e a sk ct1 dec →
          msg' ≠ ⟨e, .ct2, some chunk⟩) ∧
        msg'.epoch = msg.epoch ∧
        (recvSCKA P auth (s.stateAt party) msg).map
            (fun (keyOpt, trcv, st') => (keyOpt, trcv, st'.toBraid)) =
          Braid.recvSCKA P.toBraid auth (s.stateAt party).toBraid msg' ∧
        ∀ r, Braid.ReceiveEdge (P := P.toBraid) auth (s.toBraid.stateAt party) msg' r →
          DeliveryEdge auth s party msg r := by
    by_cases hlate : ∃ core dec chunk, s.stateAt party = .ct1Acknowledged core dec ∧
        msg = ⟨core.ep, .ek chunk⟩
    · obtain ⟨core, dec, chunk, hst, rfl⟩ := hlate
      refine ⟨s.toBraidAck party n, ⟨core.ep, .ekCt1Ack, some chunk⟩,
        transcriptInv_toBraidAck auth hT party n hst hentry, ?_, ?_,
        (fun _ _ _ _ _ _ _ h => by cases h), rfl, ?_,
        fun r h => Or.inr ⟨core, dec, chunk, hst, rfl, h⟩⟩
      · cases party <;> rfl
      · have hmsgF : s.toBraid.messagesAt (!party) n = some (⟨core.ep, .ek, some chunk⟩, tsnd) := by
          simp [hentry, Chunked.Message.toBraid]
        simp [GameState.toBraidAck, hmsgF]
      · rw [hst]
        exact recvSCKA_ct1Acknowledged_ek_toBraid P auth core dec chunk
    · have hmsg' := GameState.toBraid_messagesAt_eq_some hentry
      have hctl := (hT.control.roles (!party)).2.2 n _ tsnd hmsg'
      have hdiv : ¬ RecvDivergence (s.stateAt party) msg := fun h => hlate
        (recvDivergence_ct1Acknowledged_ek (st := s.stateAt party) (peer := s.stateAt (!party))
          (by simpa using hT.statePair.pair party) (by simpa using hT.statePair.pair (!party))
          (by simpa using hT.control.epochKnowledge.epoch_le (!party))
          (by simpa [Message.toBraid_epoch, PartyState.toBraid_epoch] using hctl.2.1)
          (hack (!party) n msg tsnd hentry) h)
      refine ⟨s.toBraid, msg.toBraid, hT, rfl, hmsg', ?_, Message.toBraid_epoch msg,
        recvSCKA_toBraid P auth _ msg hdiv, fun r h => Or.inl h⟩
      intro e a sk ct1 dec chunk hst hmsg
      rw [GameState.toBraid_stateAt] at hst
      obtain ⟨st, hst'⟩ : ∃ st, s.stateAt party = st := ⟨_, rfl⟩
      rw [hst'] at hst hcell
      cases st with
      | ekSentCt1Received core dec' =>
        simp only [PartyState.toBraid] at hst
        obtain ⟨rfl, -, -, -, -⟩ := hst
        obtain ⟨me, payload⟩ := msg
        cases payload <;> simp only [Message.toBraid, Braid.Message.mk.injEq,
          reduceCtorEq, and_false, false_and, true_and, Option.some.injEq] at hmsg
        obtain ⟨rfl, rfl⟩ := hmsg
        exact hcell ⟨core, _, _, rfl, rfl⟩
      | _ => simp [PartyState.toBraid] at hst
  -- Braid receives `msg'` without a key; transfer the result through the agreement.
  obtain ⟨r', hr', hnone', hLocal'⟩ := Braid.receive_recorded_noKey (P := P.toBraid) auth
    hHdrSound hEkSound hCt1Sound hTB party hentryB hcellB
  have hedge := Braid.ReceiveEdge.of_eq_ok (P := P.toBraid) auth hr'
  have hmsgEpoch := Braid.receive_msg_epoch_le (P := P.toBraid) auth hTB.control party
    hentryB hr'
  rw [hstB, GameState.toBraid_stateAt] at hr' hedge
  have hb : Braid.recvSCKA P.toBraid auth (s.stateAt party).toBraid msg' =
      some (none, msg.epoch - 1, r'.state) := by
    simp [Braid.recvSCKA, hr', hnone', hep]
  rw [hb] at hagree
  obtain ⟨r, hr, hrk, hre, hrs⟩ : ∃ r, recv P auth (s.stateAt party) msg = .ok r ∧
      r.outputKey = none ∧ r.receivingEpoch = msg.epoch - 1 ∧ r.state.toBraid = r'.state := by
    rcases hr : recv P auth (s.stateAt party) msg with err | r
    · simp [recvSCKA, hr] at hagree
    · simp only [recvSCKA, hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hagree
      exact ⟨r, rfl, hagree.1, hagree.2.1, hagree.2.2⟩
  refine ⟨r, hr, hrk, hre, by rw [hrs]; exact hLocal', ?_, r'.receivingEpoch, hDE _ ?_⟩
  · rw [← PartyState.toBraid_epoch, hrs, ← hep]
    exact hmsgEpoch
  · rw [GameState.toBraid_stateAt, hrs, ← hnone']
    exact hedge

include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- Let `s.toBraid` satisfy `TranscriptInv D` for a transcript `T`, `s` satisfy `Ct1AckInv`, and
the second stage of `ops` be that of `P`. Delivering the message `msg` recorded by the peer of
`party` at index `n` through `recvWith auth (idealOps ops s)` succeeds with a result `r` that
reports `msg.epoch - 1` and outputs only the key recorded by the peer, which is the transcript key
of its epoch. After translation, the output key and new state of `r` are those of a `DeliveryEdge`;
the new state agrees with `T`, satisfies `PartyCt1Ack` with the messages recorded by `party`, and
has epoch at least `msg.epoch`. -/
theorem recvWith_ideal_outcome
    {ops : Ops P} (h2 : ∀ t, ops.encaps2 t = P.det.encaps2Det)
    {ik : InitKey} {T : ℕ → Braid.EpochTranscript P.toBraid}
    {s : GameState P AuthState} (hT : Braid.TranscriptInv (P := P.toBraid) auth D ik T
      s.toBraid) (hack : Ct1AckInv s)
    (party : Bool) {n : ℕ} {msg : Message P.Sym} {tsnd : ℕ}
    (hentry : s.messagesAt (!party) n = some (msg, tsnd)) :
    ∃ r : RecvResult P AuthState,
      recvWith auth (idealOps ops s) (s.stateAt party) msg = .ok r ∧
      r.receivingEpoch = msg.epoch - 1 ∧
      (∃ trep, DeliveryEdge auth s party msg ⟨trep, r.outputKey, r.state.toBraid⟩) ∧
      Braid.LocalPayloadInv (P := P.toBraid) auth ik T r.state.toBraid ∧
      msg.epoch ≤ r.state.epoch ∧
      (∀ e key, r.outputKey = some (e, key) →
        s.toBraid.keysAt (!party) e = some key ∧
        ∃ es ct1 k, (T e).encaps1 = some (es, ct1, k) ∧ key = P.kdfOK k e) ∧
      PartyCt1Ack r.state (s.messagesAt party) := by
  have hentry' := GameState.toBraid_messagesAt_eq_some hentry
  have hPayload := hT.messages (!party) n _ tsnd hentry'
  have hLocal := hT.local (P := P.toBraid) auth party
  rw [GameState.toBraid_stateAt] at hLocal
  have hpos := hT.control.epochKnowledge.keyPrefix.pos party
  rw [GameState.toBraid_stateAt, PartyState.toBraid_epoch] at hpos
  by_cases hcell : ∃ core dec chunk, s.stateAt party = .ekSentCt1Received core dec ∧
      msg = ⟨core.ep, .ct2 chunk⟩
  · -- The `ct₂` chunk of the current epoch: the decoder of the transcript's `ct₂ ‖ tag` grows, or
    -- completes and the generator outputs the peer's key, which ratchets the authenticator to the
    -- state the tag was computed with.
    obtain ⟨core, dec, chunk, hst, rfl⟩ := hcell
    have hgen : (s.toBraid.stateAt party).controlPosition.isGenerator = true := by
      rw [GameState.toBraid_stateAt, hst]; rfl
    have hpeerKey := Braid.generator_peer_key (P := P.toBraid) auth hT party hgen
    simp only [GameState.toBraid_stateAt, hst, PartyState.toBraid, Braid.State.epoch]
      at hpeerKey
    have hparty : generatorOf core.ep = party := by
      have hRole := hT.control.role party
      rw [hgen, GameState.toBraid_stateAt, hst] at hRole
      simp only [PartyState.toBraid, Braid.State.epoch] at hRole
      have h := of_decide_eq_true hRole.symm
      cases party
      · simp only [Bool.false_eq_true, ↓reduceIte] at h
        exact decide_eq_false (by omega)
      · exact decide_eq_true h
    rw [hst] at hLocal hpos ⊢
    simp only [PartyState.epoch] at hpos
    simp only [PartyState.toBraid, Braid.LocalPayloadInv] at hLocal
    obtain ⟨ha, pk, es, key, hkp, hc, hrcv⟩ := hLocal
    simp only [Message.toBraid, Braid.MessagePayloadInv] at hPayload
    obtain ⟨pk', sk', es', ct1', key', i, hkp', hc', hchunk⟩ := hPayload
    obtain ⟨rfl, hsk⟩ : pk = pk' ∧ core.sk = sk' := by simpa using hkp.symm.trans hkp'
    obtain ⟨rfl, hc1, rfl⟩ : es = es' ∧ core.c1 = ct1' ∧ key = key' := by
      have heq := Option.some.inj (hc.symm.trans hc')
      exact ⟨congrArg Prod.fst heq, congrArg (fun x => x.2.1) heq,
        congrArg (fun x => x.2.2) heq⟩
    rw [← hc1] at hchunk
    have hch := Option.some.inj hchunk
    have hC := hCt2Sound.received_addChunk hrcv i
    erw [← hch] at hC
    obtain ⟨hrcv', hnone | hsome⟩ := hC
    · refine ⟨⟨core.ep - 1, none, .ekSentCt1Received core (P.decCt2.addChunk dec chunk)⟩, ?_,
        rfl, ⟨core.ep - 1, Or.inl ?_⟩, ⟨ha, pk, es, key, hkp, hc, hrcv'⟩, le_rfl,
        (fun e k h => by cases h), partyCt1Ack_of_step (hack party) (by rw [hst]; exact le_rfl)
          fun core' dec' h => Or.inl ⟨core, _, rfl, by rw [hst] at h; cases h; rfl⟩⟩
      · rw [recvWith_ekSentCt1Received_ct2, hnone]
      rw [GameState.toBraid_stateAt, hst]
      exact Braid.ReceiveEdge.ct2Chunk _ _ _ _ _ _ hnone
    · -- The decoder completes to the transcript's `ct₂ ‖ tag`.
      set ct2 := P.toBraid.hEnc2.encaps2Det es
        (P.toBraid.inc.toHeader pk) (P.toBraid.inc.toVector pk) with hct2
      have hlookup : (idealOps ops s).completeKey core.ep core.sk core.c1 ct2 =
          some (P.kdfOK key core.ep) := by
        simp only [idealOps, hparty]
        have := hpeerKey es core.c1 key hc
        simpa [Braid.GameState.keysAt, GameState.keysAt, GameState.toBraid] using this
      have hauth : Braid.transcriptAuth (P := P.toBraid) auth ik T core.ep =
          auth.update core.authSt core.ep (P.kdfOK key core.ep) := by
        obtain ⟨m, hm⟩ : ∃ m, core.ep = m + 1 := ⟨core.ep - 1, by omega⟩
        rw [ha, hm]
        simp only [Braid.transcriptAuth, Nat.add_sub_cancel]
        rw [hm] at hc
        simp only [hc]
      have hrecv : recvCt2With auth (idealOps ops s).completeKey core ct2
          (auth.macCiphertext (Braid.transcriptAuth (P := P.toBraid) auth ik T core.ep) core.ep
            (core.c1, ct2)) =
          some (⟨core.ep + 1, auth.update core.authSt core.ep (P.kdfOK key core.ep)⟩,
            (core.ep, P.kdfOK key core.ep)) := by
        simp [recvCt2With, hlookup, ← hauth, auth.verifyCiphertext_correct]
      refine ⟨⟨core.ep - 1, some (core.ep, P.kdfOK key core.ep),
        .noHeaderReceived ⟨core.ep + 1, auth.update core.authSt core.ep (P.kdfOK key core.ep)⟩
          (P.decHdr.empty)⟩, ?_, rfl, ⟨core.ep - 1, Or.inl ?_⟩, ?_, Nat.le_succ _, ?_,
        partyCt1Ack_of_step (hack party) (by rw [hst]; exact Nat.le_succ _)
          fun core' dec' h => Or.inr (by rw [hst] at h; cases h; exact Nat.lt_succ_self _)⟩
      · simp only [recvWith_ekSentCt1Received_ct2, hsome]
        erw [hrecv]
      · rw [GameState.toBraid_stateAt, hst]
        refine Braid.ReceiveEdge.ct2Done _ _ _ _ _ _ _ _ _ hsome ?_
        rw [← hauth]
        exact auth.verifyCiphertext_correct _ _ _
      · simp only [PartyState.toBraid, Braid.LocalPayloadInv, Nat.add_sub_cancel]
        refine ⟨hauth.symm, ?_⟩
        cases (T (core.ep + 1)).keypair with
        | none => trivial
        | some kp => exact P.decHdr.received_empty P.ecpHdr _
      · intro e k h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hpeerKey es core.c1 key hc, es, core.c1, key, hc, rfl⟩
  · -- Every other delivery is received by `recv`.
    rw [recvWith_eq_recv_of_real auth (idealOps ops s) _ _ (fun t => h2 t)
      (fun core dec chunk hst hmsg => hcell ⟨core, dec, chunk, hst, hmsg⟩)]
    obtain ⟨r, hr, hnone, hrep, hLocalNew, hep, trep, hedge⟩ :=
      recv_recorded_outcome auth hHdrSound hEkSound hCt1Sound hT hack party hentry hcell
    refine ⟨r, hr, hrep, ⟨trep, by rw [hnone]; exact hedge⟩, hLocalNew, hep,
      (fun e k h => by rw [hnone] at h; cases h), partyCt1Ack_recv auth (hack party) hr⟩

include hCt2Sound in
/-- Let `s.toBraid` satisfy `TranscriptInv D` for a transcript `T`, the second stage of `ops` be
that of `P`, and decapsulation of the samples recorded in `T` at `party`'s epoch derive the
transcript key. Then delivering a message recorded by the peer of `party` through
`recvWith auth (idealOps ops s)` gives the result of `recv`. -/
theorem recvWith_idealOps_eq_recv
    (ops : Ops P) (h2 : ∀ t, ops.encaps2 t = P.det.encaps2Det)
    {ik : InitKey} {T : ℕ → Braid.EpochTranscript P.toBraid}
    {s : GameState P AuthState} (hT : Braid.TranscriptInv (P := P.toBraid) auth D ik T
      s.toBraid)
    (party : Bool) {n : ℕ} {msg : Message P.Sym} {tsnd : ℕ}
    (hentry : s.messagesAt (!party) n = some (msg, tsnd))
    (hdec : ∀ pk sk es ct1 key,
      (T (s.toBraid.stateAt party).epoch).keypair = some (pk, sk) →
      (T (s.toBraid.stateAt party).epoch).encaps1 = some (es, ct1, key) →
      Braid.decapsEpochKey (s.toBraid.stateAt party).epoch pk sk es ct1 =
        some (P.kdfOK key (s.toBraid.stateAt party).epoch)) :
    recvWith auth (idealOps ops s) (s.stateAt party) msg = recv P auth (s.stateAt party) msg := by
  refine recvWith_eq_recv_of_completeKey auth _ _ _ h2 ?_
  intro core dec chunk c2 tag hst hmsg hdecoded
  subst hmsg
  obtain ⟨hparty, pk, es, key, hkp, hc, hkey, hpayload⟩ :=
    ct2_cell_transcript auth hCt2Sound hT party hst hentry
  obtain rfl := hpayload c2 tag hdecoded
  rw [GameState.toBraid_stateAt, hst] at hdec
  simp only [PartyState.toBraid, Braid.State.epoch] at hdec
  have h := hdec pk core.sk es core.c1 key hkp hc
  simp only [idealOps, hparty]
  rw [show (P.det.decapsDet core.sk (P.det.splitC.symm (core.c1,
      P.det.encaps2Det es (P.det.toHeader pk) (P.det.toVector pk)))).map
        (fun k => P.kdfOK k core.ep) =
      Braid.decapsEpochKey core.ep pk core.sk es core.c1 from rfl, h]
  simpa [toBraid_keysAt, GameState.keysAt] using hkey

end Receive

/-! ### Preservation by the correctness queries of an ideal instance -/

section Preservation

variable [DecidableEq P.EpochKey]

/-- A send query of `party` adds one to the sender's counter. -/
private theorem countAt_sendUpdate (s : GameState P AuthState) (party who : Bool)
    (r : SendResult P AuthState) :
    (sendUpdate s party r).countAt who = s.countAt who + if who = party then 1 else 0 := by
  cases party <;> cases who <;> rcases hkey : r.outputKey with _ | ⟨e, key⟩ <;>
    simp [sendUpdate, SCKAScheme.sendAUpdate, SCKAScheme.sendBUpdate, GameState.countAt, hkey]

/-- A receive query keeps both counters. -/
private theorem countAt_recvUpdate (s : GameState P AuthState) (party who : Bool) (tsnd : ℕ)
    (r : RecvResult P AuthState) (trcv : ℕ) :
    (recvUpdate s party tsnd r trcv).countAt who = s.countAt who := by
  cases party <;> cases who <;> rcases hkey : r.outputKey with _ | ⟨e, key⟩ <;>
    simp [recvUpdate, SCKAScheme.recvAUpdate, SCKAScheme.recvBUpdate, GameState.countAt, hkey]

/-- A send of `party` through `sendWith auth ops`, with `ops` possible at the sender's state,
preserves `Ct1AckInv`. -/
theorem ct1AckInv_sendUpdate {ops : Ops P} {s : GameState P AuthState} (party : Bool)
    (hposs : OpsPossibleAt ops (s.stateAt party)) (hack : Ct1AckInv s)
    {r : SendResult P AuthState} (hr : r ∈ support (sendWith auth ops (s.stateAt party))) :
    Ct1AckInv (sendUpdate s party r) := by
  refine ct1AckInv_of_update party hack (by simp) (by simp) ?_
  rw [stateAt_sendUpdate, messagesAt_sendUpdate, ite_eq_left rfl, ite_eq_left rfl]
  exact partyCt1Ack_send auth (hack party) (sendWith_mem_support_send auth hposs hr) _ _

/-- A receive of `party` whose new state satisfies `PartyCt1Ack` with the messages of `party`
preserves `Ct1AckInv`. -/
theorem ct1AckInv_recvUpdate {s : GameState P AuthState} (party : Bool) (hack : Ct1AckInv s)
    {tsnd : ℕ} {r : RecvResult P AuthState} {trcv : ℕ}
    (h : PartyCt1Ack r.state (s.messagesAt party)) :
    Ct1AckInv (recvUpdate s party tsnd r trcv) := by
  refine ct1AckInv_of_update party hack (by simp) (by simp) ?_
  rw [stateAt_recvUpdate, messagesAt_recvUpdate, ite_eq_left rfl]
  exact h

/-- A send of `party` through `sendWith auth ops` with possible `ops` preserves `Inv`. -/
private theorem Inv_sendUpdate {ops : Ops P} {s : GameState P AuthState}
    (party : Bool) (hposs : OpsPossibleAt ops (s.stateAt party)) (hs : Inv auth s)
    {r : SendResult P AuthState} (hr : r ∈ support (sendWith auth ops (s.stateAt party))) :
    Inv auth (sendUpdate s party r) := by
  classical
  obtain ⟨⟨ik, T, hT⟩, hack, hcount⟩ := hs
  have hedge : Braid.SendEdge (P := P.toBraid) auth (s.toBraid.stateAt party)
    r.toBraid := by
    rw [GameState.toBraid_stateAt]
    exact sendEdge_toBraid auth (sendWith_mem_support_send auth hposs hr)
  have hCP := Braid.controlInv_statePairInv_sendUpdate (P := P.toBraid) auth ⟨hT.control,
    hT.statePair⟩
    party hedge
  have hc := Braid.sendUpdate_correct_of_transcriptInv (P := P.toBraid) auth hT party hedge
  have heq := Braid.sendUpdate_eq_successor_of_correct s.toBraid party r.toBraid
    hT.correct hc
  refine ⟨⟨ik, ?_⟩, ct1AckInv_sendUpdate auth party hposs hack hr, ?_⟩
  · rw [toBraid_sendUpdate, heq]
    exact Braid.send_preserves_transcript (P := P.toBraid) auth hT party hedge (heq ▸ hCP)
  · intro who
    rw [countAt_sendUpdate, toBraid_sendUpdate, Braid.stateAt_sendUpdate]
    have h := hcount who
    by_cases hwho : who = party
    · subst hwho
      simp only [↓reduceIte]
      have := Braid.SendEdge.sent_le (P := P.toBraid) auth hedge
      omega
    · simp only [ite_eq_right hwho, add_zero]
      exact h


include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- Let the second stage of `ops` be that of `P`. A successful receive by `party` of the message
recorded by the peer at index `n`, through `recvWith auth (idealOps ops s)`, keeps the game state
sample-consistent with the same initial key and transcript, and its output key and translated new
state are those of a Braid receive edge from the translated state of `party`. -/
theorem transcriptInv_recvUpdate_ideal
    {ops : Ops P} (h2 : ∀ t, ops.encaps2 t = P.det.encaps2Det)
    {ik : InitKey} {T : ℕ → Braid.EpochTranscript P.toBraid} {s : GameState P AuthState}
    (hT : Braid.TranscriptInv (P := P.toBraid) auth (fun _ _ _ _ _ _ => True) ik T s.toBraid)
    (hack : Ct1AckInv s) (party : Bool) {n : ℕ} {msg : Message P.Sym} {tsnd : ℕ}
    (hentry : s.messagesAt (!party) n = some (msg, tsnd)) {r : RecvResult P AuthState}
    (hr : recvWith auth (idealOps ops s) (s.stateAt party) msg = .ok r) :
    Braid.TranscriptInv (P := P.toBraid) auth (fun _ _ _ _ _ _ => True) ik T
        (recvUpdate s party tsnd r r.receivingEpoch).toBraid ∧
      Ct1AckInv (recvUpdate s party tsnd r r.receivingEpoch) ∧
      ∃ msg' trep, Braid.ReceiveEdge (P := P.toBraid) auth (s.toBraid.stateAt party) msg'
        ⟨trep, r.outputKey, r.state.toBraid⟩ := by
  obtain ⟨r', hr', hrep, ⟨trep, hedge⟩, hLocalNew, hepoch, hkeys, hpack⟩ :=
    recvWith_ideal_outcome auth hHdrSound hEkSound hCt1Sound hCt2Sound h2 hT hack party hentry
  obtain rfl : r = r' := by
    rw [hr'] at hr
    exact (Except.ok.inj hr).symm
  have hedge' : ∃ msg', Braid.ReceiveEdge (P := P.toBraid) auth (s.toBraid.stateAt party) msg'
      ⟨trep, r.outputKey, r.state.toBraid⟩ := by
    rcases hedge with h | ⟨_, _, _, _, _, h⟩
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
  refine ⟨?_, ct1AckInv_recvUpdate party hack hpack, hedge'.imp fun _ h => ⟨trep, h⟩⟩
  have hkeys' : ∀ t key, r.outputKey = some (t, key) → s.toBraid.keysAt (!party) t = some key ∧
      ∃ es ct1 k, (T t).encaps1 = some (es, ct1, k) ∧ key = P.kdfOK k t ∧
        ∀ pk sk, (T t).keypair = some (pk, sk) → True := fun t key h => by
    obtain ⟨hpeer, es, ct1, k, hc, hk⟩ := hkeys t key h
    exact ⟨hpeer, es, ct1, k, hc, hk, fun _ _ _ => trivial⟩
  have hmsgEpoch : msg.epoch ≤ r.state.toBraid.epoch := by
    rw [PartyState.toBraid_epoch]
    exact hepoch
  rw [toBraid_recvUpdate, hrep]
  rcases hedge with hedge | ⟨core, dec, chunk, hst, rfl, hedge⟩
  · have hT' := Braid.transcriptInv_recvUpdate (P := P.toBraid) auth hT party
      (GameState.toBraid_messagesAt_eq_some hentry) hedge
      (by rw [Message.toBraid_epoch]; exact hmsgEpoch) hLocalNew hkeys'
    rw [← Message.toBraid_epoch]
    exact hT'
  · -- The delivered plain vector chunk is received as an acknowledging chunk: relabel it, take
    -- the Braid step, and restore it.
    have hstB : (s.toBraidAck party n).stateAt party = s.toBraid.stateAt party := by
      cases party <;> rfl
    have hT' := Braid.transcriptInv_recvUpdate (P := P.toBraid) auth
      (transcriptInv_toBraidAck auth hT party n hst hentry) party (n := n)
      (msg := ⟨core.ep, .ekCt1Ack, some chunk⟩) (tsnd := tsnd)
      (by
        have hmsgF : s.toBraid.messagesAt (!party) n =
            some (⟨core.ep, .ek, some chunk⟩, tsnd) := by
          simp [hentry, Chunked.Message.toBraid]
        simp [GameState.toBraidAck, hmsgF])
      (by rw [hstB]; exact hedge)
      hmsgEpoch hLocalNew
      (fun t key h => by
        obtain ⟨h1, h2⟩ := hkeys' t key h
        exact ⟨by cases party <;> exact h1, h2⟩)
    have h := transcriptInv_restore auth party n hentry (by simp) hT'
    have hZ : (Braid.recvUpdate (s.toBraidAck party n) party tsnd
          ⟨trep, r.outputKey, r.state.toBraid⟩ (core.ep - 1)).setMessages (!party)
          (s.toBraid.messagesAt (!party)) =
        Braid.recvUpdate s.toBraid party tsnd r.toBraid (core.ep - 1) := by
      cases party <;> rcases hk : r.outputKey with _ | ⟨t, k⟩ <;>
        simp [Braid.recvUpdate, Braid.GameState.setMessages, GameState.toBraidAck,
          SCKAScheme.recvAUpdate, SCKAScheme.recvBUpdate, Chunked.RecvResult.toBraid, hk,
          Braid.GameState.messagesAt]
    rw [hZ] at h
    exact h

include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- Let the second stage of `ops` be that of `P`. A successful receive by `party` of the message
recorded by the peer at index `n`, through `recvWith auth (idealOps ops s)`, preserves `Inv`. -/
private theorem Inv_recvUpdate
    {ops : Ops P} (h2 : ∀ t, ops.encaps2 t = P.det.encaps2Det)
    {s : GameState P AuthState} (hs : Inv auth s) (party : Bool) {n : ℕ} {msg : Message P.Sym}
    {tsnd : ℕ} (hentry : s.messagesAt (!party) n = some (msg, tsnd))
    {r : RecvResult P AuthState}
    (hr : recvWith auth (idealOps ops s) (s.stateAt party) msg = .ok r) :
    Inv auth (recvUpdate s party tsnd r r.receivingEpoch) := by
  obtain ⟨⟨ik, T, hT⟩, hack, hcount⟩ := hs
  obtain ⟨hT', hack', msg', trep, hedge⟩ := transcriptInv_recvUpdate_ideal auth hHdrSound
    hEkSound hCt1Sound hCt2Sound h2 hT hack party hentry hr
  refine ⟨⟨ik, T, hT'⟩, hack', fun who => ?_⟩
  rw [countAt_recvUpdate, toBraid_recvUpdate, Braid.stateAt_recvUpdate]
  have h := hcount who
  by_cases hwho : who = party
  · subst hwho
    simp only [↓reduceIte]
    have hpos := hT.control.epochKnowledge.keyPrefix.pos who
    have := Braid.ReceiveEdge.sent_eq (P := P.toBraid) auth hedge hpos
    dsimp only at this
    change r.state.toBraid.epoch - 1 + r.state.toBraid.sentInEpoch ≤ _
    omega
  · simp only [ite_eq_right hwho]
    exact h

/-- Let `I` be a predicate on game states and `s` a state with `I s` from which every possible
send of either party through `sendWith auth ops` leads to a state satisfying `I`, and every message
recorded by the peer of a party is accepted by `recvWith auth (idealOps ops s)` with a successor
satisfying `I`. Then every correctness query of `schemeWith auth (idealOps ops s) sampleInitKey`
from `s` leads to a state satisfying `I`. -/
theorem schemeWith_correctness_preserves (ops : Ops P) (I : GameState P AuthState → Prop)
    (s : GameState P AuthState) (hs : I s)
    (hsend : ∀ party r, r ∈ support (sendWith auth ops (s.stateAt party)) →
      I (sendUpdate s party r))
    (hrecv : ∀ party n msg tsnd, s.messagesAt (!party) n = some (msg, tsnd) →
      ∃ r, recvWith auth (idealOps ops s) (s.stateAt party) msg = .ok r ∧
        I (recvUpdate s party tsnd r r.receivingEpoch))
    (t : (SCKAScheme.sckaCorrectnessSpec (Message P.Sym)).Domain)
    (res : (SCKAScheme.sckaCorrectnessSpec (Message P.Sym)).Range t × GameState P AuthState)
    (hres : res ∈ support ((SCKAScheme.sckaCorrectnessImpl
      (schemeWith auth (idealOps ops s) sampleInitKey) t).run s)) : I res.2 := by
  have hS : ∀ party z, z ∈ support ((SCKAScheme.oracleSend
      (schemeWith auth (idealOps ops s) sampleInitKey) party ()).run s) → I z.2 := by
    intro party z hz
    obtain ⟨out, hout, rfl⟩ := (SCKAScheme.mem_support_oracleSend_run_iff _ s rfl party z).mp hz
    simp only [schemeWith, mem_support_bind_iff, mem_support_pure_iff] at hout
    obtain ⟨r, hr, rfl⟩ := hout
    rw [sendWith_idealOps] at hr
    exact hsend party r hr
  have hR : ∀ party n z, z ∈ support ((SCKAScheme.oracleRecv
      (schemeWith auth (idealOps ops s) sampleInitKey) party n).run s) → I z.2 := by
    intro party n z hz
    rcases (SCKAScheme.mem_support_oracleRecv_run_iff _ s rfl party n z).mp hz with
      ⟨-, rfl⟩ | ⟨ρ, tsnd, hentry, hrefuse, -⟩ | ⟨ρ, tsnd, keyOpt, trcv, st', hentry, hok, rfl⟩
    · exact hs
    · obtain ⟨r, hr, -⟩ := hrecv party _ _ _ hentry
      have hr' : recvWith auth (idealOps ops s) (if party then s.stA else s.stB) ρ = .ok r := hr
      simp [schemeWith, recvSCKAWith, hr'] at hrefuse
    · obtain ⟨r, hr, hI⟩ := hrecv party _ _ _ hentry
      have hr' : recvWith auth (idealOps ops s) (if party then s.stA else s.stB) ρ = .ok r := hr
      simp only [schemeWith, recvSCKAWith, hr', Option.some.injEq, Prod.mk.injEq] at hok
      obtain ⟨rfl, rfl, rfl⟩ := hok
      exact hI
  rcases t with ((((m | u) | u) | m) | m)
  · rw [SCKAScheme.mem_support_oracleUnif_run m s res hres]
    exact hs
  · exact hS true res hres
  · exact hS false res hres
  · exact hR true m res hres
  · exact hR false m res hres

include hHdrSound hEkSound hCt1Sound hCt2Sound in
/-- With sound stream decoders and possible `ops`, every correctness query of
`schemeWith auth (idealOps ops s) sampleInitKey` from `s` preserves `Inv auth`. -/
theorem idealCorrectness_preserves_at
    {ops : Ops P} (hops : OpsPossible P ops)
    (s : GameState P AuthState) (hs : Inv auth s)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message P.Sym)).Domain)
    (res : (SCKAScheme.sckaCorrectnessSpec (Message P.Sym)).Range t × GameState P AuthState)
    (hres : res ∈ support ((SCKAScheme.sckaCorrectnessImpl
      (schemeWith auth (idealOps ops s) sampleInitKey) t).run s)) : Inv auth res.2 :=
  schemeWith_correctness_preserves auth sampleInitKey ops (Inv auth) s hs
    (fun party _ hr => Inv_sendUpdate auth party (hops.at _) hs hr)
    (fun party _ _ _ hentry => by
      obtain ⟨r, hr, -⟩ := recvWith_ideal_outcome auth hHdrSound hEkSound hCt1Sound hCt2Sound
        hops.2.2 hs.1.choose_spec.choose_spec hs.2.1 party hentry
      exact ⟨r, hr, Inv_recvUpdate auth hHdrSound hEkSound hCt1Sound hCt2Sound hops.2.2 hs party
        hentry hr⟩)
    t res hres

end Preservation

end SPQR
