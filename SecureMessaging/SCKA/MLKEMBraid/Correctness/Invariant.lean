/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Correctness.EpochSafety.StatePair

/-!
# The transcript invariant of the Braid correctness game

An `EpochTranscript` records the key pair and the first-stage encapsulation sampled in an epoch.
`TranscriptConsistent T s` states that the game state `s` agrees with the transcript `T`: the
party states and the recorded messages carry the recorded samples (`LocalPayloadInv`,
`MessagePayloadInv`), decapsulation in a completed epoch gives the recorded key, and the output
keys are the transcript keys. `CorrectnessInv s` states that the correctness flag is false or
that `s` is consistent with some transcript.

The module also derives from the invariant the state of the peer of a party that is about to
sample: the peer of a key generator in `keysUnsampled` waits for the header, and the peer of an
encapsulator in `headerReceived` holds the recorded key pair.
-/

open OracleSpec OracleComp
open ErasureCodePayload.Streaming
open SCKAScheme.sckaCorrectnessSpec

namespace MLKEMBraid

variable {P : Parameters ProbComp} {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)

/-- The key pair and the first-stage encapsulation sampled in one epoch. -/
structure EpochTranscript (P : Parameters ProbComp) where
  /-- The key pair sampled in this epoch, if any. -/
  keypair : Option (P.PK × P.SK)
  /-- The first-stage encapsulation of this epoch, if any: the encapsulation state, the first
  ciphertext and the KEM key. -/
  encaps1 : Option (P.inc.St × P.inc.C₁ × P.K)

/-- The authenticator state after epoch `e` of the transcript. It starts from `auth.init ik 1`
and is updated with the epoch key of every epoch that has an encapsulation. -/
def transcriptAuth (ik : InitKey) (T : ℕ → EpochTranscript P) : ℕ → AuthState
  | 0 => auth.init ik 1
  | e + 1 =>
      match (T (e + 1)).encaps1 with
      | none => transcriptAuth ik T e
      | some (_, _, key) => auth.update (transcriptAuth ik T e) (e + 1) (P.kdfOK key (e + 1))

/-- Transcripts with the same encapsulation records through epoch `n` have the same
authenticator state after that epoch. -/
theorem transcriptAuth_congr {ik : InitKey} {T T' : ℕ → EpochTranscript P} (n : ℕ)
    (h : ∀ i, i ≤ n → (T' i).encaps1 = (T i).encaps1) :
    transcriptAuth auth ik T' n = transcriptAuth auth ik T n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hprev := ih fun i hi => h i (Nat.le_succ_of_le hi)
      rw [transcriptAuth, transcriptAuth, h (n + 1) le_rfl]
      cases (T (n + 1)).encaps1 <;> simp only [hprev]

/-- A party's state agrees with the transcript. Its authenticator is the transcript authenticator,
its keys and ciphertexts are the samples recorded for its epoch, its encoders encode the payloads
of that epoch, and its decoders hold chunks of them. -/
def LocalPayloadInv (ik : InitKey) (T : ℕ → EpochTranscript P) (st : State P AuthState) : Prop :=
  let encOK := fun {M : Type} (ecp : ErasureCodePayload M P.Sym)
      (payload : M) (enc : EncoderState M P.Sym) =>
      enc.ecp = ecp ∧ enc.payload = payload
  let decOK := fun {M : Type} (ecp : ErasureCodePayload M P.Sym)
      (payload : M) (dec : DecoderState M P.Sym) =>
      dec.ecp = ecp ∧ ∃ I : Finset (Fin ecp.ec.N),
        dec.chunks = ErasureCodePayload.payloadChunks ecp payload I
  match st with
  | .keysUnsampled e a =>
      a = transcriptAuth auth ik T (e - 1) ∧
        (T e).keypair = none ∧ (T e).encaps1 = none
  | .keysSampled e a sk vec enc =>
      a = transcriptAuth auth ik T (e - 1) ∧
        ∃ pk, (T e).keypair = some (pk, sk) ∧
          vec = P.inc.toVector pk ∧
          encOK P.ecpHdr
            (P.inc.toHeader pk,
              auth.macHeader (transcriptAuth auth ik T (e - 1)) e (P.inc.toHeader pk)) enc
  | .headerSent e a sk dec enc =>
      a = transcriptAuth auth ik T (e - 1) ∧
        ∃ pk encapsState ct1 key, (T e).keypair = some (pk, sk) ∧
          (T e).encaps1 = some (encapsState, ct1, key) ∧
          decOK P.ecpCt1 ct1 dec ∧ encOK P.ecpEk (P.inc.toVector pk) enc
  | .ct1Received e a sk ct1 enc =>
      a = transcriptAuth auth ik T (e - 1) ∧
        ∃ pk encapsState key, (T e).keypair = some (pk, sk) ∧
          (T e).encaps1 = some (encapsState, ct1, key) ∧
          encOK P.ecpEk (P.inc.toVector pk) enc
  | .ekSentCt1Received e a sk ct1 dec =>
      a = transcriptAuth auth ik T (e - 1) ∧
        ∃ pk encapsState key, (T e).keypair = some (pk, sk) ∧
          (T e).encaps1 = some (encapsState, ct1, key) ∧
          let ct2 := P.hEnc2.encaps2Det encapsState (P.inc.toHeader pk) (P.inc.toVector pk)
          decOK P.ecpCt2 (ct2, auth.macCiphertext (transcriptAuth auth ik T e) e (ct1, ct2)) dec
  | .noHeaderReceived e a dec =>
      a = transcriptAuth auth ik T (e - 1) ∧
        match (T e).keypair with
        | none => dec = DecoderState.empty P.ecpHdr
        | some (pk, _) => decOK P.ecpHdr
            (P.inc.toHeader pk,
              auth.macHeader (transcriptAuth auth ik T (e - 1)) e (P.inc.toHeader pk)) dec
  | .headerReceived e a hdr dec =>
      a = transcriptAuth auth ik T (e - 1) ∧
        (T e).encaps1 = none ∧
        ∃ pk sk, (T e).keypair = some (pk, sk) ∧
          hdr = P.inc.toHeader pk ∧ dec = DecoderState.empty P.ecpEk
  | .ct1Sampled e a hdr encapsState ct1 enc dec =>
      a = transcriptAuth auth ik T e ∧
        ∃ pk sk key, (T e).keypair = some (pk, sk) ∧
          (T e).encaps1 = some (encapsState, ct1, key) ∧
          hdr = P.inc.toHeader pk ∧
          encOK P.ecpCt1 ct1 enc ∧ decOK P.ecpEk (P.inc.toVector pk) dec
  | .ekReceivedCt1Sampled e a encapsState ct1 hdr vec enc =>
      a = transcriptAuth auth ik T e ∧
        ∃ pk sk key, (T e).keypair = some (pk, sk) ∧
          (T e).encaps1 = some (encapsState, ct1, key) ∧
          hdr = P.inc.toHeader pk ∧
          vec = P.inc.toVector pk ∧ encOK P.ecpCt1 ct1 enc
  | .ct1Acknowledged e a hdr encapsState ct1 dec =>
      a = transcriptAuth auth ik T e ∧
        ∃ pk sk key, (T e).keypair = some (pk, sk) ∧
          (T e).encaps1 = some (encapsState, ct1, key) ∧
          hdr = P.inc.toHeader pk ∧ decOK P.ecpEk (P.inc.toVector pk) dec
  | .ct2Sampled e a enc =>
      a = transcriptAuth auth ik T e ∧
        ∃ pk sk encapsState ct1 key, (T e).keypair = some (pk, sk) ∧
          (T e).encaps1 = some (encapsState, ct1, key) ∧
          let ct2 := P.hEnc2.encaps2Det encapsState (P.inc.toHeader pk) (P.inc.toVector pk)
          encOK P.ecpCt2 (ct2, auth.macCiphertext (transcriptAuth auth ik T e) e (ct1, ct2)) enc

/-- A recorded message carries a chunk of the payload named by its type, computed from the
transcript of its epoch. A message of type `none` carries no data. -/
def MessagePayloadInv (ik : InitKey) (T : ℕ → EpochTranscript P) (msg : Message P.Sym) : Prop :=
  match msg.type with
  | .none => msg.data = none
  | .hdr =>
      ∃ pk sk i, (T msg.epoch).keypair = some (pk, sk) ∧
        msg.data = some (P.ecpHdr.encode
          (P.inc.toHeader pk,
            auth.macHeader (transcriptAuth auth ik T (msg.epoch - 1)) msg.epoch
              (P.inc.toHeader pk)) i)
  | .ek | .ekCt1Ack =>
      ∃ pk sk i, (T msg.epoch).keypair = some (pk, sk) ∧
        msg.data = some (P.ecpEk.encode (P.inc.toVector pk) i)
  | .ct1 =>
      ∃ encapsState ct1 key i, (T msg.epoch).encaps1 = some (encapsState, ct1, key) ∧
        msg.data = some (P.ecpCt1.encode ct1 i)
  | .ct2 =>
      ∃ pk sk encapsState ct1 key i, (T msg.epoch).keypair = some (pk, sk) ∧
        (T msg.epoch).encaps1 = some (encapsState, ct1, key) ∧
        let ct2 := P.hEnc2.encaps2Det encapsState (P.inc.toHeader pk) (P.inc.toVector pk)
        msg.data = some (P.ecpCt2.encode
          (ct2, auth.macCiphertext (transcriptAuth auth ik T msg.epoch) msg.epoch (ct1, ct2)) i)
  | .ct1Ack => False

/-- A message remains consistent with an extended transcript when its recorded samples are
preserved and its header and ciphertext authenticator states agree. Agreement at the message's
epoch is needed only when that epoch already has an encapsulation in the original transcript. -/
theorem MessagePayloadInv.transport {ik : InitKey} {T T' : ℕ → EpochTranscript P}
    {msg : Message P.Sym} (h : MessagePayloadInv auth ik T msg)
    (hkeypair : ∀ kp, (T msg.epoch).keypair = some kp →
      (T' msg.epoch).keypair = some kp)
    (hencaps : ∀ c, (T msg.epoch).encaps1 = some c →
      (T' msg.epoch).encaps1 = some c)
    (hprev : transcriptAuth auth ik T' (msg.epoch - 1) =
      transcriptAuth auth ik T (msg.epoch - 1))
    (hcurrent : ∀ c, (T msg.epoch).encaps1 = some c →
      transcriptAuth auth ik T' msg.epoch = transcriptAuth auth ik T msg.epoch) :
    MessagePayloadInv auth ik T' msg := by
  cases htype : msg.type <;> simp only [MessagePayloadInv, htype] at h ⊢
  case none => exact h
  case hdr =>
    obtain ⟨pk, sk, i, hk, hd⟩ := h
    exact ⟨pk, sk, i, hkeypair _ hk, by rw [hprev]; exact hd⟩
  case ek =>
    obtain ⟨pk, sk, i, hk, hd⟩ := h
    exact ⟨pk, sk, i, hkeypair _ hk, hd⟩
  case ekCt1Ack =>
    obtain ⟨pk, sk, i, hk, hd⟩ := h
    exact ⟨pk, sk, i, hkeypair _ hk, hd⟩
  case ct1 =>
    obtain ⟨es, ct1, key, i, hc, hd⟩ := h
    exact ⟨es, ct1, key, i, hencaps _ hc, hd⟩
  case ct2 =>
    obtain ⟨pk, sk, es, ct1, key, i, hk, hc, hd⟩ := h
    exact ⟨pk, sk, es, ct1, key, i, hkeypair _ hk, hencaps _ hc,
      by rw [hcurrent _ hc]; exact hd⟩

/-- The epoch-`e` key derived by decapsulating, with the key pair `(pk, sk)`, the ciphertext of
the staged encapsulation `(encapsState, ct1)`, or `none` if decapsulation fails. -/
def decapsEpochKey (e : ℕ) (pk : P.PK) (sk : P.SK) (encapsState : P.inc.St) (ct1 : P.inc.C₁) :
    Option P.EpochKey :=
  (P.hDet.decapsDet sk (P.inc.splitC.symm (ct1,
    P.hEnc2.encaps2Det encapsState (P.inc.toHeader pk) (P.inc.toVector pk)))).map
      (fun k => P.kdfOK k e)

/-- The game state `s` is consistent with the transcript `T`. -/
structure TranscriptConsistent (ik : InitKey) (T : ℕ → EpochTranscript P)
    (s : GameState P AuthState) : Prop where
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
  /-- A recorded encapsulation belongs to a positive epoch its encapsulator has completed. The
  epoch has a recorded key pair, and once the generator completes the epoch, decapsulation gives
  the recorded key. -/
  encaps : ∀ e encapsState ct1 key,
    (T e).encaps1 = some (encapsState, ct1, key) →
    0 < e ∧
      e ≤ (if e % 2 = 1 then s.stB else s.stA).completedEpoch ∧
      ∃ pk sk, (T e).keypair = some (pk, sk) ∧
        (e ≤ (if e % 2 = 1 then s.stA else s.stB).completedEpoch →
          decapsEpochKey e pk sk encapsState ct1 = some (P.kdfOK key e))
  /-- A's state agrees with the transcript. -/
  localA : LocalPayloadInv auth ik T s.stA
  /-- B's state agrees with the transcript. -/
  localB : LocalPayloadInv auth ik T s.stB
  /-- Every recorded message agrees with the transcript. -/
  messages : ∀ (party : Bool) n msg tsnd,
    (if party then s.msgA else s.msgB) n = some (msg, tsnd) →
      MessagePayloadInv auth ik T msg
  /-- Each party's output keys are the transcript keys of its completed epochs. -/
  keys : ∀ (party : Bool) e,
    (if party then s.keyA else s.keyB) e =
      if 0 < e ∧ e ≤ (if party then s.stA else s.stB).completedEpoch then
        (T e).encaps1.map (fun (_, _, key) => P.kdfOK key e)
      else none

/-- The state of either party agrees with the transcript. -/
theorem TranscriptConsistent.local {ik : InitKey} {T : ℕ → EpochTranscript P}
    {s : GameState P AuthState} (hT : TranscriptConsistent auth ik T s) (party : Bool) :
    LocalPayloadInv auth ik T (s.stateAt party) := by
  cases party
  · exact hT.localB
  · exact hT.localA

/-- Either the correctness flag is already false, or some transcript is consistent with the game
state. -/
def CorrectnessInv (ik : InitKey) (s : GameState P AuthState) : Prop :=
  s.correct = false ∨ ∃ T : ℕ → EpochTranscript P, TranscriptConsistent auth ik T s

/-- The initial game state is consistent with the empty transcript. -/
theorem transcriptConsistent_initGameState (ik : InitKey) :
    TranscriptConsistent auth ik (fun _ => { keypair := none, encaps1 := none })
      (SCKAScheme.initGameState (initA P auth ik) (initB P auth ik)) := by
  have hControl : ControlInv
      (SCKAScheme.initGameState (I := P.EpochKey) (Rho := Message P.Sym)
        (initA P auth ik) (initB P auth ik)) := by
    refine ⟨epochKnowledgeInv_initGameState auth ik,
      recordedReportInv_initGameState (initA P auth ik) (initB P auth ik), ?_, ?_, ?_⟩
    · simp [SCKAScheme.initGameState, initA, State.epoch]
    · simp [SCKAScheme.initGameState, initB, State.epoch]
    · intro party
      cases party <;>
        simp [PartyControl, SCKAScheme.initGameState, initA, initB, State.controlPosition,
          State.epoch]
  refine ⟨rfl, hControl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [StatePairInv, PairInv, SCKAScheme.initGameState, initA, initB, State.controlPosition,
      State.epoch, AllowedStatePair]
  · simp
  · simp
  · simp [LocalPayloadInv, SCKAScheme.initGameState, initA, transcriptAuth]
  · simp [LocalPayloadInv, SCKAScheme.initGameState, initB, transcriptAuth]
  · simp [SCKAScheme.initGameState]
  · intro party e
    cases party <;>
      simp [SCKAScheme.initGameState, initA, initB, State.completedEpoch, State.epoch]

/-! ### The peer of a sampling party -/

/-- The peer of a key generator in `keysUnsampled` waits for the header of the same epoch. -/
theorem PairInv.peer_of_keysUnsampled {st peer : State P AuthState}
    (h : PairInv st peer) (h' : PairInv peer st)
    (hpos : 0 < st.epoch) (hposP : 0 < peer.epoch)
    (hcross : st.epoch ≤ peer.completedEpoch + 1) (hcrossP : peer.epoch ≤ st.completedEpoch + 1)
    {e : ℕ} {a : AuthState} (hst : st = .keysUnsampled e a) :
    ∃ b dec, peer = .noHeaderReceived e b dec := by
  subst hst
  cases peer <;>
    simp [PairInv, AllowedStatePair, State.controlPosition, State.epoch,
      State.completedEpoch] at * <;>
    omega

/-- The peer of an encapsulator in `headerReceived` holds the key pair of the same epoch. -/
theorem PairInv.peer_of_headerReceived {st peer : State P AuthState}
    (h : PairInv st peer) (h' : PairInv peer st)
    (hpos : 0 < st.epoch) (hposP : 0 < peer.epoch)
    (hcross : st.epoch ≤ peer.completedEpoch + 1) (hcrossP : peer.epoch ≤ st.completedEpoch + 1)
    (hroles : st.epoch = peer.epoch →
      st.controlPosition.isGenerator = (!peer.controlPosition.isGenerator))
    {e : ℕ} {a : AuthState} {hdr : P.inc.PKheader} {dec : DecoderState P.inc.PKvector P.Sym}
    (hst : st = .headerReceived e a hdr dec) :
    ∃ b sk vec enc, peer = .keysSampled e b sk vec enc := by
  subst hst
  cases peer <;>
    simp [PairInv, AllowedStatePair, State.controlPosition, State.epoch,
      State.completedEpoch] at * <;>
    omega

/-- The epoch bounds and roles that `PairInv.peer_of_keysUnsampled` and
`PairInv.peer_of_headerReceived` need, for `party` and its peer. -/
theorem TranscriptConsistent.pairBounds {ik : InitKey} {T : ℕ → EpochTranscript P}
    {s : GameState P AuthState} (hT : TranscriptConsistent auth ik T s) (party : Bool) :
    let st := if party then s.stA else s.stB
    let peer := if party then s.stB else s.stA
    PairInv st peer ∧ PairInv peer st ∧ 0 < st.epoch ∧ 0 < peer.epoch ∧
      st.epoch ≤ peer.completedEpoch + 1 ∧ peer.epoch ≤ st.completedEpoch + 1 ∧
      (st.epoch = peer.epoch →
        st.controlPosition.isGenerator = (!peer.controlPosition.isGenerator)) := by
  have hE := hT.control.epochKnowledge
  cases party
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨hT.statePair.2, hT.statePair.1, hE.keyPrefix.posB, hE.keyPrefix.posA, hE.epochB_le,
      hE.epochA_le, fun heq => ?_⟩
    rw [roles_opposite hT.control heq.symm, Bool.not_not]
  · simp only [↓reduceIte]
    exact ⟨hT.statePair.1, hT.statePair.2, hE.keyPrefix.posA, hE.keyPrefix.posB, hE.epochA_le,
      hE.epochB_le, roles_opposite hT.control⟩

/-- When a party is about to sample its key pair, its peer is waiting for the header of the same
epoch. -/
theorem peer_noHeaderReceived_of_keysUnsampled {ik : InitKey} {T : ℕ → EpochTranscript P}
    {s : GameState P AuthState} (hT : TranscriptConsistent auth ik T s)
    (party : Bool) {e : ℕ} {a : AuthState}
    (hst : (if party then s.stA else s.stB) = .keysUnsampled e a) :
    ∃ b dec, (if party then s.stB else s.stA) = .noHeaderReceived e b dec := by
  obtain ⟨h, h', hpos, hposP, hcross, hcrossP, -⟩ := hT.pairBounds auth party
  exact PairInv.peer_of_keysUnsampled h h' hpos hposP hcross hcrossP hst

/-- When a party is about to encapsulate against a received header, the epoch has a recorded key
pair, the header is that key pair's header, and the peer holds its secret key and vector. -/
theorem peer_keysSampled_of_headerReceived {ik : InitKey} {T : ℕ → EpochTranscript P}
    {s : GameState P AuthState} (hT : TranscriptConsistent auth ik T s)
    (party : Bool) {e : ℕ} {a : AuthState} {hdr : P.inc.PKheader}
    {dec : DecoderState P.inc.PKvector P.Sym}
    (hst : (if party then s.stA else s.stB) = .headerReceived e a hdr dec) :
    ∃ pk sk b enc,
      (T e).keypair = some (pk, sk) ∧
      (if party then s.stB else s.stA) = .keysSampled e b sk (P.inc.toVector pk) enc ∧
      hdr = P.inc.toHeader pk := by
  obtain ⟨h, h', hpos, hposP, hcross, hcrossP, hroles⟩ := hT.pairBounds auth party
  obtain ⟨b, sk', vec, enc, hpeer⟩ :=
    PairInv.peer_of_headerReceived h h' hpos hposP hcross hcrossP hroles hst
  have hLs : LocalPayloadInv auth ik T (if party then s.stA else s.stB) := by
    cases party
    · exact hT.localB
    · exact hT.localA
  have hLp : LocalPayloadInv auth ik T (if party then s.stB else s.stA) := by
    cases party
    · exact hT.localA
    · exact hT.localB
  rw [hst] at hLs
  rw [hpeer] at hLp
  obtain ⟨-, -, pk, sk, hkp, hhdr, -⟩ := hLs
  obtain ⟨-, pk', hkp', hvec, -⟩ := hLp
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hkp.symm.trans hkp'))
  exact ⟨pk, sk, b, enc, hkp, by rw [hpeer, hvec], hhdr⟩

/-! ### Transcript consistency of states that agree on the relevant fields -/

/-- A state is consistent with the same transcript when its epochs, completed epochs and key
tables are unchanged, its local states and recorded messages agree with the transcript, and its
correctness flag, control invariant and pair invariant hold. -/
theorem TranscriptConsistent.of_fields {ik : InitKey} {T : ℕ → EpochTranscript P}
    {s s' : GameState P AuthState} (hT : TranscriptConsistent auth ik T s)
    (hc : s'.correct = true) (hC : ControlInv s') (hP : StatePairInv s')
    (hA : s'.stA.epoch = s.stA.epoch) (hB : s'.stB.epoch = s.stB.epoch)
    (hcA : s'.stA.completedEpoch = s.stA.completedEpoch)
    (hcB : s'.stB.completedEpoch = s.stB.completedEpoch)
    (hLA : LocalPayloadInv auth ik T s'.stA) (hLB : LocalPayloadInv auth ik T s'.stB)
    (hMessages : ∀ (party : Bool) n msg tsnd,
      (if party then s'.msgA else s'.msgB) n = some (msg, tsnd) →
        MessagePayloadInv auth ik T msg)
    (hkA : s'.keyA = s.keyA) (hkB : s'.keyB = s.keyB) :
    TranscriptConsistent auth ik T s' := by
  obtain ⟨-, -, -, h0k, h0e, hKeypair, hEncaps, -, -, -, hKeys⟩ := hT
  refine ⟨hc, hC, hP, h0k, h0e, ?_, ?_, hLA, hLB, hMessages, ?_⟩
  · intro e pk sk hk
    obtain ⟨h0, hle⟩ := hKeypair e pk sk hk
    have h1 : (if e % 2 = 1 then s'.stA else s'.stB).epoch =
        (if e % 2 = 1 then s.stA else s.stB).epoch := by
      split_ifs <;> assumption
    exact ⟨h0, h1 ▸ hle⟩
  · intro e es ct1 key hc'
    obtain ⟨h0, hle, pk, sk, hkp, hdec⟩ := hEncaps e es ct1 key hc'
    have h1 : (if e % 2 = 1 then s'.stB else s'.stA).completedEpoch =
        (if e % 2 = 1 then s.stB else s.stA).completedEpoch := by
      split_ifs <;> assumption
    have h2 : (if e % 2 = 1 then s'.stA else s'.stB).completedEpoch =
        (if e % 2 = 1 then s.stA else s.stB).completedEpoch := by
      split_ifs <;> assumption
    refine ⟨h0, by rw [h1]; exact hle, pk, sk, hkp, fun h => hdec ?_⟩
    rw [← h2]
    exact h
  · intro party e
    have hK := hKeys party e
    cases party
    · simp only [Bool.false_eq_true, ↓reduceIte] at hK ⊢
      rw [hkB, hcB]
      exact hK
    · simp only [↓reduceIte] at hK ⊢
      rw [hkA, hcA]
      exact hK

/-- Party-indexed form of `TranscriptConsistent.of_fields`. -/
theorem TranscriptConsistent.of_party {ik : InitKey} {T : ℕ → EpochTranscript P}
    {s s' : GameState P AuthState} (hT : TranscriptConsistent auth ik T s)
    (hc : s'.correct = true) (hC : ControlInv s') (hP : StatePairInv s')
    (he : ∀ party, (s'.stateAt party).epoch = (s.stateAt party).epoch)
    (hcomp : ∀ party, (s'.stateAt party).completedEpoch = (s.stateAt party).completedEpoch)
    (hLocal : ∀ party, LocalPayloadInv auth ik T (s'.stateAt party))
    (hMessages : ∀ party n msg tsnd, s'.messagesAt party n = some (msg, tsnd) →
      MessagePayloadInv auth ik T msg)
    (hKeys : ∀ party, s'.keysAt party = s.keysAt party) :
    TranscriptConsistent auth ik T s' :=
  hT.of_fields auth hc hC hP (he true) (he false) (hcomp true) (hcomp false)
    (hLocal true) (hLocal false) hMessages (hKeys true) (hKeys false)

/-- `TranscriptConsistent.of_fields` when the recorded-message tables are unchanged. -/
theorem TranscriptConsistent.of_eq {ik : InitKey} {T : ℕ → EpochTranscript P}
    {s s' : GameState P AuthState} (hT : TranscriptConsistent auth ik T s)
    (hc : s'.correct = true) (hC : ControlInv s') (hP : StatePairInv s')
    (hA : s'.stA.epoch = s.stA.epoch) (hB : s'.stB.epoch = s.stB.epoch)
    (hcA : s'.stA.completedEpoch = s.stA.completedEpoch)
    (hcB : s'.stB.completedEpoch = s.stB.completedEpoch)
    (hLA : LocalPayloadInv auth ik T s'.stA) (hLB : LocalPayloadInv auth ik T s'.stB)
    (hmA : s'.msgA = s.msgA) (hmB : s'.msgB = s.msgB)
    (hkA : s'.keyA = s.keyA) (hkB : s'.keyB = s.keyB) :
    TranscriptConsistent auth ik T s' := by
  refine hT.of_fields auth hc hC hP hA hB hcA hcB hLA hLB ?_ hkA hkB
  intro party n msg tsnd hmsg
  apply hT.messages party n msg tsnd
  cases party
  · simpa [hmB] using hmsg
  · simpa [hmA] using hmsg

end MLKEMBraid
