/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Correctness.EpochSafety.Preservation

/-!
# The transcript invariant of the Braid correctness game

An `EpochTranscript` records the key pair and the first-stage encapsulation sampled in an epoch.
`TranscriptConsistent T s` states that the game state `s` agrees with the transcript `T`: the
party states and recorded messages carry the recorded samples, decapsulation in a completed epoch
gives the recorded key, and the output keys are the transcript keys. `CorrectnessInv s` states
that the correctness flag is false or that `s` is consistent with some transcript.
-/

open OracleSpec OracleComp
open ErasureCodePayload.Streaming
open SCKAScheme.sckaCorrectnessSpec

namespace MLKEMBraid

variable (P : Parameters ProbComp) {InitKey AuthState : Type}
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
def transcriptAuth
    (ik : InitKey) (T : ℕ → EpochTranscript P) : ℕ → AuthState
  | 0 => auth.init ik 1
  | e + 1 =>
      match (T (e + 1)).encaps1 with
      | none => transcriptAuth ik T e
      | some (_, _, key) => auth.update (transcriptAuth ik T e)
          (e + 1) (P.kdfOK key (e + 1))

/-- A party's state agrees with the transcript. Its authenticator is the transcript authenticator,
its keys and ciphertexts are the samples recorded for its epoch, its encoders encode the payloads
of that epoch, and its decoders hold chunks of them. -/
def LocalPayloadInv
    (ik : InitKey) (T : ℕ → EpochTranscript P)
    (st : State P AuthState) : Prop :=
  let encOK := fun {M : Type} (ecp : ErasureCodePayload M P.Sym)
      (payload : M) (enc : EncoderState M P.Sym) =>
      enc.ecp = ecp ∧ enc.payload = payload
  let decOK := fun {M : Type} (ecp : ErasureCodePayload M P.Sym)
      (payload : M) (dec : DecoderState M P.Sym) =>
      dec.ecp = ecp ∧ ∃ I : Finset (Fin ecp.ec.N),
        dec.chunks = ErasureCodePayload.payloadChunks ecp payload I
  match st with
  | .keysUnsampled e a =>
      a = transcriptAuth P auth ik T (e - 1) ∧
        (T e).keypair = none ∧ (T e).encaps1 = none
  | .keysSampled e a sk vec enc =>
      a = transcriptAuth P auth ik T (e - 1) ∧
        ∃ pk, (T e).keypair = some (pk, sk) ∧
          vec = P.inc.toVector pk ∧
          encOK P.ecpHdr
            (P.inc.toHeader pk,
              auth.macHeader (transcriptAuth P auth ik T (e - 1))
                e (P.inc.toHeader pk)) enc
  | .headerSent e a sk dec enc =>
      a = transcriptAuth P auth ik T (e - 1) ∧
        ∃ pk encapsState ct1 key, (T e).keypair = some (pk, sk) ∧
          (T e).encaps1 = some (encapsState, ct1, key) ∧
          decOK P.ecpCt1 ct1 dec ∧ encOK P.ecpEk (P.inc.toVector pk) enc
  | .ct1Received e a sk ct1 enc =>
      a = transcriptAuth P auth ik T (e - 1) ∧
        ∃ pk encapsState key, (T e).keypair = some (pk, sk) ∧
          (T e).encaps1 = some (encapsState, ct1, key) ∧
          encOK P.ecpEk (P.inc.toVector pk) enc
  | .ekSentCt1Received e a sk ct1 dec =>
      a = transcriptAuth P auth ik T (e - 1) ∧
        ∃ pk encapsState key, (T e).keypair = some (pk, sk) ∧
          (T e).encaps1 = some (encapsState, ct1, key) ∧
          let ct2 := P.hEnc2.encaps2Det encapsState
            (P.inc.toHeader pk) (P.inc.toVector pk)
          decOK P.ecpCt2
            (ct2, auth.macCiphertext (transcriptAuth P auth ik T e)
              e (ct1, ct2)) dec
  | .noHeaderReceived e a dec =>
      a = transcriptAuth P auth ik T (e - 1) ∧
        match (T e).keypair with
        | none => dec = DecoderState.empty P.ecpHdr
        | some (pk, _) => decOK P.ecpHdr
            (P.inc.toHeader pk,
              auth.macHeader (transcriptAuth P auth ik T (e - 1))
                e (P.inc.toHeader pk)) dec
  | .headerReceived e a hdr dec =>
      a = transcriptAuth P auth ik T (e - 1) ∧
        (T e).encaps1 = none ∧
        ∃ pk sk, (T e).keypair = some (pk, sk) ∧
          hdr = P.inc.toHeader pk ∧ dec = DecoderState.empty P.ecpEk
  | .ct1Sampled e a hdr encapsState ct1 enc dec =>
      a = transcriptAuth P auth ik T e ∧
        ∃ pk sk key, (T e).keypair = some (pk, sk) ∧
          (T e).encaps1 = some (encapsState, ct1, key) ∧
          hdr = P.inc.toHeader pk ∧
          encOK P.ecpCt1 ct1 enc ∧ decOK P.ecpEk (P.inc.toVector pk) dec
  | .ekReceivedCt1Sampled e a encapsState ct1 hdr vec enc =>
      a = transcriptAuth P auth ik T e ∧
        ∃ pk sk key, (T e).keypair = some (pk, sk) ∧
          (T e).encaps1 = some (encapsState, ct1, key) ∧
          hdr = P.inc.toHeader pk ∧
          vec = P.inc.toVector pk ∧ encOK P.ecpCt1 ct1 enc
  | .ct1Acknowledged e a hdr encapsState ct1 dec =>
      a = transcriptAuth P auth ik T e ∧
        ∃ pk sk key, (T e).keypair = some (pk, sk) ∧
          (T e).encaps1 = some (encapsState, ct1, key) ∧
          hdr = P.inc.toHeader pk ∧ decOK P.ecpEk (P.inc.toVector pk) dec
  | .ct2Sampled e a enc =>
      a = transcriptAuth P auth ik T e ∧
        ∃ pk sk encapsState ct1 key, (T e).keypair = some (pk, sk) ∧
          (T e).encaps1 = some (encapsState, ct1, key) ∧
          let ct2 := P.hEnc2.encaps2Det encapsState
            (P.inc.toHeader pk) (P.inc.toVector pk)
          encOK P.ecpCt2
            (ct2, auth.macCiphertext (transcriptAuth P auth ik T e)
              e (ct1, ct2)) enc

/-- A recorded message carries a chunk of the payload named by its type, computed from the
transcript of its epoch. A message of type `none` carries no data. -/
def MessagePayloadInv
    (ik : InitKey) (T : ℕ → EpochTranscript P)
    (msg : Message P.Sym) : Prop :=
  match msg.type with
  | .none => msg.data = none
  | .hdr =>
      ∃ pk sk i, (T msg.epoch).keypair = some (pk, sk) ∧
        msg.data = some (P.ecpHdr.encode
          (P.inc.toHeader pk,
            auth.macHeader (transcriptAuth P auth ik T (msg.epoch - 1))
              msg.epoch (P.inc.toHeader pk)) i)
  | .ek | .ekCt1Ack =>
      ∃ pk sk i, (T msg.epoch).keypair = some (pk, sk) ∧
        msg.data = some (P.ecpEk.encode (P.inc.toVector pk) i)
  | .ct1 =>
      ∃ encapsState ct1 key i, (T msg.epoch).encaps1 = some (encapsState, ct1, key) ∧
        msg.data = some (P.ecpCt1.encode ct1 i)
  | .ct2 =>
      ∃ pk sk encapsState ct1 key i, (T msg.epoch).keypair = some (pk, sk) ∧
        (T msg.epoch).encaps1 = some (encapsState, ct1, key) ∧
        let ct2 := P.hEnc2.encaps2Det encapsState
          (P.inc.toHeader pk) (P.inc.toVector pk)
        msg.data = some (P.ecpCt2.encode
          (ct2, auth.macCiphertext (transcriptAuth P auth ik T msg.epoch)
            msg.epoch (ct1, ct2)) i)
  | .ct1Ack => False

/-- The epoch-`e` key derived by decapsulating, with the key pair `(pk, sk)`, the ciphertext of the
staged encapsulation `(encapsState, ct1)`, or `none` if decapsulation fails. -/
def decapsEpochKey (e : ℕ) (pk : P.PK) (sk : P.SK) (encapsState : P.inc.St) (ct1 : P.inc.C₁) :
    Option P.EpochKey :=
  (P.hDet.decapsDet sk (P.inc.splitC.symm (ct1,
    P.hEnc2.encaps2Det encapsState (P.inc.toHeader pk) (P.inc.toVector pk)))).map
      (fun k => P.kdfOK k e)

/-- The game state `s` is consistent with the transcript `T`. -/
structure TranscriptConsistent
    (ik : InitKey) (T : ℕ → EpochTranscript P)
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
          decapsEpochKey P e pk sk encapsState ct1 = some (P.kdfOK key e))
  /-- A's state agrees with the transcript. -/
  localA : LocalPayloadInv P auth ik T s.stA
  /-- B's state agrees with the transcript. -/
  localB : LocalPayloadInv P auth ik T s.stB
  /-- Every recorded message agrees with the transcript. -/
  messages : ∀ (party : Bool) n msg tsnd,
    (if party then s.msgA else s.msgB) n = some (msg, tsnd) →
      MessagePayloadInv P auth ik T msg
  /-- Each party's output keys are the transcript keys of its completed epochs. -/
  keys : ∀ (party : Bool) e,
    (if party then s.keyA else s.keyB) e =
      if 0 < e ∧ e ≤ (if party then s.stA else s.stB).completedEpoch then
        (T e).encaps1.map (fun (_, _, key) => P.kdfOK key e)
      else none

/-- Either the correctness flag is already false, or some transcript is consistent with the game
state. -/
def CorrectnessInv
    (ik : InitKey)
    (s : GameState P AuthState) : Prop :=
  s.correct = false ∨
    ∃ T : ℕ → EpochTranscript P, TranscriptConsistent P auth ik T s

theorem transcriptConsistent_initGameState
    (ik : InitKey) :
    TranscriptConsistent P auth ik
      (fun _ => { keypair := none, encaps1 := none })
      (SCKAScheme.initGameState (initA P auth ik) (initB P auth ik)) := by
  have hControl : ControlInv
      (SCKAScheme.initGameState (I := P.EpochKey) (Rho := Message P.Sym)
        (initA P auth ik) (initB P auth ik)) := by
    refine ⟨epochKnowledgeInv_initGameState P auth ik,
      recordedReportInv_initGameState (initA P auth ik) (initB P auth ik),
      ?_, ?_, ?_⟩
    · simp [SCKAScheme.initGameState, initA, State.epoch]
    · simp [SCKAScheme.initGameState, initB, State.epoch]
    · intro party
      cases party <;>
        simp [SCKAScheme.initGameState, initA, initB,
          State.controlPosition, State.epoch]
  refine ⟨rfl, hControl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro party
    cases party <;>
      simp [SCKAScheme.initGameState, initA, initB,
        State.controlPosition, State.epoch, AllowedStatePair]
  · simp
  · simp
  · simp [LocalPayloadInv, SCKAScheme.initGameState, initA,
      transcriptAuth]
  · simp [LocalPayloadInv, SCKAScheme.initGameState, initB,
      transcriptAuth]
  · simp [SCKAScheme.initGameState]
  · intro party e
    cases party <;>
      simp [SCKAScheme.initGameState, initA, initB,
        State.completedEpoch, State.epoch]

/-- When a party is about to sample its key pair, its peer is waiting for the header of the same
epoch. -/
theorem peer_noHeaderReceived_of_keysUnsampled
    (ik : InitKey) (T : ℕ → EpochTranscript P)
    (s : GameState P AuthState)
    (hT : TranscriptConsistent P auth ik T s)
    (party : Bool) (e : ℕ) (a : AuthState)
    (hst : (if party then s.stA else s.stB) = .keysUnsampled e a) :
    ∃ b dec, (if party then s.stB else s.stA) = .noHeaderReceived e b dec := by
  have hEpoch := hT.control.epochKnowledge
  have hPosA := hEpoch.keyPrefix.posA
  have hPosB := hEpoch.keyPrefix.posB
  have hCrossA := hEpoch.epochA_le
  have hCrossB := hEpoch.epochB_le
  have hCompletedA := s.stA.completedEpoch_le_epoch
  have hCompletedB := s.stB.completedEpoch_le_epoch
  have hPairA := hT.statePair true
  have hPairB := hT.statePair false
  simp only [if_true] at hPairA
  simp only [Bool.false_eq_true, ↓reduceIte] at hPairB
  cases party
  · change s.stB = .keysUnsampled e a at hst
    change ∃ b dec, s.stA = .noHeaderReceived e b dec
    have hUpper : s.stA.epoch ≤ e := by
      have h := hCrossA
      rw [hst] at h
      simp only [State.completedEpoch, State.epoch] at h
      have he : 0 < e := by
        simpa [hst, State.epoch] using hPosB
      have heq : e - 1 + 1 = e := by omega
      simpa only [State.epoch, heq] using h
    have hLower : e ≤ s.stA.epoch + 1 := by
      have h := hCrossB
      rw [hst] at h
      simp only [State.epoch] at h
      omega
    have hNotLag : ¬ e = s.stA.epoch + 1 := by
      intro hLag
      have hLag' : s.stB.epoch = s.stA.epoch + 1 := by
        rw [hst]
        exact hLag
      rcases hPairA.2 hLag' with ⟨a', enc, b, dec, _, hPeer⟩
      rw [hst] at hPeer
      cases hPeer
    have hEqual : s.stA.epoch = e := by omega
    have hSame : s.stB.epoch = s.stA.epoch := by
      rw [hst]
      exact hEqual.symm
    have hGenerator : s.stB.controlPosition.isGenerator = true := by
      rw [hst]
      rfl
    have hAllowed := hPairB.1 hSame hGenerator
    cases ha : s.stA
    case noHeaderReceived e' b dec =>
      have he' : e' = e := by
        simpa [ha, State.epoch] using hEqual
      subst e'
      exact ⟨b, dec, rfl⟩
    all_goals simp [AllowedStatePair, hst, ha] at hAllowed
  · change s.stA = .keysUnsampled e a at hst
    change ∃ b dec, s.stB = .noHeaderReceived e b dec
    have hUpper : s.stB.epoch ≤ e := by
      have h := hCrossB
      rw [hst] at h
      simp only [State.completedEpoch, State.epoch] at h
      have he : 0 < e := by
        simpa [hst, State.epoch] using hPosA
      have heq : e - 1 + 1 = e := by omega
      simpa only [State.epoch, heq] using h
    have hLower : e ≤ s.stB.epoch + 1 := by
      have h := hCrossA
      rw [hst] at h
      simp only [State.epoch] at h
      omega
    have hNotLag : ¬ e = s.stB.epoch + 1 := by
      intro hLag
      have hLag' : s.stA.epoch = s.stB.epoch + 1 := by
        rw [hst]
        exact hLag
      rcases hPairB.2 hLag' with ⟨a', enc, b, dec, _, hPeer⟩
      rw [hst] at hPeer
      cases hPeer
    have hEqual : s.stB.epoch = e := by omega
    have hSame : s.stA.epoch = s.stB.epoch := by
      rw [hst]
      exact hEqual.symm
    have hGenerator : s.stA.controlPosition.isGenerator = true := by
      rw [hst]
      rfl
    have hAllowed := hPairA.1 hSame hGenerator
    cases hb : s.stB
    case noHeaderReceived e' b dec =>
      have he' : e' = e := by
        simpa [hb, State.epoch] using hEqual
      subst e'
      exact ⟨b, dec, rfl⟩
    all_goals simp [AllowedStatePair, hst, hb] at hAllowed

/-- When a party is about to encapsulate against a received header, the epoch has a recorded key
pair, the header is that key pair's header, and the peer holds its secret key and vector. -/
theorem peer_keysSampled_of_headerReceived
    (ik : InitKey) (T : ℕ → EpochTranscript P)
    (s : GameState P AuthState)
    (hT : TranscriptConsistent P auth ik T s)
    (party : Bool) (e : ℕ) (a : AuthState) (hdr : P.inc.PKheader)
    (dec : DecoderState P.inc.PKvector P.Sym)
    (hst : (if party then s.stA else s.stB) = .headerReceived e a hdr dec) :
    ∃ pk sk b enc,
      (T e).keypair = some (pk, sk) ∧
      (if party then s.stB else s.stA) = .keysSampled e b sk (P.inc.toVector pk) enc ∧
      hdr = P.inc.toHeader pk := by
  have hEpoch := hT.control.epochKnowledge
  have hPosA := hEpoch.keyPrefix.posA
  have hPosB := hEpoch.keyPrefix.posB
  have hCrossA := hEpoch.epochA_le
  have hCrossB := hEpoch.epochB_le
  have hCompletedA := s.stA.completedEpoch_le_epoch
  have hCompletedB := s.stB.completedEpoch_le_epoch
  have hPairA := hT.statePair true
  have hPairB := hT.statePair false
  have hRoleA := (hT.control.roles true).1
  have hRoleB := (hT.control.roles false).1
  have hLocalA := hT.localA
  have hLocalB := hT.localB
  simp only [if_true] at hPairA hRoleA
  simp only [Bool.false_eq_true, ↓reduceIte] at hPairB hRoleB
  cases party
  · change s.stB = .headerReceived e a hdr dec at hst
    change ∃ pk sk b enc,
      (T e).keypair = some (pk, sk) ∧
        s.stA = .keysSampled e b sk (P.inc.toVector pk) enc ∧
        hdr = P.inc.toHeader pk
    have hUpper : s.stA.epoch ≤ e := by
      have h := hCrossA
      rw [hst] at h
      simp only [State.completedEpoch, State.epoch] at h
      have he : 0 < e := by
        simpa [hst, State.epoch] using hPosB
      have heq : e - 1 + 1 = e := by omega
      simpa only [State.epoch, heq] using h
    have hLower : e ≤ s.stA.epoch + 1 := by
      have h := hCrossB
      rw [hst] at h
      simp only [State.epoch] at h
      omega
    have hNotLag : ¬ e = s.stA.epoch + 1 := by
      intro hLag
      have hLag' : s.stB.epoch = s.stA.epoch + 1 := by
        rw [hst]
        exact hLag
      rcases hPairA.2 hLag' with ⟨a', enc, b, dec, _, hPeer⟩
      rw [hst] at hPeer
      cases hPeer
    have hEqual : s.stA.epoch = e := by omega
    have hMod : e % 2 = 1 := by
      have hLt : e % 2 < 2 := Nat.mod_lt _ (by omega)
      rw [hst] at hRoleB
      simp only [State.controlPosition, State.epoch] at hRoleB
      have hNot : e % 2 ≠ 0 := of_decide_eq_false hRoleB.symm
      omega
    have hGenerator : s.stA.controlPosition.isGenerator = true := by
      rw [hRoleA, hEqual]
      simp [hMod]
    have hSame : s.stA.epoch = s.stB.epoch := by
      rw [hst]
      exact hEqual
    have hAllowed := hPairA.1 hSame hGenerator
    cases ha : s.stA
    case keysSampled e' b sk vec enc =>
      have he' : e' = e := by
        simpa [ha, State.epoch] using hEqual
      subst e'
      rw [ha] at hLocalA
      rw [hst] at hLocalB
      simp only [LocalPayloadInv] at hLocalA hLocalB
      rcases hLocalA with ⟨_, pk, hkeyA, hvec, _⟩
      rcases hLocalB with ⟨_, _, pk', sk', hkeyB, hhdr, _⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hkeyA.symm.trans hkeyB))
      refine ⟨pk, sk, b, enc, hkeyA, ?_, ?_⟩
      · simp [hvec] at ha ⊢
      · simpa using hhdr
    all_goals simp [AllowedStatePair, hst, ha] at hAllowed
  · change s.stA = .headerReceived e a hdr dec at hst
    change ∃ pk sk b enc,
      (T e).keypair = some (pk, sk) ∧
        s.stB = .keysSampled e b sk (P.inc.toVector pk) enc ∧
        hdr = P.inc.toHeader pk
    have hUpper : s.stB.epoch ≤ e := by
      have h := hCrossB
      rw [hst] at h
      simp only [State.completedEpoch, State.epoch] at h
      have he : 0 < e := by
        simpa [hst, State.epoch] using hPosA
      have heq : e - 1 + 1 = e := by omega
      simpa only [State.epoch, heq] using h
    have hLower : e ≤ s.stB.epoch + 1 := by
      have h := hCrossA
      rw [hst] at h
      simp only [State.epoch] at h
      omega
    have hNotLag : ¬ e = s.stB.epoch + 1 := by
      intro hLag
      have hLag' : s.stA.epoch = s.stB.epoch + 1 := by
        rw [hst]
        exact hLag
      rcases hPairB.2 hLag' with ⟨a', enc, b, dec, _, hPeer⟩
      rw [hst] at hPeer
      cases hPeer
    have hEqual : s.stB.epoch = e := by omega
    have hMod : e % 2 = 0 := by
      have hLt : e % 2 < 2 := Nat.mod_lt _ (by omega)
      rw [hst] at hRoleA
      simp only [State.controlPosition, State.epoch] at hRoleA
      have hNot : e % 2 ≠ 1 := of_decide_eq_false hRoleA.symm
      omega
    have hGenerator : s.stB.controlPosition.isGenerator = true := by
      rw [hRoleB, hEqual]
      simp [hMod]
    have hSame : s.stB.epoch = s.stA.epoch := by
      rw [hst]
      exact hEqual
    have hAllowed := hPairB.1 hSame hGenerator
    cases hb : s.stB
    case keysSampled e' b sk vec enc =>
      have he' : e' = e := by
        simpa [hb, State.epoch] using hEqual
      subst e'
      rw [hb] at hLocalB
      rw [hst] at hLocalA
      simp only [LocalPayloadInv] at hLocalA hLocalB
      rcases hLocalB with ⟨_, pk, hkeyB, hvec, _⟩
      rcases hLocalA with ⟨_, _, pk', sk', hkeyA, hhdr, _⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hkeyB.symm.trans hkeyA))
      refine ⟨pk, sk, b, enc, hkeyB, ?_, ?_⟩
      · simp [hvec] at hb ⊢
      · simpa using hhdr
    all_goals simp [AllowedStatePair, hst, hb] at hAllowed

end MLKEMBraid
