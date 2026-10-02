/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Correctness.EpochSafety.Control

/-!
# Receives by an encapsulator

A successful receive of a recorded message by a party in an encapsulating state preserves
`StatePairInv` (`receive_encapsulator_preserves_statePairInv`).
-/

open OracleSpec OracleComp
open ErasureCodePayload.Streaming
open SCKAScheme.sckaCorrectnessSpec

namespace MLKEMBraid

variable (P : Parameters ProbComp) {InitKey AuthState : Type}
  (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
    P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)

private theorem receive_noHeaderReceived_preserves_statePairInv
    [DecidableEq P.Sym]
    (s : GameState P AuthState)
    (hs : ControlInv s ∧ StatePairInv s)
    (party : Bool)
    (e : ℕ) (a : AuthState)
    (headerDecoder : DecoderState (P.inc.PKheader × P.Mac) P.Sym)
    (hst : (if party then s.stA else s.stB) =
      .noHeaderReceived e a headerDecoder)
    (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ)
    (hmsg : (if party then s.msgB else s.msgA) n = some (msg, tsnd))
    (r : RecvResult P AuthState)
    (hr : receive P auth (.noHeaderReceived e a headerDecoder) msg = .ok r) :
    StatePairInv
      (if party then { s with stA := r.state }
       else { s with stB := r.state }) := by
  -- The receive leaves the state unchanged, or a header chunk of epoch `e` extends the decoder,
  -- or it completes the header and moves to `headerReceived`.
  have houtcome :
      r.state = .noHeaderReceived e a headerDecoder ∨
      (msg.type = .hdr ∧ msg.epoch = e ∧
        ((∃ dec, r.state = .noHeaderReceived e a dec) ∨
          ∃ hdr dec, r.state = .headerReceived e a hdr dec)) := by
    simp only [receive] at hr
    repeat' split at hr
    all_goals cases hr
    all_goals first
      | exact Or.inr ⟨by assumption, by assumption, Or.inl ⟨_, rfl⟩⟩
      | exact Or.inr ⟨by assumption, by assumption, Or.inr ⟨_, _, rfl⟩⟩
      | exact Or.inl rfl
  obtain ⟨⟨hEpoch, -, -, -, hcontrol⟩, hPair⟩ := hs
  have hA := hcontrol true
  have hB := hcontrol false
  simp only [if_true] at hA
  simp only [Bool.false_eq_true, ↓reduceIte] at hB
  cases party
  · simp only [Bool.false_eq_true, ↓reduceIte] at hst hmsg ⊢
    rcases houtcome with hsame | ⟨htype, hepoch, hnew⟩
    · rw [hsame, ← hst]
      exact hPair
    · have hmsgCtl := hA.2.2 n msg tsnd hmsg
      simp only [MessageControl, htype, hepoch] at hmsgCtl
      obtain ⟨-, hle, -, hrank⟩ := hmsgCtl
      have hposB : 0 < s.stB.epoch := hEpoch.keyPrefix.posB
      have hepochB : s.stB.epoch = e := by
        rw [hst]
        rfl
      have hcompleted : s.stB.completedEpoch = e - 1 := by
        rw [hst]
        rfl
      have hboundA : s.stA.epoch ≤ s.stB.completedEpoch + 1 := hEpoch.epochA_le
      have heqA : s.stA.epoch = e := by omega
      have hrank2 : 1 ≤ s.stA.controlPosition.step := hrank heqA.symm
      have hodd : e % 2 = 1 := by
        have hphase := hB.1
        rw [hst] at hphase
        rcases Nat.mod_two_eq_zero_or_one e with hzero | hone
        · simp [State.controlPosition, State.epoch, hzero] at hphase
        · exact hone
      have hgenA : s.stA.controlPosition.isGenerator = true := by
        rw [hA.1, heqA]
        simp [hodd]
      have hpairA := hPair true
      simp only [if_true] at hpairA
      have hallowed := hpairA.1 (by omega) hgenA
      rw [hst] at hallowed
      cases hb : s.stA <;>
        simp only [AllowedStatePair, hb, State.epoch, State.controlPosition] at hallowed heqA hrank2
      all_goals try omega
      rcases hnew with ⟨_, hnew⟩ | ⟨_, _, hnew⟩
      all_goals
        rw [hnew]
        intro side
        cases side
        · simp only [Bool.false_eq_true, ↓reduceIte, State.epoch, State.controlPosition]
          constructor
          · intros
            trivial
          · intro hlag
            omega
        · simp only [if_true, State.epoch, State.controlPosition]
          constructor
          · intros
            trivial
          · intro hlag
            omega
  · simp only [if_true] at hst hmsg ⊢
    rcases houtcome with hsame | ⟨htype, hepoch, hnew⟩
    · rw [hsame, ← hst]
      exact hPair
    · have hmsgCtl := hB.2.2 n msg tsnd hmsg
      simp only [MessageControl, htype, hepoch] at hmsgCtl
      obtain ⟨-, hle, -, hrank⟩ := hmsgCtl
      have hposA : 0 < s.stA.epoch := hEpoch.keyPrefix.posA
      have hepochA : s.stA.epoch = e := by
        rw [hst]
        rfl
      have hcompleted : s.stA.completedEpoch = e - 1 := by
        rw [hst]
        rfl
      have hboundB : s.stB.epoch ≤ s.stA.completedEpoch + 1 := hEpoch.epochB_le
      have heqB : s.stB.epoch = e := by omega
      have hrank2 : 1 ≤ s.stB.controlPosition.step := hrank heqB.symm
      have heven : e % 2 = 0 := by
        have hphase := hA.1
        rw [hst] at hphase
        rcases Nat.mod_two_eq_zero_or_one e with hzero | hone
        · exact hzero
        · simp [State.controlPosition, State.epoch, hone] at hphase
      have hgenB : s.stB.controlPosition.isGenerator = true := by
        rw [hB.1, heqB]
        simp [heven]
      have hpairB := hPair false
      simp only [Bool.false_eq_true, ↓reduceIte] at hpairB
      have hallowed := hpairB.1 (by omega) hgenB
      rw [hst] at hallowed
      cases hb : s.stB <;>
        simp only [AllowedStatePair, hb, State.epoch, State.controlPosition] at hallowed heqB hrank2
      all_goals try omega
      rcases hnew with ⟨_, hnew⟩ | ⟨_, _, hnew⟩
      all_goals
        rw [hnew]
        intro side
        cases side
        · simp only [Bool.false_eq_true, ↓reduceIte, State.epoch, State.controlPosition]
          constructor
          · intros
            trivial
          · intro hlag
            omega
        · simp only [if_true, State.epoch, State.controlPosition]
          constructor
          · intros
            trivial
          · intro hlag
            omega

private theorem receive_ct1Sampled_preserves_statePairInv
    [DecidableEq P.Sym]
    (s : GameState P AuthState)
    (hs : ControlInv s ∧ StatePairInv s)
    (party : Bool)
    (e : ℕ) (a : AuthState) (header : P.inc.PKheader)
    (encapsState : P.inc.St) (ct1 : P.inc.C₁)
    (ct1Encoder : EncoderState P.inc.C₁ P.Sym)
    (ekDecoder : DecoderState P.inc.PKvector P.Sym)
    (hst : (if party then s.stA else s.stB) =
      .ct1Sampled e a header encapsState ct1 ct1Encoder ekDecoder)
    (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ)
    (hmsg : (if party then s.msgB else s.msgA) n = some (msg, tsnd))
    (r : RecvResult P AuthState)
    (hr : receive P auth
      (.ct1Sampled e a header encapsState ct1 ct1Encoder ekDecoder) msg = .ok r) :
    StatePairInv
      (if party then { s with stA := r.state }
       else { s with stB := r.state }) := by
  -- An `ek` chunk of epoch `e` extends the vector decoder or completes it and moves to
  -- `ekReceivedCt1Sampled`. An `ekCt1Ack` chunk moves to `ct1Acknowledged`, or to `ct2Sampled`
  -- if it completes the vector. Every other message leaves the state unchanged.
  have houtcome :
      r.state = .ct1Sampled e a header encapsState ct1 ct1Encoder ekDecoder ∨
      (msg.type = .ek ∧ msg.epoch = e ∧
        ((∃ dec, r.state = .ct1Sampled e a header encapsState ct1 ct1Encoder dec) ∨
          ∃ vec, r.state = .ekReceivedCt1Sampled e a encapsState ct1 header vec ct1Encoder)) ∨
      (msg.type = .ekCt1Ack ∧ msg.epoch = e ∧
        ((∃ dec, r.state = .ct1Acknowledged e a header encapsState ct1 dec) ∨
          ∃ enc, r.state = .ct2Sampled e a enc)) := by
    simp only [receive] at hr
    repeat' split at hr
    all_goals cases hr
    all_goals first
      | exact Or.inr (Or.inl ⟨by assumption, by assumption, Or.inl ⟨_, rfl⟩⟩)
      | exact Or.inr (Or.inl ⟨by assumption, by assumption, Or.inr ⟨_, rfl⟩⟩)
      | exact Or.inr (Or.inr ⟨by assumption, by assumption, Or.inl ⟨_, rfl⟩⟩)
      | exact Or.inr (Or.inr ⟨by assumption, by assumption, Or.inr ⟨_, rfl⟩⟩)
      | exact Or.inl rfl
  obtain ⟨⟨hEpoch, -, -, -, hcontrol⟩, hPair⟩ := hs
  have hA := hcontrol true
  have hB := hcontrol false
  simp only [if_true] at hA
  simp only [Bool.false_eq_true, ↓reduceIte] at hB
  cases party
  · simp only [Bool.false_eq_true, ↓reduceIte] at hst hmsg ⊢
    rcases houtcome with hsame | ⟨htype, hepoch, hnew⟩ | ⟨htype, hepoch, hnew⟩
    · rw [hsame, ← hst]
      exact hPair
    · have hmsgCtl := hA.2.2 n msg tsnd hmsg
      simp only [MessageControl, htype, hepoch] at hmsgCtl
      obtain ⟨-, hle, -, hrank⟩ := hmsgCtl
      have hepochB : s.stB.epoch = e := by
        rw [hst]
        rfl
      have hcompleted : s.stB.completedEpoch = e := by
        rw [hst]
        rfl
      have hboundA : s.stA.epoch ≤ s.stB.completedEpoch + 1 := hEpoch.epochA_le
      have hpairB := hPair false
      simp only [Bool.false_eq_true, ↓reduceIte] at hpairB
      have hnotLag : s.stA.epoch ≠ e + 1 := by
        intro hlag
        rcases hpairB.2 (by omega) with ⟨_, _, _, _, hct2, _⟩
        rw [hst] at hct2
        cases hct2
      have heqA : s.stA.epoch = e := by omega
      have hrank2 : 2 ≤ s.stA.controlPosition.step := hrank heqA.symm
      have hodd : e % 2 = 1 := by
        have hphase := hB.1
        rw [hst] at hphase
        rcases Nat.mod_two_eq_zero_or_one e with hzero | hone
        · simp [State.controlPosition, State.epoch, hzero] at hphase
        · exact hone
      have hgenA : s.stA.controlPosition.isGenerator = true := by
        rw [hA.1, heqA]
        simp [hodd]
      have hpairA := hPair true
      simp only [if_true] at hpairA
      have hallowed := hpairA.1 (by omega) hgenA
      rw [hst] at hallowed
      cases hb : s.stA <;>
        simp only [AllowedStatePair, hb, State.epoch, State.controlPosition] at hallowed heqA hrank2
      all_goals try omega
      all_goals
        rcases hnew with ⟨_, hnew⟩ | ⟨_, hnew⟩
      all_goals
        rw [hnew]
        intro side
        cases side
        · simp only [Bool.false_eq_true, ↓reduceIte, State.epoch, State.controlPosition]
          constructor
          · intros
            trivial
          · intro hlag
            omega
        · simp only [if_true, State.epoch, State.controlPosition]
          constructor
          · intros
            trivial
          · intro hlag
            omega
    · have hmsgCtl := hA.2.2 n msg tsnd hmsg
      simp only [MessageControl, htype, hepoch] at hmsgCtl
      obtain ⟨-, hle, -, hrank⟩ := hmsgCtl
      have hepochB : s.stB.epoch = e := by
        rw [hst]
        rfl
      have hcompleted : s.stB.completedEpoch = e := by
        rw [hst]
        rfl
      have hboundA : s.stA.epoch ≤ s.stB.completedEpoch + 1 := hEpoch.epochA_le
      have hpairB := hPair false
      simp only [Bool.false_eq_true, ↓reduceIte] at hpairB
      have hnotLag : s.stA.epoch ≠ e + 1 := by
        intro hlag
        rcases hpairB.2 (by omega) with ⟨_, _, _, _, hct2, _⟩
        rw [hst] at hct2
        cases hct2
      have heqA : s.stA.epoch = e := by omega
      have hrank2 : 3 ≤ s.stA.controlPosition.step := hrank heqA.symm
      have hodd : e % 2 = 1 := by
        have hphase := hB.1
        rw [hst] at hphase
        rcases Nat.mod_two_eq_zero_or_one e with hzero | hone
        · simp [State.controlPosition, State.epoch, hzero] at hphase
        · exact hone
      have hgenA : s.stA.controlPosition.isGenerator = true := by
        rw [hA.1, heqA]
        simp [hodd]
      have hpairA := hPair true
      simp only [if_true] at hpairA
      have hallowed := hpairA.1 (by omega) hgenA
      rw [hst] at hallowed
      cases hb : s.stA <;>
        simp only [AllowedStatePair, hb, State.epoch, State.controlPosition] at hallowed heqA hrank2
      all_goals try omega
      all_goals
        rcases hnew with ⟨_, hnew⟩ | ⟨_, hnew⟩
      all_goals
        rw [hnew]
        intro side
        cases side
        · simp only [Bool.false_eq_true, ↓reduceIte, State.epoch, State.controlPosition]
          constructor
          · intros
            trivial
          · intro hlag
            omega
        · simp only [if_true, State.epoch, State.controlPosition]
          constructor
          · intros
            trivial
          · intro hlag
            omega
  · simp only [if_true] at hst hmsg ⊢
    rcases houtcome with hsame | ⟨htype, hepoch, hnew⟩ | ⟨htype, hepoch, hnew⟩
    · rw [hsame, ← hst]
      exact hPair
    · have hmsgCtl := hB.2.2 n msg tsnd hmsg
      simp only [MessageControl, htype, hepoch] at hmsgCtl
      obtain ⟨-, hle, -, hrank⟩ := hmsgCtl
      have hepochA : s.stA.epoch = e := by
        rw [hst]
        rfl
      have hcompleted : s.stA.completedEpoch = e := by
        rw [hst]
        rfl
      have hboundB : s.stB.epoch ≤ s.stA.completedEpoch + 1 := hEpoch.epochB_le
      have hpairA := hPair true
      simp only [if_true] at hpairA
      have hnotLag : s.stB.epoch ≠ e + 1 := by
        intro hlag
        rcases hpairA.2 (by omega) with ⟨_, _, _, _, hct2, _⟩
        rw [hst] at hct2
        cases hct2
      have heqB : s.stB.epoch = e := by omega
      have hrank2 : 2 ≤ s.stB.controlPosition.step := hrank heqB.symm
      have heven : e % 2 = 0 := by
        have hphase := hA.1
        rw [hst] at hphase
        rcases Nat.mod_two_eq_zero_or_one e with hzero | hone
        · exact hzero
        · simp [State.controlPosition, State.epoch, hone] at hphase
      have hgenB : s.stB.controlPosition.isGenerator = true := by
        rw [hB.1, heqB]
        simp [heven]
      have hpairB := hPair false
      simp only [Bool.false_eq_true, ↓reduceIte] at hpairB
      have hallowed := hpairB.1 (by omega) hgenB
      rw [hst] at hallowed
      cases hb : s.stB <;>
        simp only [AllowedStatePair, hb, State.epoch, State.controlPosition] at hallowed heqB hrank2
      all_goals try omega
      all_goals
        rcases hnew with ⟨_, hnew⟩ | ⟨_, hnew⟩
      all_goals
        rw [hnew]
        intro side
        cases side
        · simp only [Bool.false_eq_true, ↓reduceIte, State.epoch, State.controlPosition]
          constructor
          · intros
            trivial
          · intro hlag
            omega
        · simp only [if_true, State.epoch, State.controlPosition]
          constructor
          · intros
            trivial
          · intro hlag
            omega
    · have hmsgCtl := hB.2.2 n msg tsnd hmsg
      simp only [MessageControl, htype, hepoch] at hmsgCtl
      obtain ⟨-, hle, -, hrank⟩ := hmsgCtl
      have hepochA : s.stA.epoch = e := by
        rw [hst]
        rfl
      have hcompleted : s.stA.completedEpoch = e := by
        rw [hst]
        rfl
      have hboundB : s.stB.epoch ≤ s.stA.completedEpoch + 1 := hEpoch.epochB_le
      have hpairA := hPair true
      simp only [if_true] at hpairA
      have hnotLag : s.stB.epoch ≠ e + 1 := by
        intro hlag
        rcases hpairA.2 (by omega) with ⟨_, _, _, _, hct2, _⟩
        rw [hst] at hct2
        cases hct2
      have heqB : s.stB.epoch = e := by omega
      have hrank2 : 3 ≤ s.stB.controlPosition.step := hrank heqB.symm
      have heven : e % 2 = 0 := by
        have hphase := hA.1
        rw [hst] at hphase
        rcases Nat.mod_two_eq_zero_or_one e with hzero | hone
        · exact hzero
        · simp [State.controlPosition, State.epoch, hone] at hphase
      have hgenB : s.stB.controlPosition.isGenerator = true := by
        rw [hB.1, heqB]
        simp [heven]
      have hpairB := hPair false
      simp only [Bool.false_eq_true, ↓reduceIte] at hpairB
      have hallowed := hpairB.1 (by omega) hgenB
      rw [hst] at hallowed
      cases hb : s.stB <;>
        simp only [AllowedStatePair, hb, State.epoch, State.controlPosition] at hallowed heqB hrank2
      all_goals try omega
      all_goals
        rcases hnew with ⟨_, hnew⟩ | ⟨_, hnew⟩
      all_goals
        rw [hnew]
        intro side
        cases side
        · simp only [Bool.false_eq_true, ↓reduceIte, State.epoch, State.controlPosition]
          constructor
          · intros
            trivial
          · intro hlag
            omega
        · simp only [if_true, State.epoch, State.controlPosition]
          constructor
          · intros
            trivial
          · intro hlag
            omega

private theorem receive_ekReceivedCt1Sampled_preserves_statePairInv
    [DecidableEq P.Sym]
    (s : GameState P AuthState)
    (hs : ControlInv s ∧ StatePairInv s)
    (party : Bool)
    (e : ℕ) (a : AuthState) (encapsState : P.inc.St) (ct1 : P.inc.C₁)
    (header : P.inc.PKheader) (ekVector : P.inc.PKvector)
    (ct1Encoder : EncoderState P.inc.C₁ P.Sym)
    (hst : (if party then s.stA else s.stB) =
      .ekReceivedCt1Sampled e a encapsState ct1 header ekVector ct1Encoder)
    (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ)
    (hmsg : (if party then s.msgB else s.msgA) n = some (msg, tsnd))
    (r : RecvResult P AuthState)
    (hr : receive P auth
      (.ekReceivedCt1Sampled e a encapsState ct1 header ekVector ct1Encoder) msg = .ok r) :
    StatePairInv
      (if party then { s with stA := r.state }
       else { s with stB := r.state }) := by
  -- The receive leaves the state unchanged, or an `ekCt1Ack` message of epoch `e` runs `Encaps2`
  -- and moves to `ct2Sampled`.
  have houtcome :
      r.state = .ekReceivedCt1Sampled e a encapsState ct1 header ekVector ct1Encoder ∨
      (msg.type = .ekCt1Ack ∧ msg.epoch = e ∧ ∃ enc, r.state = .ct2Sampled e a enc) := by
    simp only [receive] at hr
    repeat' split at hr
    all_goals cases hr
    all_goals first
      | exact Or.inr ⟨by assumption, by assumption, _, rfl⟩
      | exact Or.inl rfl
  obtain ⟨⟨hEpoch, -, -, -, hcontrol⟩, hPair⟩ := hs
  have hA := hcontrol true
  have hB := hcontrol false
  simp only [if_true] at hA
  simp only [Bool.false_eq_true, ↓reduceIte] at hB
  cases party
  · simp only [Bool.false_eq_true, ↓reduceIte] at hst hmsg ⊢
    rcases houtcome with hsame | ⟨htype, hepoch, _, hnew⟩
    · rw [hsame, ← hst]
      exact hPair
    · have hmsgCtl := hA.2.2 n msg tsnd hmsg
      simp only [MessageControl, htype, hepoch] at hmsgCtl
      obtain ⟨-, hle, -, hrank⟩ := hmsgCtl
      have hepochB : s.stB.epoch = e := by
        rw [hst]
        rfl
      have hcompleted : s.stB.completedEpoch = e := by
        rw [hst]
        rfl
      have hboundA : s.stA.epoch ≤ s.stB.completedEpoch + 1 := hEpoch.epochA_le
      have hpairB := hPair false
      simp only [Bool.false_eq_true, ↓reduceIte] at hpairB
      have hnotLag : s.stA.epoch ≠ e + 1 := by
        intro hlag
        rcases hpairB.2 (by omega) with ⟨_, _, _, _, hct2, _⟩
        rw [hst] at hct2
        cases hct2
      have heqA : s.stA.epoch = e := by omega
      have hrank2 : 3 ≤ s.stA.controlPosition.step := hrank heqA.symm
      have hodd : e % 2 = 1 := by
        have hphase := hB.1
        rw [hst] at hphase
        rcases Nat.mod_two_eq_zero_or_one e with hzero | hone
        · simp [State.controlPosition, State.epoch, hzero] at hphase
        · exact hone
      have hgenA : s.stA.controlPosition.isGenerator = true := by
        rw [hA.1, heqA]
        simp [hodd]
      have hpairA := hPair true
      simp only [if_true] at hpairA
      have hallowed := hpairA.1 (by omega) hgenA
      rw [hst] at hallowed
      rw [hnew]
      cases hb : s.stA <;>
        simp only [AllowedStatePair, hb, State.epoch, State.controlPosition] at hallowed heqA hrank2
      all_goals try omega
      intro side
      cases side
      · simp only [Bool.false_eq_true, ↓reduceIte, State.epoch, State.controlPosition]
        constructor
        · intros
          trivial
        · intro hlag
          omega
      · simp only [if_true, State.epoch, State.controlPosition]
        constructor
        · intros
          trivial
        · intro hlag
          omega
  · simp only [if_true] at hst hmsg ⊢
    rcases houtcome with hsame | ⟨htype, hepoch, _, hnew⟩
    · rw [hsame, ← hst]
      exact hPair
    · have hmsgCtl := hB.2.2 n msg tsnd hmsg
      simp only [MessageControl, htype, hepoch] at hmsgCtl
      obtain ⟨-, hle, -, hrank⟩ := hmsgCtl
      have hepochA : s.stA.epoch = e := by
        rw [hst]
        rfl
      have hcompleted : s.stA.completedEpoch = e := by
        rw [hst]
        rfl
      have hboundB : s.stB.epoch ≤ s.stA.completedEpoch + 1 := hEpoch.epochB_le
      have hpairA := hPair true
      simp only [if_true] at hpairA
      have hnotLag : s.stB.epoch ≠ e + 1 := by
        intro hlag
        rcases hpairA.2 (by omega) with ⟨_, _, _, _, hct2, _⟩
        rw [hst] at hct2
        cases hct2
      have heqB : s.stB.epoch = e := by omega
      have hrank2 : 3 ≤ s.stB.controlPosition.step := hrank heqB.symm
      have heven : e % 2 = 0 := by
        have hphase := hA.1
        rw [hst] at hphase
        rcases Nat.mod_two_eq_zero_or_one e with hzero | hone
        · exact hzero
        · simp [State.controlPosition, State.epoch, hone] at hphase
      have hgenB : s.stB.controlPosition.isGenerator = true := by
        rw [hB.1, heqB]
        simp [heven]
      have hpairB := hPair false
      simp only [Bool.false_eq_true, ↓reduceIte] at hpairB
      have hallowed := hpairB.1 (by omega) hgenB
      rw [hst] at hallowed
      rw [hnew]
      cases hb : s.stB <;>
        simp only [AllowedStatePair, hb, State.epoch, State.controlPosition] at hallowed heqB hrank2
      all_goals try omega
      intro side
      cases side
      · simp only [Bool.false_eq_true, ↓reduceIte, State.epoch, State.controlPosition]
        constructor
        · intros
          trivial
        · intro hlag
          omega
      · simp only [if_true, State.epoch, State.controlPosition]
        constructor
        · intros
          trivial
        · intro hlag
          omega

private theorem receive_ct1Acknowledged_preserves_statePairInv
    [DecidableEq P.Sym]
    (s : GameState P AuthState)
    (hs : ControlInv s ∧ StatePairInv s)
    (party : Bool)
    (e : ℕ) (a : AuthState) (header : P.inc.PKheader)
    (encapsState : P.inc.St) (ct1 : P.inc.C₁)
    (ekDecoder : DecoderState P.inc.PKvector P.Sym)
    (hst : (if party then s.stA else s.stB) =
      .ct1Acknowledged e a header encapsState ct1 ekDecoder)
    (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ)
    (hmsg : (if party then s.msgB else s.msgA) n = some (msg, tsnd))
    (r : RecvResult P AuthState)
    (hr : receive P auth
      (.ct1Acknowledged e a header encapsState ct1 ekDecoder) msg = .ok r) :
    StatePairInv
      (if party then { s with stA := r.state }
       else { s with stB := r.state }) := by
  -- The receive leaves the state unchanged, or an `ekCt1Ack` chunk of epoch `e` extends the
  -- vector decoder, or it completes the vector and moves to `ct2Sampled`.
  have houtcome :
      r.state = .ct1Acknowledged e a header encapsState ct1 ekDecoder ∨
      (msg.epoch = e ∧
        ((∃ dec, r.state = .ct1Acknowledged e a header encapsState ct1 dec) ∨
          ∃ enc, r.state = .ct2Sampled e a enc)) := by
    simp only [receive] at hr
    repeat' split at hr
    all_goals cases hr
    all_goals first
      | exact Or.inr ⟨by assumption, Or.inl ⟨_, rfl⟩⟩
      | exact Or.inr ⟨by assumption, Or.inr ⟨_, rfl⟩⟩
      | exact Or.inl rfl
  obtain ⟨⟨hEpoch, -, -, -, hcontrol⟩, hPair⟩ := hs
  have hA := hcontrol true
  have hB := hcontrol false
  simp only [if_true] at hA
  simp only [Bool.false_eq_true, ↓reduceIte] at hB
  cases party
  · simp only [Bool.false_eq_true, ↓reduceIte] at hst hmsg ⊢
    rcases houtcome with hsame | ⟨hepoch, hnew⟩
    · rw [hsame, ← hst]
      exact hPair
    · have hle : msg.epoch ≤ s.stA.epoch := (hA.2.2 n msg tsnd hmsg).2.1
      have hepochB : s.stB.epoch = e := by
        rw [hst]
        rfl
      have hcompleted : s.stB.completedEpoch = e := by
        rw [hst]
        rfl
      have hboundA : s.stA.epoch ≤ s.stB.completedEpoch + 1 := hEpoch.epochA_le
      have hpairB := hPair false
      simp only [Bool.false_eq_true, ↓reduceIte] at hpairB
      have hnotLag : s.stA.epoch ≠ e + 1 := by
        intro hlag
        rcases hpairB.2 (by omega) with ⟨_, _, _, _, hct2, _⟩
        rw [hst] at hct2
        cases hct2
      have heqA : s.stA.epoch = e := by omega
      have hodd : e % 2 = 1 := by
        have hphase := hB.1
        rw [hst] at hphase
        rcases Nat.mod_two_eq_zero_or_one e with hzero | hone
        · simp [State.controlPosition, State.epoch, hzero] at hphase
        · exact hone
      have hgenA : s.stA.controlPosition.isGenerator = true := by
        rw [hA.1, heqA]
        simp [hodd]
      have hpairA := hPair true
      simp only [if_true] at hpairA
      have hallowed := hpairA.1 (by omega) hgenA
      rw [hst] at hallowed
      cases hb : s.stA <;>
        simp only [AllowedStatePair, hb, State.epoch] at hallowed heqA
      rcases hnew with ⟨_, hnew⟩ | ⟨_, hnew⟩
      all_goals
        rw [hnew]
        intro side
        cases side
        · simp only [Bool.false_eq_true, ↓reduceIte, State.epoch, State.controlPosition]
          constructor
          · intros
            trivial
          · intro hlag
            omega
        · simp only [if_true, State.epoch, State.controlPosition]
          constructor
          · intros
            trivial
          · intro hlag
            omega
  · simp only [if_true] at hst hmsg ⊢
    rcases houtcome with hsame | ⟨hepoch, hnew⟩
    · rw [hsame, ← hst]
      exact hPair
    · have hle : msg.epoch ≤ s.stB.epoch := (hB.2.2 n msg tsnd hmsg).2.1
      have hepochA : s.stA.epoch = e := by
        rw [hst]
        rfl
      have hcompleted : s.stA.completedEpoch = e := by
        rw [hst]
        rfl
      have hboundB : s.stB.epoch ≤ s.stA.completedEpoch + 1 := hEpoch.epochB_le
      have hpairA := hPair true
      simp only [if_true] at hpairA
      have hnotLag : s.stB.epoch ≠ e + 1 := by
        intro hlag
        rcases hpairA.2 (by omega) with ⟨_, _, _, _, hct2, _⟩
        rw [hst] at hct2
        cases hct2
      have heqB : s.stB.epoch = e := by omega
      have heven : e % 2 = 0 := by
        have hphase := hA.1
        rw [hst] at hphase
        rcases Nat.mod_two_eq_zero_or_one e with hzero | hone
        · exact hzero
        · simp [State.controlPosition, State.epoch, hone] at hphase
      have hgenB : s.stB.controlPosition.isGenerator = true := by
        rw [hB.1, heqB]
        simp [heven]
      have hpairB := hPair false
      simp only [Bool.false_eq_true, ↓reduceIte] at hpairB
      have hallowed := hpairB.1 (by omega) hgenB
      rw [hst] at hallowed
      cases hb : s.stB <;>
        simp only [AllowedStatePair, hb, State.epoch] at hallowed heqB
      rcases hnew with ⟨_, hnew⟩ | ⟨_, hnew⟩
      all_goals
        rw [hnew]
        intro side
        cases side
        · simp only [Bool.false_eq_true, ↓reduceIte, State.epoch, State.controlPosition]
          constructor
          · intros
            trivial
          · intro hlag
            omega
        · simp only [if_true, State.epoch, State.controlPosition]
          constructor
          · intros
            trivial
          · intro hlag
            omega

private theorem receive_ct2Sampled_preserves_statePairInv
    [DecidableEq P.Sym]
    (s : GameState P AuthState)
    (hs : ControlInv s ∧ StatePairInv s)
    (party : Bool)
    (e : ℕ) (a : AuthState)
    (ct2Encoder : EncoderState (P.inc.C₂ × P.Mac) P.Sym)
    (hst : (if party then s.stA else s.stB) = .ct2Sampled e a ct2Encoder)
    (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ)
    (hmsg : (if party then s.msgB else s.msgA) n = some (msg, tsnd))
    (r : RecvResult P AuthState)
    (hr : receive P auth (.ct2Sampled e a ct2Encoder) msg = .ok r) :
    StatePairInv
      (if party then { s with stA := r.state }
       else { s with stB := r.state }) := by
  -- The receive leaves the state unchanged, or a message of epoch `e + 1` moves to
  -- `keysUnsampled (e + 1)`.
  have houtcome :
      r.state = .ct2Sampled e a ct2Encoder ∨
      (msg.epoch = e + 1 ∧ r.state = .keysUnsampled (e + 1) a) := by
    simp only [receive] at hr
    repeat' split at hr
    all_goals cases hr
    all_goals first
      | exact Or.inr ⟨by assumption, rfl⟩
      | exact Or.inl rfl
  obtain ⟨⟨hEpoch, -, -, -, hcontrol⟩, hPair⟩ := hs
  have hA := hcontrol true
  have hB := hcontrol false
  simp only [if_true] at hA
  simp only [Bool.false_eq_true, ↓reduceIte] at hB
  cases party
  · simp only [Bool.false_eq_true, ↓reduceIte] at hst hmsg ⊢
    rcases houtcome with hsame | ⟨hepoch, hnew⟩
    · rw [hsame, ← hst]
      exact hPair
    · have hle : msg.epoch ≤ s.stA.epoch := (hA.2.2 n msg tsnd hmsg).2.1
      have hepochB : s.stB.epoch = e := by
        rw [hst]
        rfl
      have hcompleted : s.stB.completedEpoch = e := by
        rw [hst]
        rfl
      have hboundA : s.stA.epoch ≤ s.stB.completedEpoch + 1 := hEpoch.epochA_le
      have hpairB := hPair false
      simp only [Bool.false_eq_true, ↓reduceIte] at hpairB
      obtain ⟨_, _, _, _, -, hstA⟩ := hpairB.2 (by omega)
      -- Keep B's epoch as a variable so the projections stay opaque to the simplifier.
      obtain ⟨eB, heB⟩ : ∃ eB, s.stB.epoch = eB := ⟨_, rfl⟩
      rw [heB] at hstA hepochB
      rw [hnew]
      cases hb : s.stA <;> rw [hb] at hstA <;> cases hstA
      intro side
      cases side
      · simp only [Bool.false_eq_true, ↓reduceIte, State.epoch, State.controlPosition]
        constructor
        · intros
          trivial
        · intro hlag
          omega
      · simp only [if_true, State.epoch, State.controlPosition]
        constructor
        · intros
          trivial
        · intro hlag
          omega
  · simp only [if_true] at hst hmsg ⊢
    rcases houtcome with hsame | ⟨hepoch, hnew⟩
    · rw [hsame, ← hst]
      exact hPair
    · have hle : msg.epoch ≤ s.stB.epoch := (hB.2.2 n msg tsnd hmsg).2.1
      have hepochA : s.stA.epoch = e := by
        rw [hst]
        rfl
      have hcompleted : s.stA.completedEpoch = e := by
        rw [hst]
        rfl
      have hboundB : s.stB.epoch ≤ s.stA.completedEpoch + 1 := hEpoch.epochB_le
      have hpairA := hPair true
      simp only [if_true] at hpairA
      obtain ⟨_, _, _, _, -, hstB⟩ := hpairA.2 (by omega)
      -- Keep A's epoch as a variable so the projections stay opaque to the simplifier.
      obtain ⟨eA, heA⟩ : ∃ eA, s.stA.epoch = eA := ⟨_, rfl⟩
      rw [heA] at hstB hepochA
      rw [hnew]
      cases hb : s.stB <;> rw [hb] at hstB <;> cases hstB
      intro side
      cases side
      · simp only [Bool.false_eq_true, ↓reduceIte, State.epoch, State.controlPosition]
        constructor
        · intros
          trivial
        · intro hlag
          omega
      · simp only [if_true, State.epoch, State.controlPosition]
        constructor
        · intros
          trivial
        · intro hlag
          omega

namespace Correctness.Internal

theorem receive_encapsulator_preserves_statePairInv
    [DecidableEq P.Sym]
    (s : GameState P AuthState)
    (hs : ControlInv s ∧ StatePairInv s)
    (party : Bool) (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ)
    (hmsg :
      (if party then s.msgB else s.msgA) n = some (msg, tsnd))
    (hencapsulator :
      (if party then s.stA else s.stB).controlPosition.isGenerator = false)
    (r : RecvResult P AuthState)
    (hr :
      receive P auth (if party then s.stA else s.stB) msg = .ok r) :
    StatePairInv
      (if party then { s with stA := r.state }
       else { s with stB := r.state }) := by
  -- Split on the receiver's state, handling `headerReceived` directly and applying the
  -- state-specific lemmas in the remaining cases.
  obtain ⟨st, hst⟩ : ∃ st, (if party then s.stA else s.stB) = st := ⟨_, rfl⟩
  rw [hst] at hencapsulator hr
  cases st <;> simp only [State.controlPosition, Bool.true_eq_false] at hencapsulator
  case headerReceived e a header ekDecoder =>
    -- `headerReceived` ignores every message, so the state pair is unchanged.
    have hsame : r.state = .headerReceived e a header ekDecoder := by
      simp only [receive] at hr
      repeat' split at hr
      all_goals cases hr
      all_goals rfl
    cases party
    · simp only [Bool.false_eq_true, ↓reduceIte] at hst ⊢
      rw [hsame, ← hst]
      exact hs.2
    · simp only [if_true] at hst ⊢
      rw [hsame, ← hst]
      exact hs.2
  case noHeaderReceived e a headerDecoder =>
    exact receive_noHeaderReceived_preserves_statePairInv P auth s hs party
      e a headerDecoder hst n msg tsnd hmsg r hr
  case ct1Sampled e a header encapsState ct1 ct1Encoder ekDecoder =>
    exact receive_ct1Sampled_preserves_statePairInv P auth s hs party
      e a header encapsState ct1 ct1Encoder ekDecoder hst n msg tsnd hmsg r hr
  case ekReceivedCt1Sampled e a encapsState ct1 header ekVector ct1Encoder =>
    exact receive_ekReceivedCt1Sampled_preserves_statePairInv P auth s hs party
      e a encapsState ct1 header ekVector ct1Encoder hst n msg tsnd hmsg r hr
  case ct1Acknowledged e a header encapsState ct1 ekDecoder =>
    exact receive_ct1Acknowledged_preserves_statePairInv P auth s hs party
      e a header encapsState ct1 ekDecoder hst n msg tsnd hmsg r hr
  case ct2Sampled e a ct2Encoder =>
    exact receive_ct2Sampled_preserves_statePairInv P auth s hs party
      e a ct2Encoder hst n msg tsnd hmsg r hr

end Correctness.Internal

end MLKEMBraid
