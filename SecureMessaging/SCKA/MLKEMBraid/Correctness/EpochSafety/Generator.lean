import SecureMessaging.SCKA.MLKEMBraid.Correctness.EpochSafety.Control

open OracleSpec OracleComp
open ErasureCodePayload.Streaming
open SCKAScheme.sckaCorrectnessSpec

namespace MLKEMBraid

private theorem receive_keysSampled_preserves_statePairInv
    (P : Parameters ProbComp) [DecidableEq P.Sym]
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (s : SCKAScheme.GameState
      (State P AuthState) (State P AuthState)
      P.EpochKey (Message P.Sym))
    (hs : ControlInv s ∧ StatePairInv s)
    (party : Bool)
    (e : ℕ) (a : AuthState) (sk : P.SK) (ekVector : P.inc.PKvector)
    (headerEncoder : EncoderState (P.inc.PKheader × P.Mac) P.Sym)
    (hst : (if party then s.stA else s.stB) =
      .keysSampled e a sk ekVector headerEncoder)
    (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ)
    (hmsg : (if party then s.msgB else s.msgA) n = some (msg, tsnd))
    (r : RecvResult P AuthState)
    (hr : receive P auth (.keysSampled e a sk ekVector headerEncoder) msg = .ok r) :
    StatePairInv
      (if party then { s with stA := r.state }
       else { s with stB := r.state }) := by
  -- Reduce the concrete handler once, before any orientation work: the state is either
  -- literally unchanged, or the first `ct1` chunk of epoch `e` moves it to `headerSent`.
  have houtcome :
      r.state = .keysSampled e a sk ekVector headerEncoder ∨
      (msg.type = .ct1 ∧ msg.epoch = e ∧
        ∃ chunk, msg.data = some chunk ∧
          r.state = .headerSent e a sk
            ((DecoderState.empty P.ecpCt1).addChunk chunk)
            (EncoderState.init P.ecpEk ekVector)) := by
    simp only [receive] at hr
    repeat' split at hr
    all_goals cases hr
    all_goals first
      | exact Or.inl rfl
      | exact Or.inr ⟨by assumption, by assumption, _, by assumption, rfl⟩
  obtain ⟨⟨hEpoch, -, -, -, hcontrol⟩, hPair⟩ := hs
  have hA := hcontrol true
  have hB := hcontrol false
  simp only [if_true] at hA
  simp only [Bool.false_eq_true, ↓reduceIte] at hB
  cases party
  · -- B receives a message recorded in A's table.
    simp only [Bool.false_eq_true, ↓reduceIte] at hst hmsg ⊢
    rcases houtcome with hsame | ⟨htype, hepoch, _, -, hnew⟩
    · -- Unchanged state: transport the original invariant.
      rw [hsame, ← hst]
      exact hPair
    · have hmsgCtl := hA.2.2 n msg tsnd hmsg
      simp only [htype, hepoch] at hmsgCtl
      obtain ⟨-, hle, -, hrank⟩ := hmsgCtl
      have hposB : 0 < s.stB.epoch := hEpoch.1.2.1
      have hepochB : s.stB.epoch = e := by
        rw [hst]
        rfl
      have hcompleted : s.stB.completedEpoch = e - 1 := by
        rw [hst]
        rfl
      have hboundA : s.stA.epoch ≤ s.stB.completedEpoch + 1 := hEpoch.2.1
      have heqA : s.stA.epoch = e := by omega
      have hrank2 : 2 ≤ s.stA.controlPosition.2 := hrank heqA.symm
      have hpairB := hPair false
      simp only [Bool.false_eq_true, ↓reduceIte] at hpairB
      have hallowed := hpairB.1 (by omega) (by rw [hst]; rfl)
      rw [hst] at hallowed
      rw [hnew]
      cases hb : s.stA <;>
        simp only [hb, State.epoch, State.controlPosition] at hallowed heqA hrank2
      -- The rank bound leaves only `ct1Sampled`; `omega` refutes the two lower ranks.
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
  · -- A receives a message recorded in B's table.
    simp only [if_true] at hst hmsg ⊢
    rcases houtcome with hsame | ⟨htype, hepoch, _, -, hnew⟩
    · -- Unchanged state: transport the original invariant.
      rw [hsame, ← hst]
      exact hPair
    · have hmsgCtl := hB.2.2 n msg tsnd hmsg
      simp only [htype, hepoch] at hmsgCtl
      obtain ⟨-, hle, -, hrank⟩ := hmsgCtl
      have hposA : 0 < s.stA.epoch := hEpoch.1.1
      have hepochA : s.stA.epoch = e := by
        rw [hst]
        rfl
      have hcompleted : s.stA.completedEpoch = e - 1 := by
        rw [hst]
        rfl
      have hboundB : s.stB.epoch ≤ s.stA.completedEpoch + 1 := hEpoch.2.2.1
      have heqB : s.stB.epoch = e := by omega
      have hrank2 : 2 ≤ s.stB.controlPosition.2 := hrank heqB.symm
      have hpairA := hPair true
      simp only [if_true] at hpairA
      have hallowed := hpairA.1 (by omega) (by rw [hst]; rfl)
      rw [hst] at hallowed
      rw [hnew]
      cases hb : s.stB <;>
        simp only [hb, State.epoch, State.controlPosition] at hallowed heqB hrank2
      -- The rank bound leaves only `ct1Sampled`; `omega` refutes the two lower ranks.
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

private theorem receive_headerSent_preserves_statePairInv
    (P : Parameters ProbComp) [DecidableEq P.Sym]
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (s : SCKAScheme.GameState
      (State P AuthState) (State P AuthState)
      P.EpochKey (Message P.Sym))
    (hs : ControlInv s ∧ StatePairInv s)
    (party : Bool)
    (e : ℕ) (a : AuthState) (sk : P.SK)
    (ct1Decoder : DecoderState P.inc.C₁ P.Sym)
    (ekEncoder : EncoderState P.inc.PKvector P.Sym)
    (hst : (if party then s.stA else s.stB) =
      .headerSent e a sk ct1Decoder ekEncoder)
    (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ)
    (hmsg : (if party then s.msgB else s.msgA) n = some (msg, tsnd))
    (r : RecvResult P AuthState)
    (hr : receive P auth (.headerSent e a sk ct1Decoder ekEncoder) msg = .ok r) :
    StatePairInv
      (if party then { s with stA := r.state }
       else { s with stB := r.state }) := by
  -- Reduce the concrete handler once: the state is literally unchanged, or a `ct1` chunk of
  -- epoch `e` updates the decoder (same constructor) or completes `ct1` (`ct1Received`).
  have houtcome :
      r.state = .headerSent e a sk ct1Decoder ekEncoder ∨
      (msg.epoch = e ∧
        ((∃ dec, r.state = .headerSent e a sk dec ekEncoder) ∨
          ∃ ct1, r.state = .ct1Received e a sk ct1 ekEncoder)) := by
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
  · -- B receives a message recorded in A's table.
    simp only [Bool.false_eq_true, ↓reduceIte] at hst hmsg ⊢
    rcases houtcome with hsame | ⟨hepoch, hnew⟩
    · -- Unchanged state: transport the original invariant.
      rw [hsame, ← hst]
      exact hPair
    · have hle : msg.epoch ≤ s.stA.epoch := (hA.2.2 n msg tsnd hmsg).2.1
      have hposB : 0 < s.stB.epoch := hEpoch.1.2.1
      have hepochB : s.stB.epoch = e := by
        rw [hst]
        rfl
      have hcompleted : s.stB.completedEpoch = e - 1 := by
        rw [hst]
        rfl
      have hboundA : s.stA.epoch ≤ s.stB.completedEpoch + 1 := hEpoch.2.1
      have heqA : s.stA.epoch = e := by omega
      have hpairB := hPair false
      simp only [Bool.false_eq_true, ↓reduceIte] at hpairB
      have hallowed := hpairB.1 (by omega) (by rw [hst]; rfl)
      rw [hst] at hallowed
      -- The original table admits only `ct1Sampled` and `ekReceivedCt1Sampled` peers.
      cases hb : s.stA <;>
        simp only [hb, State.epoch] at hallowed heqA
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
  · -- A receives a message recorded in B's table.
    simp only [if_true] at hst hmsg ⊢
    rcases houtcome with hsame | ⟨hepoch, hnew⟩
    · -- Unchanged state: transport the original invariant.
      rw [hsame, ← hst]
      exact hPair
    · have hle : msg.epoch ≤ s.stB.epoch := (hB.2.2 n msg tsnd hmsg).2.1
      have hposA : 0 < s.stA.epoch := hEpoch.1.1
      have hepochA : s.stA.epoch = e := by
        rw [hst]
        rfl
      have hcompleted : s.stA.completedEpoch = e - 1 := by
        rw [hst]
        rfl
      have hboundB : s.stB.epoch ≤ s.stA.completedEpoch + 1 := hEpoch.2.2.1
      have heqB : s.stB.epoch = e := by omega
      have hpairA := hPair true
      simp only [if_true] at hpairA
      have hallowed := hpairA.1 (by omega) (by rw [hst]; rfl)
      rw [hst] at hallowed
      -- The original table admits only `ct1Sampled` and `ekReceivedCt1Sampled` peers.
      cases hb : s.stB <;>
        simp only [hb, State.epoch] at hallowed heqB
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

private theorem receive_ct1Received_preserves_statePairInv
    (P : Parameters ProbComp) [DecidableEq P.Sym]
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (s : SCKAScheme.GameState
      (State P AuthState) (State P AuthState)
      P.EpochKey (Message P.Sym))
    (hs : ControlInv s ∧ StatePairInv s)
    (party : Bool)
    (e : ℕ) (a : AuthState) (sk : P.SK) (ct1 : P.inc.C₁)
    (ekEncoder : EncoderState P.inc.PKvector P.Sym)
    (hst : (if party then s.stA else s.stB) =
      .ct1Received e a sk ct1 ekEncoder)
    (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ)
    (hmsg : (if party then s.msgB else s.msgA) n = some (msg, tsnd))
    (r : RecvResult P AuthState)
    (hr : receive P auth (.ct1Received e a sk ct1 ekEncoder) msg = .ok r) :
    StatePairInv
      (if party then { s with stA := r.state }
       else { s with stB := r.state }) := by
  -- Reduce the concrete handler once: the state is literally unchanged, or the first `ct2`
  -- chunk of epoch `e` moves it to `ekSentCt1Received`.
  have houtcome :
      r.state = .ct1Received e a sk ct1 ekEncoder ∨
      (msg.type = .ct2 ∧ msg.epoch = e ∧
        ∃ chunk, r.state = .ekSentCt1Received e a sk ct1
          ((DecoderState.empty P.ecpCt2).addChunk chunk)) := by
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
  · -- B receives a message recorded in A's table.
    simp only [Bool.false_eq_true, ↓reduceIte] at hst hmsg ⊢
    rcases houtcome with hsame | ⟨htype, hepoch, _, hnew⟩
    · -- Unchanged state: transport the original invariant.
      rw [hsame, ← hst]
      exact hPair
    · have hmsgCtl := hA.2.2 n msg tsnd hmsg
      simp only [htype, hepoch] at hmsgCtl
      obtain ⟨-, hle, -, hrank⟩ := hmsgCtl
      have hposB : 0 < s.stB.epoch := hEpoch.1.2.1
      have hepochB : s.stB.epoch = e := by
        rw [hst]
        rfl
      have hcompleted : s.stB.completedEpoch = e - 1 := by
        rw [hst]
        rfl
      have hboundA : s.stA.epoch ≤ s.stB.completedEpoch + 1 := hEpoch.2.1
      have heqA : s.stA.epoch = e := by omega
      have hrank2 : 4 ≤ s.stA.controlPosition.2 := hrank heqA.symm
      have hpairB := hPair false
      simp only [Bool.false_eq_true, ↓reduceIte] at hpairB
      have hallowed := hpairB.1 (by omega) (by rw [hst]; rfl)
      rw [hst] at hallowed
      rw [hnew]
      cases hb : s.stA <;>
        simp only [hb, State.epoch, State.controlPosition] at hallowed heqA hrank2
      -- The `ct2` rank bound leaves only `ct2Sampled`; `omega` refutes the lower ranks.
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
  · -- A receives a message recorded in B's table.
    simp only [if_true] at hst hmsg ⊢
    rcases houtcome with hsame | ⟨htype, hepoch, _, hnew⟩
    · -- Unchanged state: transport the original invariant.
      rw [hsame, ← hst]
      exact hPair
    · have hmsgCtl := hB.2.2 n msg tsnd hmsg
      simp only [htype, hepoch] at hmsgCtl
      obtain ⟨-, hle, -, hrank⟩ := hmsgCtl
      have hposA : 0 < s.stA.epoch := hEpoch.1.1
      have hepochA : s.stA.epoch = e := by
        rw [hst]
        rfl
      have hcompleted : s.stA.completedEpoch = e - 1 := by
        rw [hst]
        rfl
      have hboundB : s.stB.epoch ≤ s.stA.completedEpoch + 1 := hEpoch.2.2.1
      have heqB : s.stB.epoch = e := by omega
      have hrank2 : 4 ≤ s.stB.controlPosition.2 := hrank heqB.symm
      have hpairA := hPair true
      simp only [if_true] at hpairA
      have hallowed := hpairA.1 (by omega) (by rw [hst]; rfl)
      rw [hst] at hallowed
      rw [hnew]
      cases hb : s.stB <;>
        simp only [hb, State.epoch, State.controlPosition] at hallowed heqB hrank2
      -- The `ct2` rank bound leaves only `ct2Sampled`; `omega` refutes the lower ranks.
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

private theorem receive_ekSentCt1Received_preserves_statePairInv
    (P : Parameters ProbComp) [DecidableEq P.Sym]
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (s : SCKAScheme.GameState
      (State P AuthState) (State P AuthState)
      P.EpochKey (Message P.Sym))
    (hs : ControlInv s ∧ StatePairInv s)
    (party : Bool)
    (e : ℕ) (a : AuthState) (sk : P.SK) (ct1 : P.inc.C₁)
    (ct2Decoder : DecoderState (P.inc.C₂ × P.Mac) P.Sym)
    (hst : (if party then s.stA else s.stB) =
      .ekSentCt1Received e a sk ct1 ct2Decoder)
    (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ)
    (hmsg : (if party then s.msgB else s.msgA) n = some (msg, tsnd))
    (r : RecvResult P AuthState)
    (hr : receive P auth (.ekSentCt1Received e a sk ct1 ct2Decoder) msg = .ok r) :
    StatePairInv
      (if party then { s with stA := r.state }
       else { s with stB := r.state }) := by
  -- Reduce the concrete handler once: the state is literally unchanged, or a `ct2` chunk of
  -- epoch `e` updates the decoder (same constructor) or completes the epoch, advancing to
  -- `noHeaderReceived (e + 1)`.
  have houtcome :
      r.state = .ekSentCt1Received e a sk ct1 ct2Decoder ∨
      (msg.epoch = e ∧
        ((∃ dec, r.state = .ekSentCt1Received e a sk ct1 dec) ∨
          ∃ a' dec, r.state = .noHeaderReceived (e + 1) a' dec)) := by
    simp only [receive] at hr
    repeat' split at hr
    all_goals cases hr
    all_goals first
      | exact Or.inr ⟨by assumption, Or.inl ⟨_, rfl⟩⟩
      | exact Or.inr ⟨by assumption, Or.inr ⟨_, _, rfl⟩⟩
      | exact Or.inl rfl
  obtain ⟨⟨hEpoch, -, -, -, hcontrol⟩, hPair⟩ := hs
  have hA := hcontrol true
  have hB := hcontrol false
  simp only [if_true] at hA
  simp only [Bool.false_eq_true, ↓reduceIte] at hB
  cases party
  · -- B receives a message recorded in A's table.
    simp only [Bool.false_eq_true, ↓reduceIte] at hst hmsg ⊢
    rcases houtcome with hsame | ⟨hepoch, hnew⟩
    · -- Unchanged state: transport the original invariant.
      rw [hsame, ← hst]
      exact hPair
    · have hle : msg.epoch ≤ s.stA.epoch := (hA.2.2 n msg tsnd hmsg).2.1
      have hposB : 0 < s.stB.epoch := hEpoch.1.2.1
      have hepochB : s.stB.epoch = e := by
        rw [hst]
        rfl
      have hcompleted : s.stB.completedEpoch = e - 1 := by
        rw [hst]
        rfl
      have hboundA : s.stA.epoch ≤ s.stB.completedEpoch + 1 := hEpoch.2.1
      have heqA : s.stA.epoch = e := by omega
      have hpairB := hPair false
      simp only [Bool.false_eq_true, ↓reduceIte] at hpairB
      have hallowed := hpairB.1 (by omega) (by rw [hst]; rfl)
      rw [hst] at hallowed
      -- The original table admits only a `ct2Sampled` peer.
      cases hb : s.stA <;>
        simp only [hb, State.epoch] at hallowed heqA
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
            -- After the epoch advance, the lag clause is realized by the actual states.
            first | omega | exact ⟨_, _, _, _, rfl, by rw [heqA]⟩
  · -- A receives a message recorded in B's table.
    simp only [if_true] at hst hmsg ⊢
    rcases houtcome with hsame | ⟨hepoch, hnew⟩
    · -- Unchanged state: transport the original invariant.
      rw [hsame, ← hst]
      exact hPair
    · have hle : msg.epoch ≤ s.stB.epoch := (hB.2.2 n msg tsnd hmsg).2.1
      have hposA : 0 < s.stA.epoch := hEpoch.1.1
      have hepochA : s.stA.epoch = e := by
        rw [hst]
        rfl
      have hcompleted : s.stA.completedEpoch = e - 1 := by
        rw [hst]
        rfl
      have hboundB : s.stB.epoch ≤ s.stA.completedEpoch + 1 := hEpoch.2.2.1
      have heqB : s.stB.epoch = e := by omega
      have hpairA := hPair true
      simp only [if_true] at hpairA
      have hallowed := hpairA.1 (by omega) (by rw [hst]; rfl)
      rw [hst] at hallowed
      -- The original table admits only a `ct2Sampled` peer.
      cases hb : s.stB <;>
        simp only [hb, State.epoch] at hallowed heqB
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
            -- After the epoch advance, the lag clause is realized by the actual states.
            first | omega | exact ⟨_, _, _, _, rfl, by rw [heqB]⟩
        · simp only [if_true, State.epoch, State.controlPosition]
          constructor
          · intros
            trivial
          · intro hlag
            omega

namespace EpochSafetyInternal

theorem receive_generator_preserves_statePairInv
    (P : Parameters ProbComp) [DecidableEq P.Sym]
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (s : SCKAScheme.GameState
      (State P AuthState) (State P AuthState)
      P.EpochKey (Message P.Sym))
    (hs : ControlInv s ∧ StatePairInv s)
    (party : Bool) (n : ℕ) (msg : Message P.Sym) (tsnd : ℕ)
    (hmsg :
      (if party then s.msgB else s.msgA) n = some (msg, tsnd))
    (hgenerator :
      (if party then s.stA else s.stB).controlPosition.1 = true)
    (r : RecvResult P AuthState)
    (hr :
      receive P auth (if party then s.stA else s.stB) msg = .ok r) :
    StatePairInv
      (if party then { s with stA := r.state }
       else { s with stB := r.state }) := by
  -- Select the receiver constructor once; each concrete-field leaf is then applied with the
  -- same message and result telescope.
  obtain ⟨st, hst⟩ : ∃ st, (if party then s.stA else s.stB) = st := ⟨_, rfl⟩
  rw [hst] at hgenerator hr
  cases st <;> simp only [State.controlPosition, Bool.false_eq_true] at hgenerator
  case keysUnsampled e a =>
    -- `keysUnsampled` ignores every message: transport the original invariant.
    have hsame : r.state = .keysUnsampled e a := by
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
  case keysSampled e a sk ekVector headerEncoder =>
    exact receive_keysSampled_preserves_statePairInv P auth s hs party
      e a sk ekVector headerEncoder hst n msg tsnd hmsg r hr
  case headerSent e a sk ct1Decoder ekEncoder =>
    exact receive_headerSent_preserves_statePairInv P auth s hs party
      e a sk ct1Decoder ekEncoder hst n msg tsnd hmsg r hr
  case ct1Received e a sk ct1 ekEncoder =>
    exact receive_ct1Received_preserves_statePairInv P auth s hs party
      e a sk ct1 ekEncoder hst n msg tsnd hmsg r hr
  case ekSentCt1Received e a sk ct1 ct2Decoder =>
    exact receive_ekSentCt1Received_preserves_statePairInv P auth s hs party
      e a sk ct1 ct2Decoder hst n msg tsnd hmsg r hr

end EpochSafetyInternal

end MLKEMBraid
