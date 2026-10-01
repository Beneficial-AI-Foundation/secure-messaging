/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Gavran, Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Correctness.SendProvenance
import SecureMessaging.SCKA.OppBiKEM.Correctness.ReceiveState

/-! # Public-key epoch history for Opp-BiKEM correctness -/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

def PublicKeyEpochHistory
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (msgs : ℕ → Option (Message Sym × ℕ))
    (st : State PK SK C Sym)
    (hist : ℤ → Option PK) : Prop :=
  (∀ (n : ℕ) (ρ : Message Sym) (tsnd : ℕ),
    msgs n = some (ρ, tsnd) →
      ∃ (st₀ : State PK SK C Sym) (key? : Option (ℕ × K))
        (st₁ : State PK SK C Sym),
        some (key?, ρ, tsnd, st₁) ∈
          support (send role kem ecEk ecCt st₀) ∧
        SendProvenance role kem ecEk ecCt st₀ key? ρ tsnd st₁ ∧
        ρ.tRes ≤ st.res.resEpoch ∧
        (∀ pk : PK, st₁.req.ek = some pk →
          hist (ρ.tRes + role.offset) = some pk)) ∧
  (∀ pk : PK, st.req.ek = some pk →
    hist (st.res.resEpoch + role.offset) = some pk)

def GamePublicKeyEpochHistory
    (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (s : SCKAScheme.GameState
      (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) : Prop :=
  (∃ hist : ℤ → Option PK,
    PublicKeyEpochHistory .A kem ecEk ecCt s.msgA s.stA hist) ∧
  (∃ hist : ℤ → Option PK,
    PublicKeyEpochHistory .B kem ecEk ecCt s.msgB s.stB hist)

theorem recv_local_publicKey_eq_or_none
    [DecidableEq Sym]
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym)
    (key? : Option (ℕ × K)) (trcv : ℕ) (st' : State PK SK C Sym)
    (hout : recv role kem hDet ecEk ecCt st ρ = some (key?, trcv, st')) :
    st'.req.ek = st.req.ek ∨ st'.req.ek = none := by
  have hproj := congrArg
    (Option.map fun out : Option (ℕ × K) × ℕ × State PK SK C Sym =>
      out.2.2.req.ek) hout
  simp only [Option.map_some] at hproj
  rw [recv] at hproj
  dsimp only at hproj
  by_cases hctRec : ρ.ack.ctRec = true <;>
    simp only [hctRec, Bool.false_eq_true, if_true, if_false] at hproj
  all_goals
    by_cases hekRec : ρ.ack.ekRec = true <;>
      simp only [hekRec, Bool.false_eq_true, if_true, if_false] at hproj
  all_goals
    by_cases hstale : ρ.tRes < st.req.reqEpoch <;>
      simp only [hstale, if_true, if_false] at hproj
  all_goals try
    (simp only [Option.pure_def, Option.map_some] at hproj
     exact Or.inl (Option.some.inj hproj).symm)
  all_goals
    by_cases hadvance : st.req.reqEpoch < ρ.tRes <;>
      simp only [hadvance, if_true, if_false] at hproj
  all_goals
    by_cases hpk :
        (st.res.ekPeer
          ((if st.req.reqEpoch < ρ.tRes then st.req.reqEpoch + 2
            else st.req.reqEpoch) - role.offset)).isNone = true ∧
        ρ.bit = some 0
    · simp only [hadvance, if_true, if_false] at hpk
      simp only [hpk] at hproj
      simp only [true_and, if_true] at hproj
      cases hdecode : (insertChunkAndDecode ecEk st.req.receivedChunks ρ.ch).2 <;>
        simp only [hdecode] at hproj
      all_goals
        repeat' split at hproj
        try simp only [Option.pure_def, Option.map_some] at hproj
        all_goals first
          | exact Or.inl (Option.some.inj hproj).symm
          | exact Or.inr (Option.some.inj hproj).symm
    · simp only [hadvance, if_true, if_false] at hpk
      simp only [hpk, if_false] at hproj
      repeat' split at hproj
      all_goals try simp only [Option.bind_eq_bind,
        Option.bind] at hproj
      all_goals repeat' split at hproj
      all_goals try simp only [Option.pure_def, Option.map_some,
        Option.map_none] at hproj
      all_goals repeat' split at hproj
      all_goals try simp only [Option.map_some, Option.map_none] at hproj
      all_goals try cases hproj
      all_goals first
        | exact Or.inl (Option.some.inj hproj).symm
        | exact Or.inr (Option.some.inj hproj).symm

theorem initGameState_publicKeyEpochHistory
    (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (stA : StA PK SK C Sym) (stB : StB PK SK C Sym) :
    GamePublicKeyEpochHistory kem ecEk ecCt
      (SCKAScheme.initGameState stA stB) := by
  refine ⟨⟨Function.update (fun _ => none)
    (stA.res.resEpoch + Role.A.offset) stA.req.ek, ?_⟩,
    ⟨Function.update (fun _ => none)
    (stB.res.resEpoch + Role.B.offset) stB.req.ek, ?_⟩⟩
  all_goals
    constructor
    · intro n ρ tsnd h
      simp [SCKAScheme.initGameState] at h
    · intro pk hpk
      simpa only [SCKAScheme.initGameState, Function.update_self] using hpk

theorem publicKeyEpochHistory_record_send
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (msgs : ℕ → Option (Message Sym × ℕ))
    (st : State PK SK C Sym) (hist : ℤ → Option PK)
    (hs : PublicKeyEpochHistory role kem ecEk ecCt msgs st hist)
    (n : ℕ) (key? : Option (ℕ × K)) (ρ : Message Sym) (tsnd : ℕ)
    (st' : State PK SK C Sym)
    (hout : some (key?, ρ, tsnd, st') ∈
      support (send role kem ecEk ecCt st)) :
    ∃ hist' : ℤ → Option PK,
      (hist' = hist ∨
        ∃ pk : PK, st'.req.ek = some pk ∧
          st'.res.resEpoch = st.res.resEpoch + 2 ∧
          hist' = Function.update hist (st'.res.resEpoch + role.offset) (some pk)) ∧
      PublicKeyEpochHistory role kem ecEk ecCt
        (Function.update msgs n (some (ρ, tsnd))) st' hist' := by
  obtain ⟨hmsgs, hlocal⟩ := hs
  have hp := send_provenance role kem ecEk ecCt st key? ρ tsnd st' hout
  rcases hp.keygen_transition with hsame | ⟨newPk, _, _, hepoch, hek, _⟩
  · rcases hsame with ⟨hepoch, _, hek⟩
    refine ⟨hist, Or.inl rfl, ?_⟩
    constructor
    · intro j msg t hentry
      by_cases hj : j = n
      · subst j
        simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hentry
        rcases hentry with ⟨rfl, rfl⟩
        refine ⟨st, key?, st', hout, hp, ?_, ?_⟩
        · exact le_of_eq hp.message_resEpoch
        · intro pk hpk
          have hpk₀ : st.req.ek = some pk := by simpa only [hek] using hpk
          simpa only [hp.message_resEpoch, hepoch] using hlocal pk hpk₀
      · rw [Function.update_of_ne hj] at hentry
        obtain ⟨st₀, key₀, st₁, hsend, hprov, hle, hhist⟩ :=
          hmsgs j msg t hentry
        exact ⟨st₀, key₀, st₁, hsend, hprov, by simpa only [hepoch] using hle, hhist⟩
    · intro pk hpk
      have hpk₀ : st.req.ek = some pk := by simpa only [hek] using hpk
      simpa only [hepoch] using hlocal pk hpk₀
  · let hist' : ℤ → Option PK :=
      Function.update hist (st'.res.resEpoch + role.offset) (some newPk)
    refine ⟨hist', Or.inr ⟨newPk, hek, hepoch, rfl⟩, ?_⟩
    constructor
    · intro j msg t hentry
      by_cases hj : j = n
      · subst j
        simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hentry
        rcases hentry with ⟨rfl, rfl⟩
        refine ⟨st, key?, st', hout, hp, le_of_eq hp.message_resEpoch, ?_⟩
        intro pk hpk
        have hpkEq : pk = newPk := Option.some.inj (hpk.symm.trans hek)
        subst pk
        simp only [hp.message_resEpoch, hist', Function.update_self]
      · rw [Function.update_of_ne hj] at hentry
        obtain ⟨st₀, key₀, st₁, hsend, hprov, hle, hhist⟩ :=
          hmsgs j msg t hentry
        refine ⟨st₀, key₀, st₁, hsend, hprov, by omega, ?_⟩
        intro pk hpk
        have hne : msg.tRes + role.offset ≠ st'.res.resEpoch + role.offset := by
          omega
        simpa only [hist', Function.update_of_ne hne] using hhist pk hpk
    · intro pk hpk
      have hpkEq : pk = newPk := Option.some.inj (hpk.symm.trans hek)
      subst pk
      simp only [hist', Function.update_self]

theorem publicKeyEpochHistory_same_epoch_chunks
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (msgs : ℕ → Option (Message Sym × ℕ))
    (st : State PK SK C Sym) (hist : ℤ → Option PK)
    (hs : PublicKeyEpochHistory role kem ecEk ecCt msgs st hist)
    (n₁ n₂ : ℕ) (ρ₁ ρ₂ : Message Sym) (t₁ t₂ : ℕ)
    (h₁ : msgs n₁ = some (ρ₁, t₁)) (h₂ : msgs n₂ = some (ρ₂, t₂))
    (hbit₁ : ρ₁.bit = some 0) (hbit₂ : ρ₂.bit = some 0)
    (htRes : ρ₁.tRes = ρ₂.tRes) :
    ∃ (pk : PK) (i₁ i₂ : ℕ),
      ρ₁.ch = some (ecEk.encode pk i₁) ∧
      ρ₂.ch = some (ecEk.encode pk i₂) := by
  obtain ⟨hmsgs, _⟩ := hs
  obtain ⟨st₀₁, key₁, st₁, _, hp₁, _, hhist₁⟩ :=
    hmsgs n₁ ρ₁ t₁ h₁
  obtain ⟨st₀₂, key₂, st₂, _, hp₂, _, hhist₂⟩ :=
    hmsgs n₂ ρ₂ t₂ h₂
  obtain ⟨pk₁, hek₁, hch₁⟩ := hp₁.public_key_chunk hbit₁
  obtain ⟨pk₂, hek₂, hch₂⟩ := hp₂.public_key_chunk hbit₂
  have hsame : pk₁ = pk₂ := by
    have hhist₂' : hist (ρ₁.tRes + role.offset) = some pk₂ := by
      simpa only [htRes] using hhist₂ pk₂ hek₂
    exact Option.some.inj ((hhist₁ pk₁ hek₁).symm.trans hhist₂')
  subst pk₂
  exact ⟨pk₁, st₁.res.ich, st₂.res.ich, hch₁, hch₂⟩

theorem sckaCorrectnessImpl_preserves_publicKeyEpochHistory
    [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak) :
    QueryImpl.PreservesInv
      (SCKAScheme.sckaCorrectnessImpl
        (scheme kem hDet ecEk ecCt leak))
      (GamePublicKeyEpochHistory kem ecEk ecCt) := by
  have recv_preserves
      (role : Role) (msgs : ℕ → Option (Message Sym × ℕ))
      (st : State PK SK C Sym) (hist : ℤ → Option PK)
      (hs : PublicKeyEpochHistory role kem ecEk ecCt msgs st hist)
      (ρ : Message Sym) (key? : Option (ℕ × K))
      (trcv : ℕ) (st' : State PK SK C Sym)
      (hout : recv role kem hDet ecEk ecCt st ρ = some (key?, trcv, st')) :
      PublicKeyEpochHistory role kem ecEk ecCt msgs st' hist := by
    obtain ⟨hmsgs, hlocal⟩ := hs
    have hepoch :=
      (recv_success_state_facts role kem hDet ecEk ecCt st ρ key? trcv st' hout).2.1
    have hek := recv_local_publicKey_eq_or_none role kem hDet ecEk ecCt
      st ρ key? trcv st' hout
    constructor
    · intro j msg epoch hentry
      obtain ⟨st₀, key₀, st₁, hsend, hprov, hle, hhist⟩ :=
        hmsgs j msg epoch hentry
      exact ⟨st₀, key₀, st₁, hsend, hprov,
        by simpa only [hepoch] using hle, hhist⟩
    · intro pk hpk
      rcases hek with hkeep | hclear
      · have hpk₀ : st.req.ek = some pk := by simpa only [hkeep] using hpk
        simpa only [hepoch] using hlocal pk hpk₀
      · rw [hclear] at hpk
        cases hpk
  intro t s hs z hz
  rcases t with (((n | ⟨⟩) | ⟨⟩) | n) | n
  · have hz' : z ∈ support (((QueryImpl.ofLift unifSpec ProbComp) n) >>=
        fun y => pure (y, s)) := hz
    obtain ⟨_, _, hz⟩ := mem_support_bind_peel _ _ hz'
    have hz' := eq_of_mem_support_pure _ hz
    subst z
    exact hs
  · change z ∈ support
      ((SCKAScheme.oracleSendA (scheme kem hDet ecEk ecCt leak) ()).run s) at hz
    rcases z with ⟨out, s'⟩
    cases out with
    | none =>
        simp only [SCKAScheme.oracleSendA, StateT.run_bind, StateT.run_get, pure_bind,
          StateT.run_liftM, bind_assoc] at hz
        obtain ⟨localOut, _, hz⟩ := mem_support_bind_peel _ _ hz
        cases localOut with
        | none =>
            have hz' := eq_of_mem_support_pure _ hz
            have hs' : s' = s := congrArg Prod.snd hz'
            subst s'
            exact hs
        | some localOut =>
            rcases localOut with ⟨key?, ρ, tsnd, st'⟩
            cases key? <;>
              have hz' := congrArg Prod.fst (eq_of_mem_support_pure _ hz) <;>
              simp at hz'
    | some out =>
        rcases out with ⟨tsnd, epoch?, ρ⟩
        obtain ⟨key?, _, hsend, _, hstB, hmsgA, hmsgB, _, _⟩ :=
          oracleSendA_recorded_provenance kem hDet ecEk ecCt leak
            s s' tsnd epoch? ρ hz
        obtain ⟨histA, hA⟩ := hs.1
        obtain ⟨histB, hB⟩ := hs.2
        obtain ⟨histA', _, hA'⟩ := publicKeyEpochHistory_record_send
          .A kem ecEk ecCt s.msgA s.stA histA hA (s.nA + 1)
          key? ρ tsnd s'.stA hsend
        refine ⟨⟨histA', ?_⟩, ⟨histB, ?_⟩⟩
        · rw [hmsgA]
          exact hA'
        · rw [hmsgB, hstB]
          exact hB
  · change z ∈ support
      ((SCKAScheme.oracleSendB (scheme kem hDet ecEk ecCt leak) ()).run s) at hz
    rcases z with ⟨out, s'⟩
    cases out with
    | none =>
        simp only [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get, pure_bind,
          StateT.run_liftM, bind_assoc] at hz
        obtain ⟨localOut, _, hz⟩ := mem_support_bind_peel _ _ hz
        cases localOut with
        | none =>
            have hz' := eq_of_mem_support_pure _ hz
            have hs' : s' = s := congrArg Prod.snd hz'
            subst s'
            exact hs
        | some localOut =>
            rcases localOut with ⟨key?, ρ, tsnd, st'⟩
            cases key? <;>
              have hz' := congrArg Prod.fst (eq_of_mem_support_pure _ hz) <;>
              simp at hz'
    | some out =>
        rcases out with ⟨tsnd, epoch?, ρ⟩
        obtain ⟨key?, _, hsend, _, hstA, hmsgB, hmsgA, _, _⟩ :=
          oracleSendB_recorded_provenance kem hDet ecEk ecCt leak
            s s' tsnd epoch? ρ hz
        obtain ⟨histA, hA⟩ := hs.1
        obtain ⟨histB, hB⟩ := hs.2
        obtain ⟨histB', _, hB'⟩ := publicKeyEpochHistory_record_send
          .B kem ecEk ecCt s.msgB s.stB histB hB (s.nB + 1)
          key? ρ tsnd s'.stB hsend
        refine ⟨⟨histA, ?_⟩, ⟨histB', ?_⟩⟩
        · rw [hmsgA, hstA]
          exact hA
        · rw [hmsgB]
          exact hB'
  · change z ∈ support
      ((SCKAScheme.oracleRecvA (scheme kem hDet ecEk ecCt leak) n).run s) at hz
    cases hmsg : s.msgB n with
    | none =>
        have hz' : z ∈ ({(none, s)} : Set _) := by
          simpa [SCKAScheme.oracleRecvA, hmsg] using hz
        have hz'' : z = (none, s) := Set.mem_singleton_iff.mp hz'
        subst z
        exact hs
    | some entry =>
        rcases entry with ⟨ρ, tsnd⟩
        cases hrecv : (scheme kem hDet ecEk ecCt leak).recvA s.stA ρ with
        | none =>
            simp only [SCKAScheme.oracleRecvA, bind_pure_comp, StateT.run_bind,
              StateT.run_get, pure_bind, hmsg, hrecv, StateT.run_map, StateT.run_set,
              map_pure, support_pure] at hz
            subst z
            exact hs
        | some out =>
            rcases out with ⟨key?, trcv, st'⟩
            obtain ⟨histA, hA⟩ := hs.1
            have hlocal := recv_preserves .A s.msgA s.stA histA hA
              ρ key? trcv st' hrecv
            cases key? <;>
              simp only [SCKAScheme.oracleRecvA, bind_pure_comp, StateT.run_bind,
                StateT.run_get, pure_bind, hmsg, hrecv, StateT.run_map, StateT.run_set,
                map_pure, support_pure] at hz <;>
              subst z <;>
              exact ⟨⟨histA, hlocal⟩, hs.2⟩
  · change z ∈ support
      ((SCKAScheme.oracleRecvB (scheme kem hDet ecEk ecCt leak) n).run s) at hz
    cases hmsg : s.msgA n with
    | none =>
        have hz' : z ∈ ({(none, s)} : Set _) := by
          simpa [SCKAScheme.oracleRecvB, hmsg] using hz
        have hz'' : z = (none, s) := Set.mem_singleton_iff.mp hz'
        subst z
        exact hs
    | some entry =>
        rcases entry with ⟨ρ, tsnd⟩
        cases hrecv : (scheme kem hDet ecEk ecCt leak).recvB s.stB ρ with
        | none =>
            simp only [SCKAScheme.oracleRecvB, bind_pure_comp, StateT.run_bind,
              StateT.run_get, pure_bind, hmsg, hrecv, StateT.run_map, StateT.run_set,
              map_pure, support_pure] at hz
            subst z
            exact hs
        | some out =>
            rcases out with ⟨key?, trcv, st'⟩
            obtain ⟨histB, hB⟩ := hs.2
            have hlocal := recv_preserves .B s.msgB s.stB histB hB
              ρ key? trcv st' hrecv
            cases key? <;>
              simp only [SCKAScheme.oracleRecvB, bind_pure_comp, StateT.run_bind,
                StateT.run_get, pure_bind, hmsg, hrecv, StateT.run_map, StateT.run_set,
                map_pure, support_pure] at hz <;>
              subst z <;>
              exact ⟨hs.1, ⟨histB, hlocal⟩⟩

theorem simulateQ_publicKeyEpochHistory
    [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (stA : StA PK SK C Sym) (stB : StB PK SK C Sym)
    (z : Bool × SCKAScheme.GameState
      (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hz : z ∈ support ((simulateQ
      (SCKAScheme.sckaCorrectnessImpl
        (scheme kem hDet ecEk ecCt leak)) adv).run
      (SCKAScheme.initGameState stA stB))) :
    GamePublicKeyEpochHistory kem ecEk ecCt z.2 := by
  exact simulateQ_run_preservesInv _ (GamePublicKeyEpochHistory kem ecEk ecCt)
    (sckaCorrectnessImpl_preserves_publicKeyEpochHistory kem hDet ecEk ecCt leak)
    adv _ (initGameState_publicKeyEpochHistory kem ecEk ecCt stA stB) z hz

end oppBiKemCKA
