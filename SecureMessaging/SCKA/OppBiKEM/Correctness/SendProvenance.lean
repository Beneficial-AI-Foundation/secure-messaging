/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Gavran, Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Correctness.Invariant
import SecureMessaging.SCKA.OppBiKEM.Correctness.SendB

/-!
# Opp-BiKEM supported-send provenance

This file records source-level provenance for every supported send output, connects it to both
correctness-game send handlers, and preserves the resulting message-table property through arbitrary
correctness-game query prefixes.
-/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

structure SendProvenance
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (key? : Option (ℕ × K))
    (ρ : Message Sym) (tsnd : ℕ) (st' : State PK SK C Sym) : Prop where
  message_resEpoch : ρ.tRes = st'.res.resEpoch
  message_reqEpoch : ρ.tReq = st.req.reqEpoch
  message_sendingEpoch : tsnd = ρ.sendingEpoch
  requester_epoch : st'.req.reqEpoch = st.req.reqEpoch
  peer_keys : st'.res.ekPeer = st.res.ekPeer
  received_chunks : st'.req.receivedChunks = st.req.receivedChunks
  acknowledgements : st'.ack = st.ack
  sending_horizon : tsnd = st.ack.sendingHorizon
  advertised_acknowledgements :
    ρ.ack.ekRec =
        decide (st.req.reqEpoch - role.offset ∈ st.ack.ekRec) ∧
      ρ.ack.ctRec = decide (st.req.reqEpoch ∈ st.ack.ctRec)
  keygen_transition :
    (st'.res.resEpoch = st.res.resEpoch ∧
      st'.req.dk = st.req.dk ∧ st'.req.ek = st.req.ek) ∨
    (∃ (pk : PK) (sk : SK),
      (pk, sk) ∈ support kem.keygen ∧
      st'.res.resEpoch = st.res.resEpoch + 2 ∧
      st'.req.ek = some pk ∧
      st'.req.dk =
        (st'.res.resEpoch + role.offset, sk) ::
          st.req.dk.filter
            (fun p => p.1 != (st'.res.resEpoch + role.offset)))
  no_key_ciphertext : key? = none → st'.res.ct = st.res.ct
  emitted_key :
    ∀ (t : ℕ) (key : K), key? = some (t, key) →
      t = st'.res.resEpoch.toNat ∧ ρ.bit = some 1 ∧
      ∃ (pk : PK) (ciphertext : C),
        st.res.ekPeer st'.res.resEpoch = some pk ∧
        (ciphertext, key) ∈ support (kem.encaps pk) ∧
        st'.res.ct = some ciphertext
  public_key_chunk :
    ρ.bit = some 0 →
      ∃ pk : PK,
        st'.req.ek = some pk ∧
        ρ.ch = some (ecEk.encode pk st'.res.ich)
  ciphertext_chunk :
    ρ.bit = some 1 →
      ρ.ch = st'.res.ct.map
        (fun ciphertext => ecCt.encode ciphertext st'.res.ich)
  absent_payload : ρ.bit = none → ρ.ch = none
  chunk_counter :
    st'.res.ich =
      (if st'.res.resEpoch = st.res.resEpoch ∧ key? = none then
        st.res.ich else 0) +
        (if ρ.bit = none then 0 else 1)

theorem send_provenance
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (key? : Option (ℕ × K))
    (ρ : Message Sym) (tsnd : ℕ) (st' : State PK SK C Sym)
    (hout : some (key?, ρ, tsnd, st') ∈
      support (send role kem ecEk ecCt st)) :
    SendProvenance role kem ecEk ecCt st key? ρ tsnd st' := by
  rw [send, mem_support_bind_iff] at hout
  obtain ⟨out, hout, hpure⟩ := hout
  cases out with
  | none => simp at hpure
  | some out =>
      rcases out with ⟨key, msg, epoch, state, rand⟩
      simp only [support_pure, Set.mem_singleton_iff, Option.map_some,
        Option.some.injEq, Prod.mk.injEq] at hpure
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hpure
      unfold sendWith at hout
      dsimp only at hout
      repeat' first
        | split at hout
        | (rw [mem_support_bind_iff] at hout; obtain ⟨x, hx, hout⟩ := hout)
      all_goals simp only [support_pure, Set.mem_singleton_iff,
        Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hout
      all_goals obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hout
      all_goals constructor <;>
        simp_all [Acknowledgements.sendingHorizon, Role.offset] <;>
        aesop

theorem oracleSendA_recorded_provenance
    [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak)
    (s s' : SCKAScheme.GameState
      (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (tsnd : ℕ) (epoch? : Option ℕ) (ρ : Message Sym)
    (hout : (some (tsnd, epoch?, ρ), s') ∈ support
      ((SCKAScheme.oracleSendA
        (scheme kem hDet ecEk ecCt leak) ()).run s)) :
    ∃ key? : Option (ℕ × K),
      epoch? = key?.map Prod.fst ∧
      some (key?, ρ, tsnd, s'.stA) ∈
        support (send .A kem ecEk ecCt s.stA) ∧
      SendProvenance .A kem ecEk ecCt
        s.stA key? ρ tsnd s'.stA ∧
      s'.stB = s.stB ∧
      s'.msgA = Function.update s.msgA (s.nA + 1) (some (ρ, tsnd)) ∧
      s'.msgB = s.msgB ∧
      s'.keyA =
        (match key? with
        | none => s.keyA
        | some (t, key) => Function.update s.keyA t (some key)) ∧
      s'.keyB = s.keyB := by
  simp only [SCKAScheme.oracleSendA, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_liftM, bind_assoc] at hout
  obtain ⟨out, hsend, hout⟩ := mem_support_bind_peel _ _ hout
  cases out with
  | none => simp at hout
  | some out =>
      rcases out with ⟨key?, msg, epoch, stA'⟩
      have hsend' : some (key?, msg, epoch, stA') ∈
          support (send .A kem ecEk ecCt s.stA) := by
        simpa only [scheme, sendA] using hsend
      have hprov := send_provenance .A kem ecEk ecCt s.stA
        key? msg epoch stA' hsend'
      cases key? with
      | none =>
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Option.some.injEq, Prod.mk.injEq] at hout
          rcases hout with ⟨⟨rfl, rfl, rfl⟩, rfl⟩
          exact ⟨none, rfl, hsend', hprov, rfl, rfl, rfl, rfl, rfl⟩
      | some keyOut =>
          rcases keyOut with ⟨t, key⟩
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Option.some.injEq, Prod.mk.injEq] at hout
          rcases hout with ⟨⟨rfl, rfl, rfl⟩, rfl⟩
          exact ⟨some (t, key), rfl, hsend', hprov, rfl, rfl, rfl, rfl, rfl⟩

theorem oracleSendB_recorded_provenance
    [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak)
    (s s' : SCKAScheme.GameState
      (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (tsnd : ℕ) (epoch? : Option ℕ) (ρ : Message Sym)
    (hout : (some (tsnd, epoch?, ρ), s') ∈ support
      ((SCKAScheme.oracleSendB
        (scheme kem hDet ecEk ecCt leak) ()).run s)) :
    ∃ key? : Option (ℕ × K),
      epoch? = key?.map Prod.fst ∧
      some (key?, ρ, tsnd, s'.stB) ∈
        support (send .B kem ecEk ecCt s.stB) ∧
      SendProvenance .B kem ecEk ecCt
        s.stB key? ρ tsnd s'.stB ∧
      s'.stA = s.stA ∧
      s'.msgB = Function.update s.msgB (s.nB + 1) (some (ρ, tsnd)) ∧
      s'.msgA = s.msgA ∧
      s'.keyB =
        (match key? with
        | none => s.keyB
        | some (t, key) => Function.update s.keyB t (some key)) ∧
      s'.keyA = s.keyA := by
  simp only [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_liftM, bind_assoc] at hout
  obtain ⟨out, hsend, hout⟩ := mem_support_bind_peel _ _ hout
  cases out with
  | none => simp at hout
  | some out =>
      rcases out with ⟨key?, msg, epoch, stB'⟩
      have hsend' : some (key?, msg, epoch, stB') ∈
          support (send .B kem ecEk ecCt s.stB) := by
        simpa only [scheme, sendB] using hsend
      have hprov := send_provenance .B kem ecEk ecCt s.stB
        key? msg epoch stB' hsend'
      cases key? with
      | none =>
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Option.some.injEq, Prod.mk.injEq] at hout
          rcases hout with ⟨⟨rfl, rfl, rfl⟩, rfl⟩
          exact ⟨none, rfl, hsend', hprov, rfl, rfl, rfl, rfl, rfl⟩
      | some keyOut =>
          rcases keyOut with ⟨t, key⟩
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Option.some.injEq, Prod.mk.injEq] at hout
          rcases hout with ⟨⟨rfl, rfl, rfl⟩, rfl⟩
          exact ⟨some (t, key), rfl, hsend', hprov, rfl, rfl, rfl, rfl, rfl⟩

def MessageSendProvenance
    (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (s : SCKAScheme.GameState
      (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) : Prop :=
  (∀ (n : ℕ) (ρ : Message Sym) (tsnd : ℕ),
    s.msgA n = some (ρ, tsnd) →
      ∃ (st : State PK SK C Sym) (key? : Option (ℕ × K))
        (st' : State PK SK C Sym),
        some (key?, ρ, tsnd, st') ∈
          support (send .A kem ecEk ecCt st) ∧
        SendProvenance .A kem ecEk ecCt st key? ρ tsnd st') ∧
  (∀ (n : ℕ) (ρ : Message Sym) (tsnd : ℕ),
    s.msgB n = some (ρ, tsnd) →
      ∃ (st : State PK SK C Sym) (key? : Option (ℕ × K))
        (st' : State PK SK C Sym),
        some (key?, ρ, tsnd, st') ∈
          support (send .B kem ecEk ecCt st) ∧
        SendProvenance .B kem ecEk ecCt st key? ρ tsnd st')

theorem initGameState_messageSendProvenance
    (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (stA : StA PK SK C Sym) (stB : StB PK SK C Sym) :
    MessageSendProvenance kem ecEk ecCt
      (SCKAScheme.initGameState stA stB) := by
  simp [MessageSendProvenance, SCKAScheme.initGameState]

theorem sckaCorrectnessImpl_preserves_messageSendProvenance
    [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak) :
    QueryImpl.PreservesInv
      (SCKAScheme.sckaCorrectnessImpl
        (scheme kem hDet ecEk ecCt leak))
      (MessageSendProvenance kem ecEk ecCt) := by
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
        obtain ⟨key?, _, hsend, hprov, _, hmsgA, hmsgB, _, _⟩ :=
          oracleSendA_recorded_provenance kem hDet ecEk ecCt leak
            s s' tsnd epoch? ρ hz
        refine ⟨?_, ?_⟩
        · intro j msg epoch hentry
          rw [hmsgA] at hentry
          by_cases hj : j = s.nA + 1
          · subst j
            simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hentry
            rcases hentry with ⟨rfl, rfl⟩
            exact ⟨s.stA, key?, s'.stA, hsend, hprov⟩
          · rw [Function.update_of_ne hj] at hentry
            exact hs.1 j msg epoch hentry
        · intro j msg epoch hentry
          rw [hmsgB] at hentry
          exact hs.2 j msg epoch hentry
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
        obtain ⟨key?, _, hsend, hprov, _, hmsgB, hmsgA, _, _⟩ :=
          oracleSendB_recorded_provenance kem hDet ecEk ecCt leak
            s s' tsnd epoch? ρ hz
        refine ⟨?_, ?_⟩
        · intro j msg epoch hentry
          rw [hmsgA] at hentry
          exact hs.1 j msg epoch hentry
        · intro j msg epoch hentry
          rw [hmsgB] at hentry
          by_cases hj : j = s.nB + 1
          · subst j
            simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hentry
            rcases hentry with ⟨rfl, rfl⟩
            exact ⟨s.stB, key?, s'.stB, hsend, hprov⟩
          · rw [Function.update_of_ne hj] at hentry
            exact hs.2 j msg epoch hentry
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
            cases key? <;>
              simp only [SCKAScheme.oracleRecvA, bind_pure_comp, StateT.run_bind,
                StateT.run_get, pure_bind, hmsg, hrecv, StateT.run_map, StateT.run_set,
                map_pure, support_pure] at hz <;>
              subst z <;>
              exact hs
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
            cases key? <;>
              simp only [SCKAScheme.oracleRecvB, bind_pure_comp, StateT.run_bind,
                StateT.run_get, pure_bind, hmsg, hrecv, StateT.run_map, StateT.run_set,
                map_pure, support_pure] at hz <;>
              subst z <;>
              exact hs

theorem simulateQ_messageSendProvenance
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
    MessageSendProvenance kem ecEk ecCt z.2 := by
  exact simulateQ_run_preservesInv _ (MessageSendProvenance kem ecEk ecCt)
    (sckaCorrectnessImpl_preserves_messageSendProvenance kem hDet ecEk ecCt leak)
    adv _ (initGameState_messageSendProvenance kem ecEk ecCt stA stB) z hz

end oppBiKemCKA
