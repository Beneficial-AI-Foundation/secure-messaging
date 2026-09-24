/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Construction
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv

/-!
# Opp-BiKEM message epochs

The message tables retain the sending epoch carried in each message. This property
holds throughout the correctness game, including failed receives, and gives epoch
matching whenever a recorded message is received successfully.
-/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

universe u

variable {K PK SK C Sym : Type}

/-- The send algorithm reports exactly the epoch stored in its outgoing message. -/
theorem sendWith_reports_message_sendingEpoch
  {RKey REnc : Type} (role : Role)
  (keygen : ProbComp ((PK × SK) × RKey))
  (encaps : PK → ProbComp ((C × K) × REnc))
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
  (st : State PK SK C Sym) (key? : Option (ℕ × K)) (ρ : Message Sym)
  (tsnd : ℕ) (st' : State PK SK C Sym) (rand : SendRand RKey REnc)
  (hout : some (key?, ρ, tsnd, st', rand) ∈ support (sendWith role keygen encaps ecEk ecCt st)) :
  tsnd = ρ.sendingEpoch := by
  unfold sendWith at hout
  dsimp only at hout
  repeat' first
    | split at hout
    | (rw [mem_support_bind_iff] at hout; obtain ⟨x, _, hout⟩ := hout)
  all_goals simp only [support_pure, Set.mem_singleton_iff,
    Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hout
  all_goals obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hout; rfl

/-- Discarding send randomness preserves the reported message epoch. -/
theorem send_reports_message_sendingEpoch
  (role : Role) (kem : KEMScheme ProbComp K PK SK C)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
  (st : State PK SK C Sym) (key? : Option (ℕ × K)) (ρ : Message Sym)
  (tsnd : ℕ) (st' : State PK SK C Sym)
  (hout : some (key?, ρ, tsnd, st') ∈ support (send role kem ecEk ecCt st)) :
  tsnd = ρ.sendingEpoch := by
  rw [send, mem_support_bind_iff] at hout
  obtain ⟨out, hmem, hout⟩ := hout
  cases out with
  | none => simp at hout
  | some out =>
    rcases out with ⟨key, msg, epoch, state, rand⟩
    simp only [support_pure, Set.mem_singleton_iff, Option.map_some,
      Option.some.injEq, Prod.mk.injEq] at hout
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hout
    exact sendWith_reports_message_sendingEpoch role _ _ ecEk ecCt st _ _ _ _ rand hmem

private theorem option_all_ite {α : Type} (p : Prop) [Decidable p]
    (a b : Option α) (f : α → Bool) :
    (if p then a else b).all f = if p then a.all f else b.all f := by
  split <;> rfl

/-- Every successful receive reports the message's explicit sending epoch. -/
theorem recv_reports_message_sendingEpoch
  {m : Type → Type u} [Monad m] (role : Role)
  (kem : KEMScheme m K PK SK C) [DecidableEq Sym]
  (hDet : kem.DeterministicDecaps) (ecEk : ErasureCodePayload PK Sym)
  (ecCt : ErasureCodePayload C Sym) (st : State PK SK C Sym) (ρ : Message Sym)
  (out : Option (ℕ × K) × ℕ × State PK SK C Sym)
  (hout : recv role kem hDet ecEk ecCt st ρ = some out) :
  out.2.1 = ρ.sendingEpoch := by
  have hepoch : (recv role kem hDet ecEk ecCt st ρ).all
      (fun x => x.2.1 == ρ.sendingEpoch) = true := by
    cases hek : (insertChunkAndDecode ecEk st.req.receivedChunks ρ.ch).2 <;>
      cases hct : (insertChunkAndDecode ecCt st.req.receivedChunks ρ.ch).2
    all_goals simp only [recv, hek, hct, option_all_ite, Option.pure_def, Option.all_some,
      beq_self_eq_true, ite_self, Option.bind_eq_bind, Option.all_bind,
      Function.comp_def, Option.all_true]
  simpa only [hout, Option.all_some, beq_iff_eq] using hepoch

/-- Both transit tables store the epoch carried by each recorded message. -/
def MessageEpochsConsistent
  (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) : Prop :=
  (∀ n ρ tsnd, s.msgA n = some (ρ, tsnd) → tsnd = ρ.sendingEpoch) ∧
  (∀ n ρ tsnd, s.msgB n = some (ρ, tsnd) → tsnd = ρ.sendingEpoch)

/-- Empty message tables satisfy message-epoch consistency for any initial local states. -/
theorem initGameState_messageEpochsConsistent
    (stA : StA PK SK C Sym) (stB : StB PK SK C Sym) :
    MessageEpochsConsistent (K := K) (SCKAScheme.initGameState stA stB) := by
  simp [MessageEpochsConsistent, SCKAScheme.initGameState]

private theorem messageTable_update
    (msgs : ℕ → Option (Message Sym × ℕ))
    (hmsgs : ∀ n ρ tsnd, msgs n = some (ρ, tsnd) → tsnd = ρ.sendingEpoch)
    (n : ℕ) (ρ : Message Sym) (tsnd : ℕ) (hepoch : tsnd = ρ.sendingEpoch) :
    ∀ j msg epoch, Function.update msgs n (some (ρ, tsnd)) j = some (msg, epoch) →
      epoch = msg.sendingEpoch := by
  intro j msg epoch hentry
  by_cases hj : j = n
  · subst j
    simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hentry
    obtain ⟨rfl, rfl⟩ := hentry
    exact hepoch
  · rw [Function.update_of_ne hj] at hentry
    exact hmsgs j msg epoch hentry

private theorem oracleRecvA_preserves_messageEpochsConsistent
    {IK Rand : Type} [DecidableEq K]
    (scka : SCKAScheme ProbComp IK (StA PK SK C Sym) (StB PK SK C Sym)
      K (Message Sym) Rand) :
    QueryImpl.PreservesInv (SCKAScheme.oracleRecvA scka) MessageEpochsConsistent := by
  intro n s hs z hz
  cases hmsg : s.msgB n with
  | none =>
    have hz' : z = (none, s) := by simpa [SCKAScheme.oracleRecvA, hmsg] using hz
    subst z
    exact hs
  | some entry =>
    rcases entry with ⟨ρ, tsnd⟩
    cases hrecv : scka.recvA s.stA ρ with
    | none =>
      simp only [SCKAScheme.oracleRecvA, bind_pure_comp, StateT.run_bind, StateT.run_get,
        pure_bind, hmsg, hrecv, StateT.run_map, StateT.run_set, map_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst z
      exact hs
    | some out =>
      rcases out with ⟨key?, trcv, st'⟩
      cases key? <;>
        simp only [SCKAScheme.oracleRecvA, bind_pure_comp, StateT.run_bind, StateT.run_get,
          pure_bind, hmsg, hrecv, StateT.run_map, StateT.run_set, map_pure, support_pure,
          Set.mem_singleton_iff] at hz <;>
        subst z <;>
        exact hs

private theorem oracleRecvB_preserves_messageEpochsConsistent
    {IK Rand : Type} [DecidableEq K]
    (scka : SCKAScheme ProbComp IK (StA PK SK C Sym) (StB PK SK C Sym)
      K (Message Sym) Rand) :
    QueryImpl.PreservesInv (SCKAScheme.oracleRecvB scka) MessageEpochsConsistent := by
  intro n s hs z hz
  cases hmsg : s.msgA n with
  | none =>
    have hz' : z = (none, s) := by simpa [SCKAScheme.oracleRecvB, hmsg] using hz
    subst z
    exact hs
  | some entry =>
    rcases entry with ⟨ρ, tsnd⟩
    cases hrecv : scka.recvB s.stB ρ with
    | none =>
      simp only [SCKAScheme.oracleRecvB, bind_pure_comp, StateT.run_bind, StateT.run_get,
        pure_bind, hmsg, hrecv, StateT.run_map, StateT.run_set, map_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst z
      exact hs
    | some out =>
      rcases out with ⟨key?, trcv, st'⟩
      cases key? <;>
        simp only [SCKAScheme.oracleRecvB, bind_pure_comp, StateT.run_bind, StateT.run_get,
          pure_bind, hmsg, hrecv, StateT.run_map, StateT.run_set, map_pure, support_pure,
          Set.mem_singleton_iff] at hz <;>
        subst z <;>
        exact hs

/-- Every correctness-game query preserves the message tables' epoch consistency. -/
theorem sckaCorrectnessImpl_preserves_messageEpochsConsistent
    [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak) :
    QueryImpl.PreservesInv
      (SCKAScheme.sckaCorrectnessImpl (scheme kem hDet ecEk ecCt leak))
      (MessageEpochsConsistent (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym)) := by
  intro t s hs z hz
  rcases t with (((n | ⟨⟩) | ⟨⟩) | n) | n
  · have hz' : z ∈ support (((QueryImpl.ofLift unifSpec ProbComp) n) >>=
        fun y => pure (y, s)) := hz
    obtain ⟨_, _, hz⟩ := mem_support_bind_peel _ _ hz'
    have hz' := eq_of_mem_support_pure _ hz
    subst z
    exact hs
  · change z ∈ support ((SCKAScheme.oracleSendA (scheme kem hDet ecEk ecCt leak) ()).run s)
      at hz
    simp only [SCKAScheme.oracleSendA, StateT.run_bind, StateT.run_get, pure_bind,
      StateT.run_liftM, bind_assoc] at hz
    obtain ⟨out, hout, hz⟩ := mem_support_bind_peel _ _ hz
    cases out with
    | none =>
      simp at hz
      subst z
      exact hs
    | some out =>
      rcases out with ⟨key?, ρ, tsnd, st'⟩
      have hepoch := send_reports_message_sendingEpoch .A kem ecEk ecCt s.stA
        key? ρ tsnd st' hout
      have htable := messageTable_update s.msgA hs.1 (s.nA + 1) ρ tsnd hepoch
      cases key? <;>
        simp at hz <;>
        subst z <;>
        exact ⟨htable, hs.2⟩
  · change z ∈ support ((SCKAScheme.oracleSendB (scheme kem hDet ecEk ecCt leak) ()).run s)
      at hz
    simp only [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get, pure_bind,
      StateT.run_liftM, bind_assoc] at hz
    obtain ⟨out, hout, hz⟩ := mem_support_bind_peel _ _ hz
    cases out with
    | none =>
      simp at hz
      subst z
      exact hs
    | some out =>
      rcases out with ⟨key?, ρ, tsnd, st'⟩
      have hepoch := send_reports_message_sendingEpoch .B kem ecEk ecCt s.stB
        key? ρ tsnd st' hout
      have htable := messageTable_update s.msgB hs.2 (s.nB + 1) ρ tsnd hepoch
      cases key? <;>
        simp at hz <;>
        subst z <;>
        exact ⟨hs.1, htable⟩
  · exact oracleRecvA_preserves_messageEpochsConsistent (scheme kem hDet ecEk ecCt leak)
      n s hs z hz
  · exact oracleRecvB_preserves_messageEpochsConsistent (scheme kem hDet ecEk ecCt leak)
      n s hs z hz

/-- Any adversary execution from empty message tables retains message-epoch consistency. -/
theorem simulateQ_messageEpochsConsistent
    [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak) (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (stA : StA PK SK C Sym) (stB : StB PK SK C Sym)
    (z : Bool × SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hz : z ∈ support ((simulateQ
      (SCKAScheme.sckaCorrectnessImpl (scheme kem hDet ecEk ecCt leak)) adv).run
      (SCKAScheme.initGameState stA stB))) :
    MessageEpochsConsistent z.2 := by
  exact simulateQ_run_preservesInv _ MessageEpochsConsistent
    (sckaCorrectnessImpl_preserves_messageEpochsConsistent kem hDet ecEk ecCt leak)
    adv _ (initGameState_messageEpochsConsistent stA stB) z hz

/-- A successful receive at A matches the epoch recorded with B's delivered message. -/
theorem oracleRecvA_matches_recorded_epoch
    [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak)
    (s s' : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : MessageEpochsConsistent s) (n trcv : ℕ) (tI : Option ℕ)
    (hout : (some (trcv, tI), s') ∈ support
      ((SCKAScheme.oracleRecvA (scheme kem hDet ecEk ecCt leak) n).run s)) :
    ∃ ρ : Message Sym, s.msgB n = some (ρ, trcv) ∧ ρ.sendingEpoch = trcv := by
  cases hmsg : s.msgB n with
  | none => simp [SCKAScheme.oracleRecvA, hmsg] at hout
  | some entry =>
    rcases entry with ⟨ρ, tsnd⟩
    cases hrecv : recv .A kem hDet ecEk ecCt s.stA ρ with
    | none => simp [SCKAScheme.oracleRecvA, hmsg, scheme, recvA, hrecv] at hout
    | some out =>
      rcases out with ⟨key?, epoch, st'⟩
      have hepoch := recv_reports_message_sendingEpoch .A kem hDet ecEk ecCt
        s.stA ρ (key?, epoch, st') hrecv
      have hrecord := hs.2 n ρ tsnd hmsg
      cases key? with
      | none =>
        simp only [SCKAScheme.oracleRecvA, scheme, recvA, bind_pure_comp, StateT.run_bind,
          StateT.run_get, pure_bind, hmsg, hrecv, StateT.run_map, StateT.run_set, map_pure,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hout
        obtain ⟨⟨heq, _⟩, _⟩ := hout
        have hmatch : trcv = ρ.sendingEpoch := heq.trans hepoch
        exact ⟨ρ, congrArg (fun t => some (ρ, t)) (hrecord.trans hmatch.symm), hmatch.symm⟩
      | some key =>
        rcases key with ⟨epochI, key⟩
        simp only [SCKAScheme.oracleRecvA, scheme, recvA, bind_pure_comp, StateT.run_bind,
          StateT.run_get, pure_bind, hmsg, hrecv, StateT.run_map, StateT.run_set, map_pure,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hout
        obtain ⟨⟨heq, _⟩, _⟩ := hout
        have hmatch : trcv = ρ.sendingEpoch := heq.trans hepoch
        exact ⟨ρ, congrArg (fun t => some (ρ, t)) (hrecord.trans hmatch.symm), hmatch.symm⟩

/-- A successful receive at B matches the epoch recorded with A's delivered message. -/
theorem oracleRecvB_matches_recorded_epoch
    [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak)
    (s s' : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : MessageEpochsConsistent s) (n trcv : ℕ) (tI : Option ℕ)
    (hout : (some (trcv, tI), s') ∈ support
      ((SCKAScheme.oracleRecvB (scheme kem hDet ecEk ecCt leak) n).run s)) :
    ∃ ρ : Message Sym, s.msgA n = some (ρ, trcv) ∧ ρ.sendingEpoch = trcv := by
  cases hmsg : s.msgA n with
  | none => simp [SCKAScheme.oracleRecvB, hmsg] at hout
  | some entry =>
    rcases entry with ⟨ρ, tsnd⟩
    cases hrecv : recv .B kem hDet ecEk ecCt s.stB ρ with
    | none => simp [SCKAScheme.oracleRecvB, hmsg, scheme, recvB, hrecv] at hout
    | some out =>
      rcases out with ⟨key?, epoch, st'⟩
      have hepoch := recv_reports_message_sendingEpoch .B kem hDet ecEk ecCt
        s.stB ρ (key?, epoch, st') hrecv
      have hrecord := hs.1 n ρ tsnd hmsg
      cases key? with
      | none =>
        simp only [SCKAScheme.oracleRecvB, scheme, recvB, bind_pure_comp, StateT.run_bind,
          StateT.run_get, pure_bind, hmsg, hrecv, StateT.run_map, StateT.run_set, map_pure,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hout
        obtain ⟨⟨heq, _⟩, _⟩ := hout
        have hmatch : trcv = ρ.sendingEpoch := heq.trans hepoch
        exact ⟨ρ, congrArg (fun t => some (ρ, t)) (hrecord.trans hmatch.symm), hmatch.symm⟩
      | some key =>
        rcases key with ⟨epochI, key⟩
        simp only [SCKAScheme.oracleRecvB, scheme, recvB, bind_pure_comp, StateT.run_bind,
          StateT.run_get, pure_bind, hmsg, hrecv, StateT.run_map, StateT.run_set, map_pure,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hout
        obtain ⟨⟨heq, _⟩, _⟩ := hout
        have hmatch : trcv = ρ.sendingEpoch := heq.trans hepoch
        exact ⟨ρ, congrArg (fun t => some (ρ, t)) (hrecord.trans hmatch.symm), hmatch.symm⟩

end oppBiKemCKA
