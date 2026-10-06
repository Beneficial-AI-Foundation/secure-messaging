/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Gavran, Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Correctness.RoleParity

/-! # Phase causality for Opp-BiKEM correctness, first half

A party sends a ciphertext chunk (`bit = some 1`) only after its own public key for the current
responder epoch has been acknowledged: the ciphertext branch of `sendWith` is the `else` of the
public-key guard `tRes + role.offset ∉ ack.ekRec` (`Construction.lean:258`, `:265`, `:279`).
Since `ekRec` only grows, every recorded ciphertext message keeps that acknowledgement in the
sender's current `ekRec`. Through the parity-separated public-key acknowledgement soundness of
`RoleParity.lean`, the receiver has therefore installed the sender's public key in the slot
`recv` consults for that epoch (`Construction.lean:393-395`). The invariant holds initially and
is preserved by every correctness-game oracle. Nothing is claimed about which key is installed,
about the receiver's chunk buffer, or about the receiver's requester epoch.
-/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-- Every recorded ciphertext message of the party `role` owning `st` carries a responder epoch
whose own-key index `ρ.tRes + role.offset` is acknowledged in the owner's `ekRec`. The
ciphertext branch of `sendWith` is the `else` of the public-key guard
`tRes + role.offset ∉ ack.ekRec` (`Construction.lean:258`, `:265`, `:279`), the message carries
the post-advance `tRes` (`:284-285`), and `ekRec` only grows. -/
def CiphertextMessageKeyAck
    (role : Role) (st : State PK SK C Sym)
    (ownMsgs : ℕ → Option (Message Sym × ℕ)) : Prop :=
  ∀ (n : ℕ) (ρ : Message Sym) (tsnd : ℕ),
    ownMsgs n = some (ρ, tsnd) → ρ.bit = some 1 → ρ.tRes + role.offset ∈ st.ack.ekRec

/-- The ciphertext-message acknowledgement property for both parties of a correctness-game
state, each against its own outgoing message table. -/
def GameCiphertextMessageKeyAck
    (s : SCKAScheme.GameState
      (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) : Prop :=
  CiphertextMessageKeyAck .A s.stA s.msgA ∧ CiphertextMessageKeyAck .B s.stB s.msgB

/-- A supported send that emits a ciphertext message (`ρ.bit = some 1`) did so in the `else`
branch of the public-key guard, so the sender's own-key index `ρ.tRes + role.offset` is in the
acknowledgements the send read (`Construction.lean:239`, `:258`, `:265`, `:279`, `:284-285`). -/
theorem send_ciphertextMessage_keyAck
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (key? : Option (ℕ × K))
    (ρ : Message Sym) (tsnd : ℕ) (st' : State PK SK C Sym)
    (hout : some (key?, ρ, tsnd, st') ∈
      support (send role kem ecEk ecCt st))
    (hbit : ρ.bit = some 1) :
    ρ.tRes + role.offset ∈ st.ack.ekRec := by
  rw [send, mem_support_bind_iff] at hout
  obtain ⟨out, hmem, hout⟩ := hout
  cases out with
  | none => simp at hout
  | some out =>
    rcases out with ⟨key, msg, epoch, state, rand⟩
    simp only [support_pure, Set.mem_singleton_iff, Option.map_some,
      Option.some.injEq, Prod.mk.injEq] at hout
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hout
    unfold sendWith at hmem
    dsimp only at hmem
    repeat' first
      | split at hmem
      | (rw [mem_support_bind_iff] at hmem; obtain ⟨x, _, hmem⟩ := hmem)
    all_goals simp only [support_pure, Set.mem_singleton_iff,
      Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hmem
    all_goals obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hmem
    -- Public-key leaves contradict `hbit` by the `Fin 2` literal; every other leaf (ciphertext
    -- or no payload) lies in the `else` of the `:258` guard and carries its negation.
    all_goals first
      | exact absurd (Option.some.inj hbit) (by decide)
      | exact Decidable.of_not_not ‹_›

/-- A supported send preserves the property once the emitted message is recorded in the
sender's outgoing table: the acknowledgements are unchanged and the new message, if it is a
ciphertext message, satisfied the guard. -/
theorem ciphertextMessageKeyAck_send_step
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (msgs : ℕ → Option (Message Sym × ℕ))
    (hs : CiphertextMessageKeyAck role st msgs)
    (n : ℕ) (key? : Option (ℕ × K)) (ρ : Message Sym) (tsnd : ℕ)
    (st' : State PK SK C Sym)
    (hout : some (key?, ρ, tsnd, st') ∈
      support (send role kem ecEk ecCt st)) :
    CiphertextMessageKeyAck role st' (Function.update msgs n (some (ρ, tsnd))) := by
  have hp := send_provenance role kem ecEk ecCt st key? ρ tsnd st' hout
  intro j msg tj hj hbit
  rw [hp.acknowledgements]
  by_cases hjn : j = n
  · subst hjn
    rw [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hj
    obtain ⟨rfl, rfl⟩ := hj
    exact send_ciphertextMessage_keyAck role kem ecEk ecCt st key? _ _ st' hout hbit
  · rw [Function.update_of_ne hjn] at hj
    exact hs j msg tj hj hbit

/-- A successful receive preserves the property: `ekRec` only grows and the receiver's outgoing
table is unchanged. -/
theorem ciphertextMessageKeyAck_recv_step [DecidableEq Sym]
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (msgs : ℕ → Option (Message Sym × ℕ))
    (hs : CiphertextMessageKeyAck role st msgs)
    (ρ : Message Sym) (key? : Option (ℕ × K)) (trcv : ℕ)
    (st' : State PK SK C Sym)
    (hout : recv role kem hDet ecEk ecCt st ρ = some (key?, trcv, st')) :
    CiphertextMessageKeyAck role st' msgs := by
  have hgrow : st.ack.ekRec ⊆ st'.ack.ekRec :=
    (recv_success_state_facts role kem hDet ecEk ecCt st ρ key? trcv st' hout).2.2.2.2.2.1
  intro j msg tj hj hbit
  exact hgrow (hs j msg tj hj hbit)

/-- The initial game state has empty message tables (`Defs.lean:207`), so the property holds
for any initial local states. -/
theorem initGameState_ciphertextMessageKeyAck
    (stA : StA PK SK C Sym) (stB : StB PK SK C Sym) :
    GameCiphertextMessageKeyAck (K := K) (SCKAScheme.initGameState stA stB) := by
  refine ⟨?_, ?_⟩
  · intro j msg tj hj
    simp [SCKAScheme.initGameState] at hj
  · intro j msg tj hj
    simp [SCKAScheme.initGameState] at hj

/-- Every correctness-game oracle preserves `GameCiphertextMessageKeyAck`. -/
theorem sckaCorrectnessImpl_preserves_ciphertextMessageKeyAck
    [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak) :
    QueryImpl.PreservesInv
      (SCKAScheme.sckaCorrectnessImpl (scheme kem hDet ecEk ecCt leak))
      (GameCiphertextMessageKeyAck
        (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym)) := by
  intro t s hs z hz
  rcases t with (((n | ⟨⟩) | ⟨⟩) | n) | n
  · exact oracleUnif_preservesInv _ n s hs z hz
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
        refine ⟨?_, ?_⟩
        · rw [hmsgA]
          exact ciphertextMessageKeyAck_send_step .A kem ecEk ecCt s.stA s.msgA hs.1
            (s.nA + 1) key? ρ tsnd s'.stA hsend
        · rw [hstB, hmsgB]
          exact hs.2
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
        refine ⟨?_, ?_⟩
        · rw [hstA, hmsgA]
          exact hs.1
        · rw [hmsgB]
          exact ciphertextMessageKeyAck_send_step .B kem ecEk ecCt s.stB s.msgB hs.2
            (s.nB + 1) key? ρ tsnd s'.stB hsend
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
            have hA' := ciphertextMessageKeyAck_recv_step .A kem hDet ecEk ecCt
              s.stA s.msgA hs.1 ρ key? trcv st' hrecv
            cases key? <;>
              simp only [SCKAScheme.oracleRecvA, bind_pure_comp, StateT.run_bind,
                StateT.run_get, pure_bind, hmsg, hrecv, StateT.run_map, StateT.run_set,
                map_pure, support_pure] at hz <;>
              subst z <;>
              exact ⟨hA', hs.2⟩
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
            have hB' := ciphertextMessageKeyAck_recv_step .B kem hDet ecEk ecCt
              s.stB s.msgB hs.2 ρ key? trcv st' hrecv
            cases key? <;>
              simp only [SCKAScheme.oracleRecvB, bind_pure_comp, StateT.run_bind,
                StateT.run_get, pure_bind, hmsg, hrecv, StateT.run_map, StateT.run_set,
                map_pure, support_pure] at hz <;>
              subst z <;>
              exact ⟨hs.1, hB'⟩

/-- The ciphertext-message acknowledgement property holds in every reachable correctness-game
state, for any initial local states. -/
theorem simulateQ_ciphertextMessageKeyAck
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
      (SCKAScheme.sckaCorrectnessImpl (scheme kem hDet ecEk ecCt leak)) adv).run
      (SCKAScheme.initGameState stA stB))) :
    GameCiphertextMessageKeyAck z.2 := by
  exact simulateQ_run_preservesInv _ GameCiphertextMessageKeyAck
    (sckaCorrectnessImpl_preserves_ciphertextMessageKeyAck kem hDet ecEk ecCt leak)
    adv _ (initGameState_ciphertextMessageKeyAck stA stB) z hz

/-- Phase causality, first half, at the receiver `role` owning `st` with incoming messages
`peerMsgs`: for every recorded ciphertext message of the peer, the peer's public key for that
responder epoch is installed in `st.res.ekPeer` at `ρ.tRes - role.offset`, the slot `recv`
consults when its requester epoch equals `ρ.tRes` (`Construction.lean:393-395`). This says
nothing about which key is installed, about the receiver's chunk buffer, or about the
receiver's requester epoch. -/
def CiphertextPhaseCausality
    (role : Role) (st : State PK SK C Sym)
    (peerMsgs : ℕ → Option (Message Sym × ℕ)) : Prop :=
  ∀ (n : ℕ) (ρ : Message Sym) (tsnd : ℕ),
    peerMsgs n = some (ρ, tsnd) → ρ.bit = some 1 →
      (st.res.ekPeer (ρ.tRes - role.offset)).isSome = true

/-- The peer's ciphertext-message acknowledgement property, the peer's role parity, and the
parity-separated reading of the peer's `ekRec` at its requester parity
(`PublicKeyAckOwnership.delivered_own_key`, `RoleParity.lean:386-387`) give phase causality at
the receiver: the acknowledged index `ρ.tRes + role.peer.offset` has the peer's requester
parity and equals `ρ.tRes - role.offset` (`Construction.lean:77`). -/
theorem ciphertextPhaseCausality_of_keyAck
    (role : Role) (st peer : State PK SK C Sym)
    (peerMsgs : ℕ → Option (Message Sym × ℕ))
    (hack : CiphertextMessageKeyAck role.peer peer peerMsgs)
    (hpar : RoleParity role.peer peer peerMsgs)
    (hdeliv : ∀ t ∈ peer.ack.ekRec,
      t % 2 = (if role.peer = .A then 0 else 1) → (st.res.ekPeer t).isSome = true) :
    CiphertextPhaseCausality role st peerMsgs := by
  intro n ρ tsnd hmsg hbit
  have hk : ρ.tRes + role.peer.offset ∈ peer.ack.ekRec := hack n ρ tsnd hmsg hbit
  have hp := (hpar.message_parity n ρ tsnd hmsg).1
  have hslot : ρ.tRes - role.offset = ρ.tRes + role.peer.offset := by
    rw [Role.peer_offset]
    omega
  have hkpar : (ρ.tRes + role.peer.offset) % 2 = if role.peer = .A then 0 else 1 := by
    cases role <;>
      simp only [Role.peer, Role.offset, reduceCtorEq, if_true, if_false] at hp ⊢ <;>
      omega
  rw [hslot]
  exact hdeliv _ hk hkpar

/-- Phase causality, first half, holds for both parties in every reachable correctness-game
state from honest initialization. -/
theorem simulateQ_ciphertextPhaseCausality
    [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (stA : StA PK SK C Sym) (stB : StB PK SK C Sym)
    (hA : stA ∈ support (initA () : ProbComp (StA PK SK C Sym)))
    (hB : stB ∈ support (initB () : ProbComp (StB PK SK C Sym)))
    (z : Bool × SCKAScheme.GameState
      (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hz : z ∈ support ((simulateQ
      (SCKAScheme.sckaCorrectnessImpl (scheme kem hDet ecEk ecCt leak)) adv).run
      (SCKAScheme.initGameState stA stB))) :
    CiphertextPhaseCausality .A z.2.stA z.2.msgB ∧
      CiphertextPhaseCausality .B z.2.stB z.2.msgA := by
  have h1 := simulateQ_ciphertextMessageKeyAck kem hDet ecEk ecCt leak adv stA stB z hz
  have h2 := simulateQ_roleParity kem hDet ecEk ecCt leak adv stA stB hA hB z hz
  have h3 := simulateQ_publicKeyAckOwnership kem hDet ecEk ecCt leak adv stA stB hA hB z hz
  exact ⟨ciphertextPhaseCausality_of_keyAck .A _ _ _ h1.2 h2.2 h3.2.delivered_own_key,
    ciphertextPhaseCausality_of_keyAck .B _ _ _ h1.1 h2.1 h3.1.delivered_own_key⟩

end oppBiKemCKA
