/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Gavran, Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Correctness.PublicKeyAckSoundness
import SecureMessaging.SCKA.OppBiKEM.Correctness.ReceiveState

/-! # Role parity for Opp-BiKEM correctness

Each party's epoch counters keep a fixed parity determined by its role: `A` responds at odd
epochs and requests at even ones, and `B` the reverse. Installed peer public keys sit at the
owner's responder parity, and every recorded outgoing message carries the sender's responder
and requester parities. These facts hold initially and are preserved by every
correctness-game oracle.

Combined with public-key acknowledgement soundness, role parity separates the two readings
of a local `ek-rec` entry: at the owner's responder parity it is backed by the owner's own
`ekPeer`, and at the owner's requester parity by the peer's `ekPeer`.
-/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-- Role parity of one party `role` with its own outgoing message table `ownMsgs`.
`A` responds at odd epochs and requests at even ones; `B` the reverse (`init`,
`Construction.lean:176-182`; each counter moves only by `2`). Installed peer public
keys sit at the owner's responder parity, which is the parity of the peer's key epochs,
and every recorded outgoing message carries the sender's responder and requester parities. -/
structure RoleParity
    (role : Role) (st : State PK SK C Sym)
    (ownMsgs : ℕ → Option (Message Sym × ℕ)) : Prop where
  resEpoch_parity : st.res.resEpoch % 2 = if role = .A then 1 else 0
  reqEpoch_parity : st.req.reqEpoch % 2 = if role = .A then 0 else 1
  peerKey_parity : ∀ t : ℤ, (st.res.ekPeer t).isSome = true →
    t % 2 = if role = .A then 1 else 0
  message_parity : ∀ (n : ℕ) (ρ : Message Sym) (tsnd : ℕ),
    ownMsgs n = some (ρ, tsnd) →
      ρ.tRes % 2 = (if role = .A then 1 else 0) ∧
        ρ.tReq % 2 = (if role = .A then 0 else 1)

/-- Role parity for both parties of a correctness-game state, each against its own
outgoing message table. -/
def GameRoleParity
    (s : SCKAScheme.GameState
      (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) : Prop :=
  RoleParity .A s.stA s.msgA ∧ RoleParity .B s.stB s.msgB

/-- A successful receive changes the peer public key at index `t` only when `t` is the
receiver's new requester epoch shifted by its role offset, the only index `recv` writes. -/
theorem recv_peerKeys_origin [DecidableEq Sym]
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym)
    (key? : Option (ℕ × K)) (trcv : ℕ) (st' : State PK SK C Sym)
    (hout : recv role kem hDet ecEk ecCt st ρ = some (key?, trcv, st'))
    (t : ℤ) :
    st'.res.ekPeer t = st.res.ekPeer t ∨ t = st'.req.reqEpoch - role.offset := by
  have hproj := congrArg
    (Option.map fun out : Option (ℕ × K) × ℕ × State PK SK C Sym =>
      (out.2.2.req.reqEpoch, out.2.2.res.ekPeer t)) hout
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
  -- Stale leaves keep both the requester epoch and `ekPeer`.
  all_goals try
    (simp only [Option.pure_def, Option.map_some] at hproj
     exact Or.inl (Prod.mk.inj (Option.some.inj hproj)).2.symm)
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
      all_goals repeat' split at hproj
      all_goals try simp only [Option.pure_def, Option.map_some] at hproj
      -- Public-key leaves: either `ekPeer` is unchanged, or the decoded key is installed
      -- at the new requester epoch shifted by the role offset.
      all_goals
        obtain ⟨hreq, hpe⟩ := Prod.mk.inj (Option.some.inj hproj)
        first
          | exact Or.inl hpe.symm
          | (rw [← hpe, ← hreq, Function.update_apply]
             split_ifs with htq
             · exact Or.inr htq
             · exact Or.inl rfl)
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
      -- Ciphertext and no-payload leaves never write `ekPeer`.
      all_goals
        obtain ⟨-, hpe⟩ := Prod.mk.inj (Option.some.inj hproj)
        exact Or.inl hpe.symm

/-- A supported send preserves the sender's role parity once the emitted message is recorded
in the sender's outgoing table: the responder epoch moves by `0` or `2`, the requester epoch
and `ekPeer` are unchanged, and the new message carries the post-send responder epoch and the
unchanged requester epoch. -/
theorem roleParity_send_step
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (msgs : ℕ → Option (Message Sym × ℕ))
    (hs : RoleParity role st msgs)
    (n : ℕ) (key? : Option (ℕ × K)) (ρ : Message Sym) (tsnd : ℕ)
    (st' : State PK SK C Sym)
    (hout : some (key?, ρ, tsnd, st') ∈
      support (send role kem ecEk ecCt st)) :
    RoleParity role st' (Function.update msgs n (some (ρ, tsnd))) := by
  have hp := send_provenance role kem ecEk ecCt st key? ρ tsnd st' hout
  have hres : st'.res.resEpoch % 2 = if role = .A then 1 else 0 := by
    have h0 := hs.resEpoch_parity
    rcases hp.keygen_transition with ⟨h, -, -⟩ | ⟨pk, sk, -, h, -, -⟩
    · rw [h]
      exact h0
    · rw [h]
      omega
  refine ⟨hres, ?_, ?_, ?_⟩
  · rw [hp.requester_epoch]
    exact hs.reqEpoch_parity
  · intro t ht
    rw [hp.peer_keys] at ht
    exact hs.peerKey_parity t ht
  · intro j msg tj hj
    by_cases hjn : j = n
    · subst hjn
      rw [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hj
      obtain ⟨rfl, rfl⟩ := hj
      refine ⟨?_, ?_⟩
      · rw [hp.message_resEpoch]
        exact hres
      · rw [hp.message_reqEpoch]
        exact hs.reqEpoch_parity
    · rw [Function.update_of_ne hjn] at hj
      exact hs.message_parity j msg tj hj

/-- A successful receive preserves the receiver's role parity: the responder epoch is
unchanged, the requester epoch moves by `0` or `2`, and the only new peer public key sits at
the new requester epoch shifted by the role offset, which is the responder parity. -/
theorem roleParity_recv_step [DecidableEq Sym]
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (msgs : ℕ → Option (Message Sym × ℕ))
    (hs : RoleParity role st msgs)
    (ρ : Message Sym) (key? : Option (ℕ × K)) (trcv : ℕ)
    (st' : State PK SK C Sym)
    (hout : recv role kem hDet ecEk ecCt st ρ = some (key?, trcv, st')) :
    RoleParity role st' msgs := by
  have hfacts := recv_success_state_facts role kem hDet ecEk ecCt st ρ key? trcv st' hout
  have hreq : st'.req.reqEpoch % 2 = if role = .A then 0 else 1 := by
    have h0 := hs.reqEpoch_parity
    rw [hfacts.2.2.2.1]
    by_cases hlt : st.req.reqEpoch < ρ.tRes
    · rw [if_pos hlt]
      omega
    · rw [if_neg hlt]
      exact h0
  refine ⟨?_, hreq, ?_, hs.message_parity⟩
  · rw [hfacts.2.1]
    exact hs.resEpoch_parity
  · intro t ht
    rcases recv_peerKeys_origin role kem hDet ecEk ecCt st ρ key? trcv st' hout t with
      heq | heq
    · rw [heq] at ht
      exact hs.peerKey_parity t ht
    · subst heq
      cases role <;>
        simp only [Role.offset, reduceCtorEq, if_true, if_false]
          at hreq ⊢ <;>
        omega

/-- Honest initial states satisfy role parity: `A` starts at responder epoch `-1` and
requester epoch `0`, `B` at `0` and `-1`, with no peer public keys and empty message
tables. -/
theorem initGameState_roleParity
    (stA : StA PK SK C Sym) (stB : StB PK SK C Sym)
    (hA : stA ∈ support (initA () : ProbComp (StA PK SK C Sym)))
    (hB : stB ∈ support (initB () : ProbComp (StB PK SK C Sym))) :
    GameRoleParity (K := K) (SCKAScheme.initGameState stA stB) := by
  simp only [initA, init, support_pure, Set.mem_singleton_iff] at hA
  simp only [initB, init, support_pure, Set.mem_singleton_iff] at hB
  subst stA
  subst stB
  constructor <;> constructor <;> simp [SCKAScheme.initGameState]

/-- Every correctness-game oracle preserves `GameRoleParity`. -/
theorem sckaCorrectnessImpl_preserves_roleParity
    [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak) :
    QueryImpl.PreservesInv
      (SCKAScheme.sckaCorrectnessImpl (scheme kem hDet ecEk ecCt leak))
      (GameRoleParity
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
          exact roleParity_send_step .A kem ecEk ecCt s.stA s.msgA hs.1 (s.nA + 1)
            key? ρ tsnd s'.stA hsend
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
          exact roleParity_send_step .B kem ecEk ecCt s.stB s.msgB hs.2 (s.nB + 1)
            key? ρ tsnd s'.stB hsend
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
            have hA' := roleParity_recv_step .A kem hDet ecEk ecCt
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
            have hB' := roleParity_recv_step .B kem hDet ecEk ecCt
              s.stB s.msgB hs.2 ρ key? trcv st' hrecv
            cases key? <;>
              simp only [SCKAScheme.oracleRecvB, bind_pure_comp, StateT.run_bind,
                StateT.run_get, pure_bind, hmsg, hrecv, StateT.run_map, StateT.run_set,
                map_pure, support_pure] at hz <;>
              subst z <;>
              exact ⟨hs.1, hB'⟩

/-- Role parity holds in every reachable correctness-game state from honest
initialization. -/
theorem simulateQ_roleParity
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
    GameRoleParity z.2 := by
  exact simulateQ_run_preservesInv _ GameRoleParity
    (sckaCorrectnessImpl_preserves_roleParity kem hDet ecEk ecCt leak)
    adv _ (initGameState_roleParity stA stB hA hB) z hz

/-- Parity-separated public-key acknowledgement soundness for the party `role` owning
`st`, whose peer is in state `peer` and whose incoming messages are `peerMsgs`: the
paper's role-dependent reading of `ACK[t].ek-rec` (SCKA §4.2). An entry at the owner's
responder parity is backed by a decoded public key installed in the owner's own `ekPeer`;
an entry at the owner's requester parity (its own key epochs) is backed by a decoded
public key installed in the peer's `ekPeer`; and a true `ek-rec` flag on a recorded
peer message is backed by the peer's `ekPeer` at the receiver's insertion index. This
says nothing about which public key was installed. -/
structure PublicKeyAckOwnership
    (role : Role) (st peer : State PK SK C Sym)
    (peerMsgs : ℕ → Option (Message Sym × ℕ)) : Prop where
  received_peer_key : ∀ t ∈ st.ack.ekRec,
    t % 2 = (if role = .A then 1 else 0) → (st.res.ekPeer t).isSome = true
  delivered_own_key : ∀ t ∈ st.ack.ekRec,
    t % 2 = (if role = .A then 0 else 1) → (peer.res.ekPeer t).isSome = true
  peer_flag : ∀ (n : ℕ) (ρ : Message Sym) (tsnd : ℕ),
    peerMsgs n = some (ρ, tsnd) → ρ.ack.ekRec = true →
      (peer.res.ekPeer (ρ.tReq + role.offset)).isSome = true

/-- Origin-form public-key acknowledgement soundness, together with role parity for both
parties of opposite roles, separates each disjunction by parity: peer keys installed by a
party sit only at its responder parity, so each entry is backed by exactly the map the
parity selects. -/
theorem publicKeyAckOwnership_of_roleParity
    (role : Role)
    (st peer : State PK SK C Sym)
    (ownMsgs peerMsgs : ℕ → Option (Message Sym × ℕ))
    (hack : PublicKeyAckSoundness role st peer peerMsgs)
    (hst : RoleParity role st ownMsgs)
    (hpeer : RoleParity role.peer peer peerMsgs) :
    PublicKeyAckOwnership role st peer peerMsgs := by
  have hstKey := hst.peerKey_parity
  have hpeerKey := hpeer.peerKey_parity
  have hpeerMsg := hpeer.message_parity
  cases role
  · simp only [Role.peer, reduceCtorEq, if_true, if_false] at hstKey hpeerKey hpeerMsg
    refine ⟨?_, ?_, ?_⟩
    · intro t ht hpar
      simp only [if_true] at hpar
      rcases hack.local_entry t ht with h | h
      · exact h
      · have := hpeerKey t h
        omega
    · intro t ht hpar
      simp only [if_true] at hpar
      rcases hack.local_entry t ht with h | h
      · have := hstKey t h
        omega
      · exact h
    · intro j msg tj hj hflag
      rcases hack.peer_flag j msg tj hj hflag with h | h
      · have h1 := hstKey _ h
        have h2 := (hpeerMsg j msg tj hj).2
        simp only [Role.offset] at h1
        omega
      · exact h
  · simp only [Role.peer, reduceCtorEq, if_true, if_false] at hstKey hpeerKey hpeerMsg
    refine ⟨?_, ?_, ?_⟩
    · intro t ht hpar
      simp only [reduceCtorEq, if_false] at hpar
      rcases hack.local_entry t ht with h | h
      · exact h
      · have := hpeerKey t h
        omega
    · intro t ht hpar
      simp only [reduceCtorEq, if_false] at hpar
      rcases hack.local_entry t ht with h | h
      · have := hstKey t h
        omega
      · exact h
    · intro j msg tj hj hflag
      rcases hack.peer_flag j msg tj hj hflag with h | h
      · have h1 := hstKey _ h
        have h2 := (hpeerMsg j msg tj hj).2
        simp only [Role.offset] at h1
        omega
      · exact h

/-- Parity-separated public-key acknowledgement soundness holds for both parties in every
reachable correctness-game state from honest initialization. -/
theorem simulateQ_publicKeyAckOwnership
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
    PublicKeyAckOwnership .A z.2.stA z.2.stB z.2.msgB ∧
      PublicKeyAckOwnership .B z.2.stB z.2.stA z.2.msgA := by
  have h1 := simulateQ_publicKeyAckSoundness kem hDet ecEk ecCt leak adv stA stB hA hB z hz
  have h2 := simulateQ_roleParity kem hDet ecEk ecCt leak adv stA stB hA hB z hz
  exact ⟨publicKeyAckOwnership_of_roleParity .A _ _ _ _ h1.1 h2.1 h2.2,
    publicKeyAckOwnership_of_roleParity .B _ _ _ _ h1.2 h2.2 h2.1⟩

end oppBiKemCKA
