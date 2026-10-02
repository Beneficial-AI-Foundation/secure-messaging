/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Gavran, Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Correctness.SendProvenance

/-! # Public-key acknowledgement soundness for Opp-BiKEM correctness

Every public-key acknowledgement recorded by a party, and every public-key acknowledgement
flag on a recorded incoming message, is backed by a decoded peer public key installed in one
of the two parties' current `ekPeer` maps. Receive never overwrites an installed peer key and
adds `ekRec` entries only from the incoming flag or from a fresh install; send leaves both
maps unchanged and advertises only acknowledgements that are already recorded locally. The
invariant holds initially and is preserved by every correctness-game oracle.
-/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-- Public-key acknowledgement soundness for the party owning `st`, whose peer
is in state `peer` and whose incoming messages are `peerMsgs`. Every local
`ek-rec` entry, and every `ek-rec` flag on a recorded incoming message (at the
index the receiver would insert, `Construction.lean:368-370`), is backed by an
installed public key in one of the two parties' current `ekPeer` maps. -/
structure PublicKeyAckSoundness
    (role : Role) (st peer : State PK SK C Sym)
    (peerMsgs : ℕ → Option (Message Sym × ℕ)) : Prop where
  local_entry : ∀ t ∈ st.ack.ekRec,
    -- Own decode: `st` decoded the peer's epoch-`t` public key and installed it in its own
    -- `ekPeer`. This is the reading when `st` is the responder at `t` (the recipient).
    (st.res.ekPeer t).isSome = true ∨
    -- Peer's decode: the peer decoded `st`'s own epoch-`t` public key and installed it in the
    -- peer's `ekPeer`. This is the reading when `st` is the requester at `t` (the generator).
    -- This structure does not say which disjunct holds; `RoleParity.lean` separates them.
    (peer.res.ekPeer t).isSome = true
  peer_flag : ∀ (n : ℕ) (ρ : Message Sym) (tsnd : ℕ),
    peerMsgs n = some (ρ, tsnd) → ρ.ack.ekRec = true →
      -- The same two readings, at the index `i` that the receiver `st` inserts for the flag.
      -- Own decode: `st` installed a key at `i` (it would be the responder at `i`).
      (st.res.ekPeer (ρ.tReq + role.offset)).isSome = true ∨
        -- Peer's decode: the flag's sender, the peer, is the responder at `i`, and it
        -- decoded `st`'s own key (`st` is the requester at `i`, the generator).
        -- Role parity (`RoleParity.lean`) shows that only this disjunct occurs.
        (peer.res.ekPeer (ρ.tReq + role.offset)).isSome = true

/-- Public-key acknowledgement soundness for both parties of a correctness-game state: `A`
against `B`'s outgoing table and `B` against `A`'s outgoing table. -/
def GamePublicKeyAckSoundness
    (s : SCKAScheme.GameState
      (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) : Prop :=
  PublicKeyAckSoundness .A s.stA s.stB s.msgB ∧
    PublicKeyAckSoundness .B s.stB s.stA s.msgA

/-- A successful receive never changes an already installed peer public key. -/
theorem recv_peerKeys_stable [DecidableEq Sym]
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym)
    (key? : Option (ℕ × K)) (trcv : ℕ) (st' : State PK SK C Sym)
    (hout : recv role kem hDet ecEk ecCt st ρ = some (key?, trcv, st'))
    (t : ℤ) (ht : (st.res.ekPeer t).isSome = true) :
    st'.res.ekPeer t = st.res.ekPeer t := by
  -- The only `ekPeer` write is guarded by an empty slot, which `t` is not.
  have hne : ∀ q : ℤ, (st.res.ekPeer q).isNone = true → t ≠ q := by
    intro q hq htq
    subst htq
    rw [Option.isNone_iff_eq_none] at hq
    rw [hq] at ht
    cases ht
  have hproj := congrArg
    (Option.map fun out : Option (ℕ × K) × ℕ × State PK SK C Sym =>
      out.2.2.res.ekPeer t) hout
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
     exact (Option.some.inj hproj).symm)
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
      all_goals first
        | exact (Option.some.inj hproj).symm
        | exact (Option.some.inj hproj).symm.trans
            (Function.update_of_ne (hne _ hpk.1) _ _)
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
      all_goals exact (Option.some.inj hproj).symm

/-- Every `ekRec` entry after a successful receive was already recorded, is the index
acknowledged by the incoming flag, or carries an installed peer public key. -/
theorem recv_publicKeyAck_origin [DecidableEq Sym]
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym)
    (key? : Option (ℕ × K)) (trcv : ℕ) (st' : State PK SK C Sym)
    (hout : recv role kem hDet ecEk ecCt st ρ = some (key?, trcv, st'))
    (t : ℤ) (ht : t ∈ st'.ack.ekRec) :
    t ∈ st.ack.ekRec ∨
      (ρ.ack.ekRec = true ∧ t = ρ.tReq + role.offset) ∨
      (st'.res.ekPeer t).isSome = true := by
  have hproj := congrArg
    (Option.map fun out : Option (ℕ × K) × ℕ × State PK SK C Sym =>
      (out.2.2.ack.ekRec, out.2.2.res.ekPeer t)) hout
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
  -- Stale leaves keep `ekPeer`; `ekRec` gains at most the flagged index.
  all_goals try
    (simp only [Option.pure_def, Option.map_some] at hproj
     obtain ⟨hek, -⟩ := Prod.mk.inj (Option.some.inj hproj)
     rw [← hek] at ht
     first
       | exact Or.inl ht
       | (rw [Finset.mem_insert] at ht
          rcases ht with ht | ht
          · exact Or.inr (Or.inl ⟨hekRec, ht⟩)
          · exact Or.inl ht))
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
      -- Public-key leaves: the flag insert, the decoded-key install, or neither.
      all_goals
        obtain ⟨hek, hpe⟩ := Prod.mk.inj (Option.some.inj hproj)
        rw [← hek] at ht
        first
          | exact Or.inl ht
          | (rw [Finset.mem_insert] at ht
             rcases ht with ht | ht
             · first
                 | exact Or.inr (Or.inl ⟨hekRec, ht⟩)
                 | exact Or.inr (Or.inr (by
                     rw [← hpe, ht, Function.update_self, Option.isSome_some]))
             · exact Or.inl ht)
          | (rw [Finset.mem_insert, Finset.mem_insert] at ht
             rcases ht with ht | ht | ht
             · exact Or.inr (Or.inr (by
                 rw [← hpe, ht, Function.update_self, Option.isSome_some]))
             · exact Or.inr (Or.inl ⟨hekRec, ht⟩)
             · exact Or.inl ht)
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
      -- Ciphertext and no-payload leaves: `ekRec` gains at most the flagged index.
      all_goals
        obtain ⟨hek, -⟩ := Prod.mk.inj (Option.some.inj hproj)
        rw [← hek] at ht
        first
          | exact Or.inl ht
          | (rw [Finset.mem_insert] at ht
             rcases ht with ht | ht
             · exact Or.inr (Or.inl ⟨hekRec, ht⟩)
             · exact Or.inl ht)

/-- A supported send preserves soundness for the sender and, after recording the emitted
message in the sender's outgoing table, for the receiver. The new message's flag is backed
by the sender's own `ekRec` entry at the advertised index. -/
theorem publicKeyAckSoundness_send_step
  (roleS : Role)
    (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (stS stR : State PK SK C Sym)
    (msgsS msgsR : ℕ → Option (Message Sym × ℕ))
    (hS : PublicKeyAckSoundness roleS stS stR msgsR)
    (hR : PublicKeyAckSoundness roleS.peer stR stS msgsS)
    (n : ℕ) (key? : Option (ℕ × K)) (ρ : Message Sym) (tsnd : ℕ)
    (stS' : State PK SK C Sym)
    (hout : some (key?, ρ, tsnd, stS') ∈
      support (send roleS kem ecEk ecCt stS)) :
    PublicKeyAckSoundness roleS stS' stR msgsR ∧
      PublicKeyAckSoundness roleS.peer stR stS'
        (Function.update msgsS n (some (ρ, tsnd))) := by
  have hp := send_provenance roleS kem ecEk ecCt stS key? ρ tsnd stS' hout
  have hack : stS'.ack = stS.ack := hp.acknowledgements
  have hpeer : stS'.res.ekPeer = stS.res.ekPeer := hp.peer_keys
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro t ht
    rw [hack] at ht
    rw [hpeer]
    exact hS.local_entry t ht
  · intro j msg tj hj hflag
    rw [hpeer]
    exact hS.peer_flag j msg tj hj hflag
  · intro t ht
    rw [hpeer]
    exact hR.local_entry t ht
  · intro j msg tj hj hflag
    rw [hpeer]
    by_cases hjn : j = n
    · subst hjn
      rw [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hj
      obtain ⟨rfl, rfl⟩ := hj
      have hadv := hp.advertised_acknowledgements.1
      rw [hflag] at hadv
      have hmem : stS.req.reqEpoch - roleS.offset ∈ stS.ack.ekRec :=
        of_decide_eq_true hadv.symm
      have hreq := hp.message_reqEpoch
      have hidx : ρ.tReq + roleS.peer.offset = stS.req.reqEpoch - roleS.offset := by
        rw [Role.peer_offset]
        omega
      rw [hidx]
      exact (hS.local_entry _ hmem).symm
    · rw [Function.update_of_ne hjn] at hj
      exact hR.peer_flag j msg tj hj hflag

/-- A successful receive by the party `roleR` of a message recorded in the sender's table
preserves soundness for both parties: installed keys persist, and each new `ekRec` entry is
either backed by the recorded flag or by the key the receive installs. -/
theorem publicKeyAckSoundness_recv_step [DecidableEq Sym]
    (roleR roleS : Role) (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (stR stS : State PK SK C Sym)
    (msgsR msgsS : ℕ → Option (Message Sym × ℕ))
    (hR : PublicKeyAckSoundness roleR stR stS msgsS)
    (hS : PublicKeyAckSoundness roleS stS stR msgsR)
    (n : ℕ) (ρ : Message Sym) (tsnd : ℕ)
    (hmsg : msgsS n = some (ρ, tsnd))
    (key? : Option (ℕ × K)) (trcv : ℕ) (stR' : State PK SK C Sym)
    (hout : recv roleR kem hDet ecEk ecCt stR ρ = some (key?, trcv, stR')) :
    PublicKeyAckSoundness roleR stR' stS msgsS ∧
      PublicKeyAckSoundness roleS stS stR' msgsR := by
  have stable : ∀ t : ℤ, (stR.res.ekPeer t).isSome = true →
      (stR'.res.ekPeer t).isSome = true := by
    intro t ht
    rw [recv_peerKeys_stable roleR kem hDet ecEk ecCt stR ρ key? trcv stR' hout t ht]
    exact ht
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro t ht
    rcases recv_publicKeyAck_origin roleR kem hDet ecEk ecCt stR ρ key? trcv stR' hout
        t ht with hold | ⟨hflag, rfl⟩ | hown
    · exact (hR.local_entry t hold).imp_left (stable t)
    · exact (hR.peer_flag n ρ tsnd hmsg hflag).imp_left (stable _)
    · exact Or.inl hown
  · intro j msg tj hj hflag
    exact (hR.peer_flag j msg tj hj hflag).imp_left (stable _)
  · intro t ht
    exact (hS.local_entry t ht).imp_right (stable t)
  · intro j msg tj hj hflag
    exact (hS.peer_flag j msg tj hj hflag).imp_right (stable _)

/-- Honest initial states have no public-key acknowledgements and empty message tables. -/
theorem initGameState_publicKeyAckSoundness
    (stA : StA PK SK C Sym) (stB : StB PK SK C Sym)
    (hA : stA ∈ support (initA () : ProbComp (StA PK SK C Sym)))
    (hB : stB ∈ support (initB () : ProbComp (StB PK SK C Sym))) :
    GamePublicKeyAckSoundness (K := K) (SCKAScheme.initGameState stA stB) := by
  simp only [initA, init, support_pure, Set.mem_singleton_iff] at hA
  simp only [initB, init, support_pure, Set.mem_singleton_iff] at hB
  subst stA
  subst stB
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro t ht
    exact absurd ht (Finset.notMem_empty t)
  · intro j msg tj hj
    simp [SCKAScheme.initGameState] at hj
  · intro t ht
    exact absurd ht (Finset.notMem_empty t)
  · intro j msg tj hj
    simp [SCKAScheme.initGameState] at hj

/-- Every correctness-game oracle preserves `GamePublicKeyAckSoundness`. -/
theorem sckaCorrectnessImpl_preserves_publicKeyAckSoundness
    [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak) :
    QueryImpl.PreservesInv
      (SCKAScheme.sckaCorrectnessImpl (scheme kem hDet ecEk ecCt leak))
      (GamePublicKeyAckSoundness
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
        obtain ⟨hA', hB'⟩ := publicKeyAckSoundness_send_step .A kem ecEk ecCt
          s.stA s.stB s.msgA s.msgB hs.1 hs.2 (s.nA + 1) key? ρ tsnd s'.stA hsend
        refine ⟨?_, ?_⟩
        · rw [hstB, hmsgB]
          exact hA'
        · rw [hstB, hmsgA]
          exact hB'
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
        obtain ⟨hB', hA'⟩ := publicKeyAckSoundness_send_step .B kem ecEk ecCt
          s.stB s.stA s.msgB s.msgA hs.2 hs.1 (s.nB + 1) key? ρ tsnd s'.stB hsend
        refine ⟨?_, ?_⟩
        · rw [hstA, hmsgB]
          exact hA'
        · rw [hstA, hmsgA]
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
            obtain ⟨hA', hB'⟩ := publicKeyAckSoundness_recv_step .A .B kem hDet ecEk ecCt
              s.stA s.stB s.msgA s.msgB hs.1 hs.2 n ρ tsnd hmsg key? trcv st' hrecv
            cases key? <;>
              simp only [SCKAScheme.oracleRecvA, bind_pure_comp, StateT.run_bind,
                StateT.run_get, pure_bind, hmsg, hrecv, StateT.run_map, StateT.run_set,
                map_pure, support_pure] at hz <;>
              subst z <;>
              exact ⟨hA', hB'⟩
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
            obtain ⟨hB', hA'⟩ := publicKeyAckSoundness_recv_step .B .A kem hDet ecEk ecCt
              s.stB s.stA s.msgB s.msgA hs.2 hs.1 n ρ tsnd hmsg key? trcv st' hrecv
            cases key? <;>
              simp only [SCKAScheme.oracleRecvB, bind_pure_comp, StateT.run_bind,
                StateT.run_get, pure_bind, hmsg, hrecv, StateT.run_map, StateT.run_set,
                map_pure, support_pure] at hz <;>
              subst z <;>
              exact ⟨hA', hB'⟩

/-- Public-key acknowledgement soundness holds in every reachable correctness-game state
from honest initialization. -/
theorem simulateQ_publicKeyAckSoundness
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
    GamePublicKeyAckSoundness z.2 := by
  exact simulateQ_run_preservesInv _ GamePublicKeyAckSoundness
    (sckaCorrectnessImpl_preserves_publicKeyAckSoundness kem hDet ecEk ecCt leak)
    adv _ (initGameState_publicKeyAckSoundness stA stB hA hB) z hz

end oppBiKemCKA
