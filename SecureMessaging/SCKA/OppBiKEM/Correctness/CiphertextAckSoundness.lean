/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Gavran, Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Correctness.RoleParity

/-! # Ciphertext acknowledgement soundness for Opp-BiKEM correctness

Every positive `ct-rec` entry that a party records at its own requester parity is backed by its
own game key table, and every populated slot of that table at such an epoch is recorded in
`ct-rec`. An entry at the owner's responder parity is also in the peer's `ct-rec`. A true
`ct-rec` flag on a recorded outgoing message is backed by the sender's own entry. Receive adds
`ct-rec` entries only from the incoming flag or from its own decapsulation, which is the only
key-table write at the receiver's requester parity. Send leaves `ct-rec` unchanged and writes
its key table only at its responder parity. Role parity separates the two readings. The
invariant holds initially and, together with role parity, is preserved by every
correctness-game oracle.
-/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-- Ciphertext acknowledgement soundness for the party `role` owning `st`, with peer state
`peer`, own outgoing message table `ownMsgs`, and own game key table `ownKey`. Witness is the
game key table (`sources/RULING_ct_ack_witness.md`). At the owner's requester parity and a
positive epoch, a local `ct-rec` entry holds exactly when the owner's key table is populated
there: the owner decapsulated (`Construction.lean:403-414`, `Defs.lean:529`/`:583`). The `0 < t`
guard excludes the bootstrap entries `-1`, `0` and the `Int.toNat` collapse. An entry at the
owner's responder parity is also in the peer's `ct-rec`, and a true `ct-rec` flag on a
recorded outgoing message is backed by the sender's own entry at `ρ.tReq`. -/
structure CiphertextAckSoundness
    (role : Role) (st peer : State PK SK C Sym)
    (ownMsgs : ℕ → Option (Message Sym × ℕ))
    (ownKey : ℕ → Option K) : Prop where
  own_entry : ∀ t ∈ st.ack.ctRec, 0 < t →
    t % 2 = (if role = .A then 0 else 1) → ownKey t.toNat ≠ none
  own_key : ∀ t : ℤ, 0 < t → t % 2 = (if role = .A then 0 else 1) →
    ownKey t.toNat ≠ none → t ∈ st.ack.ctRec
  peer_entry : ∀ t ∈ st.ack.ctRec,
    t % 2 = (if role = .A then 1 else 0) → t ∈ peer.ack.ctRec
  own_flag : ∀ (n : ℕ) (ρ : Message Sym) (tsnd : ℕ),
    ownMsgs n = some (ρ, tsnd) → ρ.ack.ctRec = true → ρ.tReq ∈ st.ack.ctRec

/-- Ciphertext acknowledgement soundness for both parties of a correctness-game state, each
with its own outgoing table and its own key table. -/
def GameCiphertextAckSoundness
    (s : SCKAScheme.GameState
      (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) : Prop :=
  CiphertextAckSoundness .A s.stA s.stB s.msgA s.keyA ∧
    CiphertextAckSoundness .B s.stB s.stA s.msgB s.keyB

/-- Every `ctRec` entry after a successful receive was already recorded, is the index
acknowledged by the incoming flag, or is the receiver's post-receive requester epoch with a
key emitted (own decapsulation). -/
theorem recv_ciphertextAck_origin [DecidableEq Sym]
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym)
    (key? : Option (ℕ × K)) (trcv : ℕ) (st' : State PK SK C Sym)
    (hout : recv role kem hDet ecEk ecCt st ρ = some (key?, trcv, st'))
    (t : ℤ) (ht : t ∈ st'.ack.ctRec) :
    t ∈ st.ack.ctRec ∨
      (ρ.ack.ctRec = true ∧ t = ρ.tReq) ∨
      (key?.isSome = true ∧ t = st'.req.reqEpoch) := by
  have hproj := congrArg
    (Option.map fun out : Option (ℕ × K) × ℕ × State PK SK C Sym =>
      (out.1.isSome, out.2.2.ack.ctRec, out.2.2.req.reqEpoch)) hout
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
  -- Stale leaves: `ctRec` gains at most the flagged index.
  all_goals try
    (simp only [Option.pure_def, Option.map_some] at hproj
     obtain ⟨-, hrest⟩ := Prod.mk.inj (Option.some.inj hproj)
     obtain ⟨hct, -⟩ := Prod.mk.inj hrest
     rw [← hct] at ht
     first
       | exact Or.inl ht
       | (rw [Finset.mem_insert] at ht
          rcases ht with ht | ht
          · exact Or.inr (Or.inl ⟨hctRec, ht⟩)
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
      -- Public-key leaves: `ctRec` gains at most the flagged index.
      all_goals
        obtain ⟨-, hrest⟩ := Prod.mk.inj (Option.some.inj hproj)
        obtain ⟨hct, -⟩ := Prod.mk.inj hrest
        rw [← hct] at ht
        first
          | exact Or.inl ht
          | (rw [Finset.mem_insert] at ht
             rcases ht with ht | ht
             · exact Or.inr (Or.inl ⟨hctRec, ht⟩)
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
      -- Ciphertext and no-payload leaves: the flagged index, or the requester epoch on
      -- successful decapsulation (the only leaf that emits a key).
      all_goals
        obtain ⟨hks, hrest⟩ := Prod.mk.inj (Option.some.inj hproj)
        obtain ⟨hct, hrq⟩ := Prod.mk.inj hrest
        rw [← hct] at ht
        first
          | exact Or.inl ht
          | (rw [Finset.mem_insert] at ht
             rcases ht with ht | ht
             · first
                 | exact Or.inr (Or.inl ⟨hctRec, ht⟩)
                 | exact Or.inr (Or.inr ⟨hks.symm, ht.trans hrq⟩)
             · exact Or.inl ht)
          | (rw [Finset.mem_insert, Finset.mem_insert] at ht
             rcases ht with ht | ht | ht
             · exact Or.inr (Or.inr ⟨hks.symm, ht.trans hrq⟩)
             · exact Or.inr (Or.inl ⟨hctRec, ht⟩)
             · exact Or.inl ht)

/-- A supported send that emits a key writes it at the sender's responder parity: for every
positive epoch `t` whose index `t.toNat` is the emitted slot, `t` has the responder parity.
This is the send half of "at the owner's requester parity, only its own receive writes its
key table" (`Defs.lean:300`/`:346`; `Construction.lean:273`). -/
theorem send_emittedKey_responderParity
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym)
    (hres : st.res.resEpoch % 2 = if role = .A then 1 else 0)
    (key? : Option (ℕ × K)) (ρ : Message Sym) (tsnd : ℕ)
    (st' : State PK SK C Sym)
    (hout : some (key?, ρ, tsnd, st') ∈
      support (send role kem ecEk ecCt st))
    (tI : ℕ) (key : K) (hkey : key? = some (tI, key))
    (t : ℤ) (ht : 0 < t) (htI : t.toNat = tI) :
    t % 2 = if role = .A then 1 else 0 := by
  have hp := send_provenance role kem ecEk ecCt st key? ρ tsnd st' hout
  obtain ⟨hslot, -, -⟩ := hp.emitted_key tI key hkey
  have hres' : st'.res.resEpoch % 2 = if role = .A then 1 else 0 := by
    rcases hp.keygen_transition with ⟨h, -, -⟩ | ⟨pk, sk, -, h, -, -⟩
    · rw [h]
      exact hres
    · rw [h]
      omega
  -- `0 < t` makes `t.toNat` positive, so the emitted slot is the positive responder epoch.
  omega

/-- A supported send preserves soundness for the sender, once the emitted message is recorded
in its outgoing table and any emitted key in its key table, and for the receiver. -/
theorem ciphertextAckSoundness_send_step
    (roleS : Role) (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (stS stR : State PK SK C Sym)
    (msgsS msgsR : ℕ → Option (Message Sym × ℕ))
    (keyS keyR : ℕ → Option K)
    (hS : CiphertextAckSoundness roleS stS stR msgsS keyS)
    (hR : CiphertextAckSoundness roleS.peer stR stS msgsR keyR)
    (hres : stS.res.resEpoch % 2 = if roleS = .A then 1 else 0)
    (n : ℕ) (key? : Option (ℕ × K)) (ρ : Message Sym) (tsnd : ℕ)
    (stS' : State PK SK C Sym)
    (hout : some (key?, ρ, tsnd, stS') ∈
      support (send roleS kem ecEk ecCt stS)) :
    CiphertextAckSoundness roleS stS' stR
        (Function.update msgsS n (some (ρ, tsnd)))
        (match key? with
        | none => keyS
        | some (t, key) => Function.update keyS t (some key)) ∧
      CiphertextAckSoundness roleS.peer stR stS' msgsR keyR := by
  have hp := send_provenance roleS kem ecEk ecCt stS key? ρ tsnd stS' hout
  have hack : stS'.ack = stS.ack := hp.acknowledgements
  -- The new message advertises `ct-rec` exactly at the sender's own requester epoch.
  have hflag : ∀ (j : ℕ) (msg : Message Sym) (tj : ℕ),
      Function.update msgsS n (some (ρ, tsnd)) j = some (msg, tj) →
        msg.ack.ctRec = true → msg.tReq ∈ stS'.ack.ctRec := by
    intro j msg tj hj hfl
    rw [hack]
    by_cases hjn : j = n
    · subst hjn
      rw [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hj
      obtain ⟨rfl, rfl⟩ := hj
      have hadv := hp.advertised_acknowledgements.2
      rw [hfl] at hadv
      rw [hp.message_reqEpoch]
      exact of_decide_eq_true hadv.symm
    · rw [Function.update_of_ne hjn] at hj
      exact hS.own_flag j msg tj hj hfl
  have hpeerEntry : ∀ t ∈ stS'.ack.ctRec,
      t % 2 = (if roleS = .A then 1 else 0) → t ∈ stR.ack.ctRec := by
    intro t ht hpar
    rw [hack] at ht
    exact hS.peer_entry t ht hpar
  have hrecv : CiphertextAckSoundness roleS.peer stR stS' msgsR keyR := by
    refine ⟨hR.own_entry, hR.own_key, ?_, hR.own_flag⟩
    intro t ht hpar
    rw [hack]
    exact hR.peer_entry t ht hpar
  rcases key? with _ | ⟨tI, key⟩
  · refine ⟨⟨?_, ?_, hpeerEntry, hflag⟩, hrecv⟩
    · intro t ht hpos hpar
      rw [hack] at ht
      exact hS.own_entry t ht hpos hpar
    · intro t hpos hpar hkey
      rw [hack]
      exact hS.own_key t hpos hpar hkey
  · refine ⟨⟨?_, ?_, hpeerEntry, hflag⟩, hrecv⟩
    · intro t ht hpos hpar
      rw [hack] at ht
      change Function.update keyS tI (some key) t.toNat ≠ none
      by_cases htI : t.toNat = tI
      · rw [htI, Function.update_self]
        exact Option.some_ne_none key
      · rw [Function.update_of_ne htI]
        exact hS.own_entry t ht hpos hpar
    · intro t hpos hpar hkey
      change Function.update keyS tI (some key) t.toNat ≠ none at hkey
      rw [hack]
      by_cases htI : t.toNat = tI
      · -- The emitted slot sits at the sender's responder parity, not its requester parity.
        have hresPar := send_emittedKey_responderParity roleS kem ecEk ecCt stS hres
          (some (tI, key)) ρ tsnd stS' hout tI key rfl t hpos htI
        exfalso
        cases roleS <;>
          simp only [reduceCtorEq, if_true, if_false] at hpar hresPar <;>
          omega
      · rw [Function.update_of_ne htI] at hkey
        exact hS.own_key t hpos hpar hkey

/-- A successful receive, by the party `roleR`, of a message recorded in the peer's table
preserves soundness for both parties once any emitted key is recorded in the receiver's key
table. New `ct-rec` entries come from the flag, which is backed by the sender, or from own
decapsulation, which is recorded in the key table; role parity rules out the other readings. -/
theorem ciphertextAckSoundness_recv_step [DecidableEq Sym]
    (roleR : Role) (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (stR stS : State PK SK C Sym)
    (msgsR msgsS : ℕ → Option (Message Sym × ℕ))
    (keyR keyS : ℕ → Option K)
    (hR : CiphertextAckSoundness roleR stR stS msgsR keyR)
    (hS : CiphertextAckSoundness roleR.peer stS stR msgsS keyS)
    (hparR : RoleParity roleR stR msgsR)
    (hparS : RoleParity roleR.peer stS msgsS)
    (n : ℕ) (ρ : Message Sym) (tsnd : ℕ)
    (hmsg : msgsS n = some (ρ, tsnd))
    (key? : Option (ℕ × K)) (trcv : ℕ) (stR' : State PK SK C Sym)
    (hout : recv roleR kem hDet ecEk ecCt stR ρ = some (key?, trcv, stR')) :
    CiphertextAckSoundness roleR stR' stS msgsR
        (match key? with
        | none => keyR
        | some (t, key) => Function.update keyR t (some key)) ∧
      CiphertextAckSoundness roleR.peer stS stR' msgsS keyS := by
  have hsub : stR.ack.ctRec ⊆ stR'.ack.ctRec :=
    (recv_success_state_facts roleR kem hDet ecEk ecCt stR ρ key? trcv stR' hout).2.2.2.2.1
  have hreq := (roleParity_recv_step roleR kem hDet ecEk ecCt stR msgsR hparR ρ key? trcv
    stR' hout).reqEpoch_parity
  have hmsgPar := (hparS.message_parity n ρ tsnd hmsg).2
  have horigin := recv_ciphertextAck_origin roleR kem hDet ecEk ecCt stR ρ key? trcv stR' hout
  -- The flagged index has the sender's requester parity, the receiver's responder parity.
  have hflagPar : ρ.tReq % 2 = if roleR = .A then 1 else 0 := by
    cases roleR <;>
      simp only [Role.peer, reduceCtorEq, if_true, if_false] at hmsgPar ⊢ <;>
      omega
  have hpeer : CiphertextAckSoundness roleR.peer stS stR' msgsS keyS := by
    refine ⟨hS.own_entry, hS.own_key, ?_, hS.own_flag⟩
    intro t ht hpar
    exact hsub (hS.peer_entry t ht hpar)
  have hpeerEntry : ∀ t ∈ stR'.ack.ctRec,
      t % 2 = (if roleR = .A then 1 else 0) → t ∈ stS.ack.ctRec := by
    intro t ht hpar
    rcases horigin t ht with hold | ⟨hfl, rfl⟩ | ⟨-, rfl⟩
    · exact hR.peer_entry t hold hpar
    · exact hS.own_flag n ρ tsnd hmsg hfl
    · exfalso
      cases roleR <;>
        simp only [reduceCtorEq, if_true, if_false] at hpar hreq <;>
        omega
  have hflagR : ∀ (j : ℕ) (msg : Message Sym) (tj : ℕ),
      msgsR j = some (msg, tj) → msg.ack.ctRec = true → msg.tReq ∈ stR'.ack.ctRec :=
    fun j msg tj hj hfl => hsub (hR.own_flag j msg tj hj hfl)
  rcases key? with _ | ⟨tI, key⟩
  · refine ⟨⟨?_, ?_, hpeerEntry, hflagR⟩, hpeer⟩
    · intro t ht hpos hpar
      rcases horigin t ht with hold | ⟨-, rfl⟩ | ⟨hks, -⟩
      · exact hR.own_entry t hold hpos hpar
      · exfalso
        cases roleR <;>
          simp only [reduceCtorEq, if_true, if_false] at hpar hflagPar <;>
          omega
      · exact absurd hks Bool.false_ne_true
    · intro t hpos hpar hkey
      exact hsub (hR.own_key t hpos hpar hkey)
  · obtain ⟨-, -, hslot, -, hmem, -⟩ :=
      recv_emitted_key_facts roleR kem hDet ecEk ecCt stR ρ tI key trcv stR' hout
    refine ⟨⟨?_, ?_, hpeerEntry, hflagR⟩, hpeer⟩
    · intro t ht hpos hpar
      change Function.update keyR tI (some key) t.toNat ≠ none
      rcases horigin t ht with hold | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · by_cases htI : t.toNat = tI
        · rw [htI, Function.update_self]
          exact Option.some_ne_none key
        · rw [Function.update_of_ne htI]
          exact hR.own_entry t hold hpos hpar
      · exfalso
        cases roleR <;>
          simp only [reduceCtorEq, if_true, if_false] at hpar hflagPar <;>
          omega
      · rw [← hslot, Function.update_self]
        exact Option.some_ne_none key
    · intro t hpos hpar hkey
      change Function.update keyR tI (some key) t.toNat ≠ none at hkey
      by_cases htI : t.toNat = tI
      · -- The new slot is the positive post-receive requester epoch, recorded in `ct-rec`.
        have heq : t = stR'.req.reqEpoch := by omega
        rw [heq]
        exact hmem
      · rw [Function.update_of_ne htI] at hkey
        exact hsub (hR.own_key t hpos hpar hkey)

/-- Honest initial states satisfy ciphertext acknowledgement soundness: both parties start
with `ct-rec = {-1, 0}`, empty key tables, and empty message tables. -/
theorem initGameState_ciphertextAckSoundness
    (stA : StA PK SK C Sym) (stB : StB PK SK C Sym)
    (hA : stA ∈ support (initA () : ProbComp (StA PK SK C Sym)))
    (hB : stB ∈ support (initB () : ProbComp (StB PK SK C Sym))) :
    GameCiphertextAckSoundness (K := K) (SCKAScheme.initGameState stA stB) := by
  simp only [initA, init, support_pure, Set.mem_singleton_iff] at hA
  simp only [initB, init, support_pure, Set.mem_singleton_iff] at hB
  subst stA
  subst stB
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro t ht hpos _
    simp only [SCKAScheme.initGameState, Finset.mem_insert, Finset.mem_singleton] at ht
    omega
  · intro t _ _ hkey
    exact absurd rfl hkey
  · intro t ht _
    exact ht
  · intro j msg tj hj
    simp [SCKAScheme.initGameState] at hj
  · intro t ht hpos _
    simp only [SCKAScheme.initGameState, Finset.mem_insert, Finset.mem_singleton] at ht
    omega
  · intro t _ _ hkey
    exact absurd rfl hkey
  · intro t ht _
    exact ht
  · intro j msg tj hj
    simp [SCKAScheme.initGameState] at hj

/-- Every correctness-game oracle preserves role parity together with ciphertext
acknowledgement soundness. -/
theorem sckaCorrectnessImpl_preserves_ciphertextAckSoundness
    [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak) :
    QueryImpl.PreservesInv
      (SCKAScheme.sckaCorrectnessImpl (scheme kem hDet ecEk ecCt leak))
      (fun s => GameRoleParity
          (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym) s ∧
        GameCiphertextAckSoundness s) := by
  intro t s hs z hz
  refine ⟨sckaCorrectnessImpl_preserves_roleParity kem hDet ecEk ecCt leak t s hs.1 z hz, ?_⟩
  obtain ⟨hpar, hs⟩ := hs
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
        obtain ⟨key?, _, hsend, _, hstB, hmsgA, hmsgB, hkeyA, hkeyB⟩ :=
          oracleSendA_recorded_provenance kem hDet ecEk ecCt leak
            s s' tsnd epoch? ρ hz
        have hstep := ciphertextAckSoundness_send_step .A kem ecEk ecCt
          s.stA s.stB s.msgA s.msgB s.keyA s.keyB hs.1 hs.2 hpar.1.resEpoch_parity
          (s.nA + 1) key? ρ tsnd s'.stA hsend
        -- Case on `key?` so that the provenance and step-lemma key tables both reduce.
        rcases key? with _ | ⟨tI, key⟩ <;>
          obtain ⟨hA', hB'⟩ := hstep <;>
          refine ⟨?_, ?_⟩
        · rw [hstB, hmsgA, hkeyA]
          exact hA'
        · rw [hstB, hmsgB, hkeyB]
          exact hB'
        · rw [hstB, hmsgA, hkeyA]
          exact hA'
        · rw [hstB, hmsgB, hkeyB]
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
        obtain ⟨key?, _, hsend, _, hstA, hmsgB, hmsgA, hkeyB, hkeyA⟩ :=
          oracleSendB_recorded_provenance kem hDet ecEk ecCt leak
            s s' tsnd epoch? ρ hz
        have hstep := ciphertextAckSoundness_send_step .B kem ecEk ecCt
          s.stB s.stA s.msgB s.msgA s.keyB s.keyA hs.2 hs.1 hpar.2.resEpoch_parity
          (s.nB + 1) key? ρ tsnd s'.stB hsend
        -- Case on `key?` so that the provenance and step-lemma key tables both reduce.
        rcases key? with _ | ⟨tI, key⟩ <;>
          obtain ⟨hB', hA'⟩ := hstep <;>
          refine ⟨?_, ?_⟩
        · rw [hstA, hmsgA, hkeyA]
          exact hA'
        · rw [hstA, hmsgB, hkeyB]
          exact hB'
        · rw [hstA, hmsgA, hkeyA]
          exact hA'
        · rw [hstA, hmsgB, hkeyB]
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
            have hstep := ciphertextAckSoundness_recv_step .A kem hDet ecEk ecCt
              s.stA s.stB s.msgA s.msgB s.keyA s.keyB hs.1 hs.2 hpar.1 hpar.2
              n ρ tsnd hmsg key? trcv st' hrecv
            rcases key? with _ | ⟨tI, key⟩ <;>
              simp only [SCKAScheme.oracleRecvA, bind_pure_comp, StateT.run_bind,
                StateT.run_get, pure_bind, hmsg, hrecv, StateT.run_map, StateT.run_set,
                map_pure, support_pure] at hz <;>
              subst z <;>
              exact hstep
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
            have hstep := ciphertextAckSoundness_recv_step .B kem hDet ecEk ecCt
              s.stB s.stA s.msgB s.msgA s.keyB s.keyA hs.2 hs.1 hpar.2 hpar.1
              n ρ tsnd hmsg key? trcv st' hrecv
            rcases key? with _ | ⟨tI, key⟩ <;>
              simp only [SCKAScheme.oracleRecvB, bind_pure_comp, StateT.run_bind,
                StateT.run_get, pure_bind, hmsg, hrecv, StateT.run_map, StateT.run_set,
                map_pure, support_pure] at hz <;>
              subst z <;>
              exact ⟨hstep.2, hstep.1⟩

/-- Ciphertext acknowledgement soundness holds in every reachable correctness-game state from
honest initialization. -/
theorem simulateQ_ciphertextAckSoundness
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
    GameCiphertextAckSoundness z.2 := by
  have h := simulateQ_run_preservesInv _
    (fun s => GameRoleParity
        (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym) s ∧
      GameCiphertextAckSoundness s)
    (sckaCorrectnessImpl_preserves_ciphertextAckSoundness kem hDet ecEk ecCt leak)
    adv _
    ⟨initGameState_roleParity stA stB hA hB, initGameState_ciphertextAckSoundness stA stB hA hB⟩
    z hz
  exact h.2

/-- Parity-separated ciphertext acknowledgement soundness for the party `role` owning `st`,
in game key-table form: the paper's role-dependent reading of `ACK[t].ct-rec` (SCKA §4.2,
Figs. 17-18). For positive epochs, an entry at the owner's requester parity means the owner
decapsulated, and the owner's key table is populated there exactly at its own entries. An
entry at the owner's responder parity means the peer decapsulated. A true `ct-rec` flag on a
recorded peer message means the peer decapsulated at the flagged epoch. This says nothing
about which key was recorded. -/
structure CiphertextAckOwnership
    (role : Role) (st : State PK SK C Sym)
    (ownKey peerKey : ℕ → Option K)
    (peerMsgs : ℕ → Option (Message Sym × ℕ)) : Prop where
  own_decapsulation : ∀ t ∈ st.ack.ctRec, 0 < t →
    t % 2 = (if role = .A then 0 else 1) → ownKey t.toNat ≠ none
  own_key_recorded : ∀ t : ℤ, 0 < t → t % 2 = (if role = .A then 0 else 1) →
    ownKey t.toNat ≠ none → t ∈ st.ack.ctRec
  peer_decapsulation : ∀ t ∈ st.ack.ctRec, 0 < t →
    t % 2 = (if role = .A then 1 else 0) → peerKey t.toNat ≠ none
  peer_flag : ∀ (n : ℕ) (ρ : Message Sym) (tsnd : ℕ),
    peerMsgs n = some (ρ, tsnd) → ρ.ack.ctRec = true → 0 < ρ.tReq →
      peerKey ρ.tReq.toNat ≠ none

/-- Soundness for a party and for its peer, together with the peer's role parity, gives the
key-table form: responder-parity entries pass to the peer's `ct-rec` at the peer's requester
parity, where the peer's own entry is backed by the peer's key table. -/
theorem ciphertextAckOwnership_of_soundness
    (role : Role)
    (st peer : State PK SK C Sym)
    (ownMsgs peerMsgs : ℕ → Option (Message Sym × ℕ))
    (ownKey peerKey : ℕ → Option K)
    (hst : CiphertextAckSoundness role st peer ownMsgs ownKey)
    (hpeer : CiphertextAckSoundness role.peer peer st peerMsgs peerKey)
    (hpar : RoleParity role.peer peer peerMsgs) :
    CiphertextAckOwnership role st ownKey peerKey peerMsgs := by
  refine ⟨hst.own_entry, hst.own_key, ?_, ?_⟩
  · intro t ht hpos hparity
    -- The owner's responder parity is the peer's requester parity.
    have hpeerPar : t % 2 = if role.peer = .A then 0 else 1 := by
      cases role <;>
        simp only [Role.peer, reduceCtorEq, if_true, if_false] at hparity ⊢ <;>
        omega
    exact hpeer.own_entry t (hst.peer_entry t ht hparity) hpos hpeerPar
  · intro j msg tj hj hflag hpos
    exact hpeer.own_entry _ (hpeer.own_flag j msg tj hj hflag) hpos
      (hpar.message_parity j msg tj hj).2

/-- Parity-separated ciphertext acknowledgement soundness, in game key-table form, holds for
both parties in every reachable correctness-game state from honest initialization. -/
theorem simulateQ_ciphertextAckOwnership
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
    CiphertextAckOwnership .A z.2.stA z.2.keyA z.2.keyB z.2.msgB ∧
      CiphertextAckOwnership .B z.2.stB z.2.keyB z.2.keyA z.2.msgA := by
  have h1 := simulateQ_ciphertextAckSoundness kem hDet ecEk ecCt leak adv stA stB hA hB z hz
  have h2 := simulateQ_roleParity kem hDet ecEk ecCt leak adv stA stB hA hB z hz
  exact ⟨ciphertextAckOwnership_of_soundness .A _ _ _ _ _ _ h1.1 h1.2 h2.2,
    ciphertextAckOwnership_of_soundness .B _ _ _ _ _ _ h1.2 h1.1 h2.1⟩

end oppBiKemCKA
