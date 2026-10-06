/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Gavran, Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Correctness.OracleSupport
import SecureMessaging.SCKA.OppBiKEM.Correctness.CiphertextAckSoundness

/-!
# Epoch lockstep for Opp-BiKEM correctness

Epoch lockstep is intrinsic to the construction; no bounded-slack (`Δ_Slack`) assumption on
the adversary is needed. On every reachable correctness-game state, every recorded message
from the peer satisfies `ρ.tRes ≤ receiver.reqEpoch + 2`, and a requester-epoch advance
lands exactly on `ρ.tRes` (`simulateQ_lockstep_endpoint`).

The argument: a party advances its responder epoch only through the gate of `sendWith`,
which requires `tRes ∈ ctRec`. That entry sits at the sender's responder parity, so
ciphertext acknowledgement soundness (`CiphertextAckSoundness.peer_entry`) makes it the
peer's own decapsulation, and own decapsulations are recorded at or below the peer's current
requester epoch (`Lockstep.ctRec_req_le`). Hence `tRes + 2 ≤ peer.reqEpoch + 2`.

`Lockstep` is proved together with role parity and ciphertext acknowledgement soundness,
whose pre-state facts its preservation reads, as the conjunction `GameInv`. The game-level
preservation goes through the pure-update dispatch of `SCKA.Correctness.OracleSupport`, so
it contains no oracle-monad case analysis.
-/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-- Advancing the responder epoch in a supported send requires the gate of
`sendWith`: both adjacent ciphertext acknowledgements are present. -/
theorem send_advance_guard (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (key? : Option (ℕ × K)) (ρ : Message Sym) (tsnd : ℕ)
    (st' : State PK SK C Sym)
    (hout : some (key?, ρ, tsnd, st') ∈ support (send role kem ecEk ecCt st))
    (hadv : st'.res.resEpoch ≠ st.res.resEpoch) :
    st.res.resEpoch ∈ st.ack.ctRec ∧ st.res.resEpoch + role.offset ∈ st.ack.ctRec := by
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
    all_goals simp_all

/-- Epoch lockstep for the party `role` owning `st`, with peer state `peer` and own
outgoing table `ownMsgs`. -/
structure Lockstep (role : Role) (st peer : State PK SK C Sym)
    (ownMsgs : ℕ → Option (Message Sym × ℕ)) : Prop where
  reqEpoch_lower : (if role = .A then (0 : ℤ) else -1) ≤ st.req.reqEpoch
  resEpoch_lower : (if role = .A then (-1 : ℤ) else 0) ≤ st.res.resEpoch
  /-- The responder never runs more than one exchange ahead of the peer's requester. -/
  res_le_peer_req : st.res.resEpoch ≤ peer.req.reqEpoch + 2
  /-- The peer's requester epoch never overtakes the responder epoch that drives it. -/
  peer_req_le_res : peer.req.reqEpoch ≤ st.res.resEpoch
  /-- Own decapsulations are recorded at or below the current requester epoch. -/
  ctRec_req_le : ∀ t ∈ st.ack.ctRec, t % 2 = (if role = .A then 0 else 1) →
    t ≤ st.req.reqEpoch
  /-- Recorded messages carry a responder epoch at most the current one. -/
  message_res_le : ∀ (n : ℕ) (ρ : Message Sym) (tsnd : ℕ),
    ownMsgs n = some (ρ, tsnd) → ρ.tRes ≤ st.res.resEpoch

/-- Lockstep for both parties of a correctness-game state, each against its own table. -/
def GameLockstep
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) : Prop :=
  Lockstep .A s.stA s.stB s.msgA ∧ Lockstep .B s.stB s.stA s.msgB

/-- Honest initial states satisfy lockstep. -/
theorem initGameState_lockstep (stA : StA PK SK C Sym) (stB : StB PK SK C Sym)
    (hA : stA ∈ support (initA () : ProbComp (StA PK SK C Sym)))
    (hB : stB ∈ support (initB () : ProbComp (StB PK SK C Sym))) :
    GameLockstep (K := K) (SCKAScheme.initGameState stA stB) := by
  simp only [initA, initB, init, support_pure, Set.mem_singleton_iff] at hA hB
  subst stA
  subst stB
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  all_goals simp only [SCKAScheme.initGameState, Finset.mem_insert, Finset.mem_singleton,
    reduceCtorEq, if_true, if_false]
  all_goals first
    | omega
    | (intro t ht hp; omega)
    | (intro n ρ tsnd h; cases h)

/-- A supported send by `roleS` preserves lockstep for both parties once the emitted message
is recorded in the sender's table. -/
theorem lockstep_send_step (roleS : Role) (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (stS stR : State PK SK C Sym)
    (msgsS msgsR : ℕ → Option (Message Sym × ℕ)) (keyS : ℕ → Option K)
    (hparS : stS.res.resEpoch % 2 = if roleS = .A then 1 else 0)
    (hackS : CiphertextAckSoundness roleS stS stR msgsS keyS)
    (hS : Lockstep roleS stS stR msgsS) (hR : Lockstep roleS.peer stR stS msgsR)
    (n : ℕ) (key? : Option (ℕ × K)) (ρ : Message Sym) (tsnd : ℕ)
    (stS' : State PK SK C Sym)
    (hout : some (key?, ρ, tsnd, stS') ∈ support (send roleS kem ecEk ecCt stS)) :
    Lockstep roleS stS' stR (Function.update msgsS n (some (ρ, tsnd))) ∧
      Lockstep roleS.peer stR stS' msgsR := by
  have hp := send_provenance roleS kem ecEk ecCt stS key? ρ tsnd stS' hout
  have hack := hp.acknowledgements
  have hreq := hp.requester_epoch
  have hres : stS.res.resEpoch ≤ stS'.res.resEpoch ∧
      stS'.res.resEpoch ≤ stR.req.reqEpoch + 2 := by
    rcases hp.keygen_transition with ⟨h, -, -⟩ | ⟨-, -, -, h, -, -⟩
    · rw [h]
      exact ⟨le_rfl, hS.res_le_peer_req⟩
    · have hguard := send_advance_guard roleS kem ecEk ecCt stS key? ρ tsnd stS' hout
        (by rw [h]; omega)
      refine ⟨by rw [h]; omega, ?_⟩
      rw [h]
      by_cases hpos : 0 < stS.res.resEpoch
      · -- The gate entry sits at the sender's responder parity; n13 passes it to the peer,
        -- where it is an own decapsulation, hence at most the peer's requester epoch.
        have hmem := hackS.peer_entry _ hguard.1 hparS
        have hRpar : stS.res.resEpoch % 2 = if roleS.peer = .A then 0 else 1 := by
          cases roleS <;> simp only [Role.peer, reduceCtorEq, if_true, if_false] at hparS ⊢ <;>
            omega
        have := hR.ctRec_req_le _ hmem hRpar
        omega
      · -- Bootstrap: the first advance from `-1` (A) or `0` (B).
        have h1 := hS.resEpoch_lower
        have h2 := hR.reqEpoch_lower
        have h3 := hparS
        cases roleS <;> simp only [Role.peer, reduceCtorEq, if_true, if_false] at h1 h2 h3 <;>
          omega
  refine ⟨⟨?_, ?_, hres.2, ?_, ?_, ?_⟩,
    ⟨hR.reqEpoch_lower, hR.resEpoch_lower, ?_, ?_, hR.ctRec_req_le, hR.message_res_le⟩⟩
  · rw [hreq]
    exact hS.reqEpoch_lower
  · exact hS.resEpoch_lower.trans hres.1
  · exact hS.peer_req_le_res.trans hres.1
  · intro t ht hpar
    rw [hack] at ht
    rw [hreq]
    exact hS.ctRec_req_le t ht hpar
  · intro j msg tj hj
    by_cases hjn : j = n
    · subst hjn
      rw [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hj
      obtain ⟨rfl, rfl⟩ := hj
      rw [hp.message_resEpoch]
    · rw [Function.update_of_ne hjn] at hj
      exact (hS.message_res_le j msg tj hj).trans hres.1
  · rw [hreq]
    exact hR.res_le_peer_req
  · rw [hreq]
    exact hR.peer_req_le_res

/-- A successful receive by `roleR` of a message recorded in the peer's table preserves
lockstep for both parties. -/
theorem lockstep_recv_step [DecidableEq Sym]
    (roleR : Role) (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (stR stS : State PK SK C Sym)
    (msgsR msgsS : ℕ → Option (Message Sym × ℕ))
    (hparR : RoleParity roleR stR msgsR) (hparS : RoleParity roleR.peer stS msgsS)
    (hR : Lockstep roleR stR stS msgsR) (hS : Lockstep roleR.peer stS stR msgsS)
    (n : ℕ) (ρ : Message Sym) (tsnd : ℕ) (hmsg : msgsS n = some (ρ, tsnd))
    (key? : Option (ℕ × K)) (trcv : ℕ) (stR' : State PK SK C Sym)
    (hout : recv roleR kem hDet ecEk ecCt stR ρ = some (key?, trcv, stR')) :
    Lockstep roleR stR' stS msgsR ∧ Lockstep roleR.peer stS stR' msgsS := by
  obtain ⟨-, hres, -, hreq, -, -, -, -, -⟩ :=
    recv_success_state_facts roleR kem hDet ecEk ecCt stR ρ key? trcv stR' hout
  have hmsgRes : ρ.tRes ≤ stS.res.resEpoch := hS.message_res_le n ρ tsnd hmsg
  have hmsgPar := (hparS.message_parity n ρ tsnd hmsg).1
  have hflagPar0 := (hparS.message_parity n ρ tsnd hmsg).2
  have hreqPar := hparR.reqEpoch_parity
  have hreq_mono : stR.req.reqEpoch ≤ stR'.req.reqEpoch := by
    rw [hreq]
    split_ifs <;> omega
  have hreq_le : stR'.req.reqEpoch ≤ stS.res.resEpoch := by
    rw [hreq]
    split_ifs with hlt
    · -- Same parity and strictly below: the advance lands at or below `ρ.tRes`.
      cases roleR <;>
        simp only [Role.peer, reduceCtorEq, if_true, if_false] at hmsgPar hreqPar <;>
        omega
    · exact hS.peer_req_le_res
  have horigin := recv_ciphertextAck_origin roleR kem hDet ecEk ecCt stR ρ key? trcv stR' hout
  have hflagPar : ρ.tReq % 2 = if roleR = .A then 1 else 0 := by
    cases roleR <;>
      simp only [Role.peer, reduceCtorEq, if_true, if_false] at hflagPar0 ⊢ <;>
      omega
  refine ⟨⟨hR.reqEpoch_lower.trans hreq_mono, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨hS.reqEpoch_lower, hS.resEpoch_lower, ?_, hreq_le, hS.ctRec_req_le, hS.message_res_le⟩⟩
  · rw [hres]
    exact hR.resEpoch_lower
  · rw [hres]
    exact hR.res_le_peer_req
  · rw [hres]
    exact hR.peer_req_le_res
  · intro t ht hpar
    rcases horigin t ht with hold | ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact (hR.ctRec_req_le t hold hpar).trans hreq_mono
    · exfalso
      cases roleR <;> simp only [reduceCtorEq, if_true, if_false] at hpar hflagPar <;> omega
    · exact le_rfl
  · intro j msg tj hj
    rw [hres]
    exact hR.message_res_le j msg tj hj
  · exact hS.res_le_peer_req.trans (by omega)

/-- The three cross-party invariants, taken together because lockstep's preservation
reads parity and ciphertext-acknowledgement soundness of the pre-state. -/
def GameInv
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) : Prop :=
  GameRoleParity s ∧ GameCiphertextAckSoundness s ∧ GameLockstep s

/-- Every correctness-game oracle preserves `GameInv`. -/
theorem sckaCorrectnessImpl_preserves_gameInv
    [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak) :
    QueryImpl.PreservesInv
      (SCKAScheme.sckaCorrectnessImpl (scheme kem hDet ecEk ecCt leak))
      (GameInv (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym)) := by
  apply SCKAScheme.preservesInv_sckaCorrectnessImpl_of
  · -- SendA
    intro s hs key? ρ tsnd stA' hout
    obtain ⟨hpar, hack, hlock⟩ := hs
    rcases key? with _ | ⟨tI, key⟩
    all_goals
      have hout' : some (_, ρ, tsnd, stA') ∈ support (send .A kem ecEk ecCt s.stA) := hout
      have hpar' := roleParity_send_step .A kem ecEk ecCt s.stA s.msgA hpar.1
        (s.nA + 1) _ ρ tsnd stA' hout'
      have hack' := ciphertextAckSoundness_send_step .A kem ecEk ecCt s.stA s.stB s.msgA s.msgB
        s.keyA s.keyB hack.1 hack.2 hpar.1.resEpoch_parity (s.nA + 1) _ ρ tsnd stA' hout'
      have hlock' := lockstep_send_step .A kem ecEk ecCt s.stA s.stB s.msgA s.msgB s.keyA
        hpar.1.resEpoch_parity hack.1 hlock.1 hlock.2 (s.nA + 1) _ ρ tsnd stA' hout'
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · simpa [Role.peer] using hpar'
      · simpa using hpar.2
      · simpa [Role.peer] using hack'.1
      · simpa [Role.peer] using hack'.2
      · simpa [Role.peer] using hlock'.1
      · simpa [Role.peer] using hlock'.2
  · -- SendB
    intro s hs key? ρ tsnd stB' hout
    obtain ⟨hpar, hack, hlock⟩ := hs
    rcases key? with _ | ⟨tI, key⟩
    all_goals
      have hout' : some (_, ρ, tsnd, stB') ∈ support (send .B kem ecEk ecCt s.stB) := hout
      have hpar' := roleParity_send_step .B kem ecEk ecCt s.stB s.msgB hpar.2
        (s.nB + 1) _ ρ tsnd stB' hout'
      have hack' := ciphertextAckSoundness_send_step .B kem ecEk ecCt s.stB s.stA s.msgB s.msgA
        s.keyB s.keyA hack.2 hack.1 hpar.2.resEpoch_parity (s.nB + 1) _ ρ tsnd stB' hout'
      have hlock' := lockstep_send_step .B kem ecEk ecCt s.stB s.stA s.msgB s.msgA s.keyB
        hpar.2.resEpoch_parity hack.2 hlock.2 hlock.1 (s.nB + 1) _ ρ tsnd stB' hout'
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · simpa using hpar.1
      · simpa [Role.peer] using hpar'
      · simpa [Role.peer] using hack'.2
      · simpa [Role.peer] using hack'.1
      · simpa [Role.peer] using hlock'.2
      · simpa [Role.peer] using hlock'.1
  · -- RecvA, success
    intro s hs n ρ tsnd hmsg key? trcv stA' hrecv
    obtain ⟨hpar, hack, hlock⟩ := hs
    rcases key? with _ | ⟨tI, key⟩
    all_goals
      have hrecv' : recv .A kem hDet ecEk ecCt s.stA ρ = some (_, trcv, stA') := hrecv
      have hpar' := roleParity_recv_step .A kem hDet ecEk ecCt s.stA s.msgA hpar.1
        ρ _ trcv stA' hrecv'
      have hack' := ciphertextAckSoundness_recv_step .A kem hDet ecEk ecCt s.stA s.stB
        s.msgA s.msgB s.keyA s.keyB hack.1 hack.2 hpar.1 hpar.2 n ρ tsnd hmsg _ trcv stA' hrecv'
      have hlock' := lockstep_recv_step .A kem hDet ecEk ecCt s.stA s.stB s.msgA s.msgB
        hpar.1 hpar.2 hlock.1 hlock.2 n ρ tsnd hmsg _ trcv stA' hrecv'
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · simpa [Role.peer] using hpar'
      · simpa using hpar.2
      · simpa [Role.peer] using hack'.1
      · simpa [Role.peer] using hack'.2
      · simpa [Role.peer] using hlock'.1
      · simpa [Role.peer] using hlock'.2
  · -- RecvA, local failure: only `correct` changes.
    intro s hs n ρ tsnd hmsg hrecv
    exact hs
  · -- RecvB, success
    intro s hs n ρ tsnd hmsg key? trcv stB' hrecv
    obtain ⟨hpar, hack, hlock⟩ := hs
    rcases key? with _ | ⟨tI, key⟩
    all_goals
      have hrecv' : recv .B kem hDet ecEk ecCt s.stB ρ = some (_, trcv, stB') := hrecv
      have hpar' := roleParity_recv_step .B kem hDet ecEk ecCt s.stB s.msgB hpar.2
        ρ _ trcv stB' hrecv'
      have hack' := ciphertextAckSoundness_recv_step .B kem hDet ecEk ecCt s.stB s.stA
        s.msgB s.msgA s.keyB s.keyA hack.2 hack.1 hpar.2 hpar.1 n ρ tsnd hmsg _ trcv stB' hrecv'
      have hlock' := lockstep_recv_step .B kem hDet ecEk ecCt s.stB s.stA s.msgB s.msgA
        hpar.2 hpar.1 hlock.2 hlock.1 n ρ tsnd hmsg _ trcv stB' hrecv'
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · simpa using hpar.1
      · simpa [Role.peer] using hpar'
      · simpa [Role.peer] using hack'.2
      · simpa [Role.peer] using hack'.1
      · simpa [Role.peer] using hlock'.2
      · simpa [Role.peer] using hlock'.1
  · intro s hs n ρ tsnd hmsg hrecv
    exact hs

/-- `GameInv` holds on every reachable correctness-game state from honest initialisation. -/
theorem simulateQ_gameInv
    [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (stA : StA PK SK C Sym) (stB : StB PK SK C Sym)
    (hA : stA ∈ support (initA () : ProbComp (StA PK SK C Sym)))
    (hB : stB ∈ support (initB () : ProbComp (StB PK SK C Sym)))
    (z : Bool × SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hz : z ∈ support ((simulateQ
      (SCKAScheme.sckaCorrectnessImpl (scheme kem hDet ecEk ecCt leak)) adv).run
      (SCKAScheme.initGameState stA stB))) :
    GameInv z.2 :=
  simulateQ_run_preservesInv _ GameInv
    (sckaCorrectnessImpl_preserves_gameInv kem hDet ecEk ecCt leak) adv _
    ⟨initGameState_roleParity stA stB hA hB, initGameState_ciphertextAckSoundness stA stB hA hB,
      initGameState_lockstep stA stB hA hB⟩ z hz

/-- Lockstep endpoint, with no slack assumption: every recorded peer message is at most
two epochs ahead of the receiver's requester epoch, and an advance lands exactly on the
message's responder epoch. -/
theorem simulateQ_lockstep_endpoint
    [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak)
    (adv : SCKAScheme.SCKACorrectnessAdversary (Message Sym))
    (stA : StA PK SK C Sym) (stB : StB PK SK C Sym)
    (hA : stA ∈ support (initA () : ProbComp (StA PK SK C Sym)))
    (hB : stB ∈ support (initB () : ProbComp (StB PK SK C Sym)))
    (z : Bool × SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hz : z ∈ support ((simulateQ
      (SCKAScheme.sckaCorrectnessImpl (scheme kem hDet ecEk ecCt leak)) adv).run
      (SCKAScheme.initGameState stA stB))) :
    (∀ (n : ℕ) (ρ : Message Sym) (tsnd : ℕ), z.2.msgB n = some (ρ, tsnd) →
      ρ.tRes ≤ z.2.stA.req.reqEpoch + 2 ∧
        (z.2.stA.req.reqEpoch < ρ.tRes → ρ.tRes = z.2.stA.req.reqEpoch + 2)) ∧
    (∀ (n : ℕ) (ρ : Message Sym) (tsnd : ℕ), z.2.msgA n = some (ρ, tsnd) →
      ρ.tRes ≤ z.2.stB.req.reqEpoch + 2 ∧
        (z.2.stB.req.reqEpoch < ρ.tRes → ρ.tRes = z.2.stB.req.reqEpoch + 2)) := by
  obtain ⟨hpar, -, hlock⟩ := simulateQ_gameInv kem hDet ecEk ecCt leak adv stA stB hA hB z hz
  refine ⟨?_, ?_⟩
  · intro n ρ tsnd hmsg
    have h1 := hlock.2.message_res_le n ρ tsnd hmsg
    have h2 := hlock.2.res_le_peer_req
    have hp1 := (hpar.2.message_parity n ρ tsnd hmsg).1
    have hp2 := hpar.1.reqEpoch_parity
    simp only [reduceCtorEq, if_true, if_false] at hp1 hp2
    omega
  · intro n ρ tsnd hmsg
    have h1 := hlock.1.message_res_le n ρ tsnd hmsg
    have h2 := hlock.1.res_le_peer_req
    have hp1 := (hpar.1.message_parity n ρ tsnd hmsg).1
    have hp2 := hpar.2.reqEpoch_parity
    simp only [reduceCtorEq, if_true, if_false] at hp1 hp2
    omega

end oppBiKemCKA
