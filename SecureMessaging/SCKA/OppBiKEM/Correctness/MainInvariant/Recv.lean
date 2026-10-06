/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Gavran, Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Correctness.MainInvariant
import SecureMessaging.SCKA.OppBiKEM.Correctness.RecvSpec
import SecureMessaging.SCKA.OppBiKEM.Correctness.ReceiveState

/-!
# The main invariant is preserved by a receive

For a message recorded in the peer's table, the receive succeeds and the main invariant holds
afterwards for both parties, with the transcript unchanged. The receiver's key, if one is
emitted, is the transcript key of the decapsulated epoch; this is the only place where KEM
correctness is used, through the hypothesis `hdec`.

The proof reads `recv` through `recvSpec`. The non-stale cases share the requester epoch
`ρ.tRes` (`recvReq_eq_tRes`), and the acknowledgement update `recvAck` is characterised by
membership (`mem_recvAck_ctRec`, `mem_recvAck_ekRec`).
-/

open OracleComp KEMScheme ErasureCodePayload

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-- Membership in the ciphertext acknowledgements after ingesting a message's flags. -/
theorem mem_recvAck_ctRec (role : Role) (ack : Acknowledgements) (ρ : Message Sym) (t : ℤ) :
    t ∈ (recvAck role ack ρ).ctRec ↔ t ∈ ack.ctRec ∨ (ρ.ack.ctRec = true ∧ t = ρ.tReq) := by
  unfold recvAck
  by_cases h : ρ.ack.ctRec = true <;> simp [h, or_comm]

/-- Membership in the public-key acknowledgements after ingesting a message's flags. -/
theorem mem_recvAck_ekRec (role : Role) (ack : Acknowledgements) (ρ : Message Sym) (t : ℤ) :
    t ∈ (recvAck role ack ρ).ekRec ↔
      t ∈ ack.ekRec ∨ (ρ.ack.ekRec = true ∧ t = ρ.tReq + role.offset) := by
  unfold recvAck
  by_cases h : ρ.ack.ekRec = true <;> simp [h, or_comm]

theorem recvAck_ctRec_subset (role : Role) (ack : Acknowledgements) (ρ : Message Sym) :
    ack.ctRec ⊆ (recvAck role ack ρ).ctRec := by
  intro t ht
  rw [mem_recvAck_ctRec]
  exact Or.inl ht

theorem recvAck_ekRec_subset (role : Role) (ack : Acknowledgements) (ρ : Message Sym) :
    ack.ekRec ⊆ (recvAck role ack ρ).ekRec := by
  intro t ht
  rw [mem_recvAck_ekRec]
  exact Or.inl ht

/-- An empty buffer is consistent whenever the state's other fields are arbitrary. -/
theorem bufferConsistent_of_empty (role : Role) {kem : KEMScheme ProbComp K PK SK C}
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (T : Transcript kem) (st : State PK SK C Sym) (h : st.req.receivedChunks = ∅) :
    BufferConsistent role ecEk ecCt T st := by
  unfold BufferConsistent
  have hpk : ∀ (M : Type) (ecp : ErasureCodePayload M Sym) (m : M),
      ∃ I : Finset (Fin ecp.ec.N), (∅ : Finset (ℕ × Sym)) = payloadChunks ecp m I ∧
        I.card < ecp.ec.nchunk := by
    intro M ecp m
    refine ⟨∅, ?_, by simpa using ecp.ec.nchunk_pos⟩
    simp [payloadChunks, ErasureCode.encodeChunks]
  split_ifs <;> (try split) <;> simp only [h] <;> first | rfl | exact hpk _ _ _

section Receive

variable {roleR : Role} {kem : KEMScheme ProbComp K PK SK C} {hDet : kem.DeterministicDecaps}
  {ecEk : ErasureCodePayload PK Sym} {ecCt : ErasureCodePayload C Sym}
  {T : Transcript kem} {stR stS : State PK SK C Sym}
  {msgsR msgsS : ℕ → Option (Message Sym × ℕ)} {keyR keyS : ℕ → Option K}
  {tcurR tcurS : ℕ}
  (hR : PartyInv roleR ecEk ecCt T stR stS msgsR keyR keyS tcurR)
  (hS : PartyInv roleR.peer ecEk ecCt T stS stR msgsS keyS keyR tcurS)
  {n : ℕ} {ρ : Message Sym} {tsnd : ℕ} (hmsg : msgsS n = some (ρ, tsnd))

include hR hS hmsg

omit hR in
/-- The received message is honest with respect to the peer's state. -/
theorem recv_msgInv : MessageInv roleR.peer ecEk ecCt T stS ρ tsnd := hS.msgs n ρ tsnd hmsg

omit hR in
/-- The carried responder epoch has the receiver's requester parity. -/
theorem recv_tRes_parity : ρ.tRes % 2 = roleR.reqParity := by
  have h := (recv_msgInv hS hmsg).res_parity
  simpa using h

omit hR in
/-- The carried requester epoch has the receiver's responder parity. -/
theorem recv_tReq_parity : ρ.tReq % 2 = roleR.resParity := by
  have h := (recv_msgInv hS hmsg).req_parity
  simpa using h

omit hR in
/-- The carried responder epoch is at most two ahead of the receiver's requester epoch. -/
theorem recv_tRes_le : ρ.tRes ≤ stR.req.reqEpoch + 2 :=
  (recv_msgInv hS hmsg).res_le.trans hS.res_le_peer_req

/-- The carried requester epoch is at most the receiver's responder epoch. -/
theorem recv_tReq_le : ρ.tReq ≤ stR.res.resEpoch :=
  (recv_msgInv hS hmsg).req_le.trans hR.peer_req_le_res

/-- A non-stale message lands the requester epoch exactly on its responder epoch. -/
theorem recvReq_eq_tRes (hns : ¬ ρ.tRes < stR.req.reqEpoch) : recvReq stR ρ = ρ.tRes := by
  have h1 := recv_tRes_le hS hmsg
  have h2 := recv_tRes_parity hS hmsg
  have h3 := hR.req_parity
  unfold recvReq
  split_ifs with hlt <;> omega

/-- On an epoch advance the previous requester epoch is already acknowledged: the peer's gate
required it, and the peer's responder-parity entries are the receiver's own. -/
theorem recv_advance_prev (hadv : stR.req.reqEpoch < ρ.tRes) :
    stR.req.reqEpoch ∈ stR.ack.ctRec := by
  have h1 := recv_tRes_le hS hmsg
  have hle := (recv_msgInv hS hmsg).res_le
  by_cases hpos : 0 < stR.req.reqEpoch
  · have hpar : stR.req.reqEpoch % 2 = roleR.peer.resParity := by
      simpa using hR.req_parity
    have hmem := hS.ctRec_res_closed stR.req.reqEpoch hpos hpar (by omega)
    exact hS.ctRec_res_peer _ hmem hpar
  · have hlow := hR.req_lower
    have hinit := hR.init_acks
    have : stR.req.reqEpoch = -1 ∨ stR.req.reqEpoch = 0 := by omega
    rcases this with h | h <;> rw [h] <;> simp [hinit.1, hinit.2]

omit hR in
/-- A ciphertext flag is backed by the peer's own decapsulation. -/
theorem recv_flag_ct_peer (hfl : ρ.ack.ctRec = true) : ρ.tReq ∈ stS.ack.ctRec :=
  (recv_msgInv hS hmsg).ct_flag hfl

omit hR in
/-- A ciphertext flag at a positive epoch is backed by an encapsulation. -/
theorem recv_flag_ct_enc (hfl : ρ.ack.ctRec = true) (hpos : 0 < ρ.tReq) :
    (T ρ.tReq).enc.isSome = true :=
  hS.ctRec_req_enc ρ.tReq (recv_flag_ct_peer hS hmsg hfl) hpos
    (by simpa using recv_tReq_parity hS hmsg)

/-- A public-key flag is backed by the peer's decoded copy of the receiver's key. -/
theorem recv_flag_ek_peerKey (hfl : ρ.ack.ekRec = true) :
    (stS.res.ekPeer (ρ.tReq + roleR.offset)).isSome = true := by
  have h := (recv_msgInv hS hmsg).ek_flag hfl
  have hidx : ρ.tReq - roleR.peer.offset = ρ.tReq + roleR.offset := by
    rw [Role.peer_offset]; omega
  rw [hidx] at h
  have hpar : (ρ.tReq + roleR.offset) % 2 = roleR.peer.resParity := by
    have := recv_tReq_parity hS hmsg
    cases roleR <;> simp only [Role.peer, Role.offset, Role.resParity] at this ⊢ <;> omega
  exact hS.ekRec_res _ h hpar

/-- A ciphertext message implies the receiver holds the peer's key for that epoch (phase
causality). -/
theorem recv_bit1_ekPeer (hbit : ρ.bit = some 1) :
    (stR.res.ekPeer (ρ.tRes - roleR.offset)).isSome = true := by
  have h := (recv_msgInv hS hmsg).bit1_acked hbit
  have hidx : ρ.tRes + roleR.peer.offset = ρ.tRes - roleR.offset := by
    rw [Role.peer_offset]; omega
  rw [hidx] at h
  have hpar : (ρ.tRes - roleR.offset) % 2 = roleR.peer.reqParity := by
    have := recv_tRes_parity hS hmsg
    cases roleR <;> simp only [Role.peer, Role.offset, Role.reqParity] at this ⊢ <;> omega
  have h' := hS.ekRec_req _ h hpar
  exact h'

omit hR in
/-- A stale message's ciphertext flag is already recorded by the receiver. -/
theorem recv_stale_flag (hst : ρ.tRes < stR.req.reqEpoch) (hfl : ρ.ack.ctRec = true) :
    ρ.tReq ∈ stR.ack.ctRec :=
  hS.msgs_stale n ρ tsnd hmsg hst hfl

/-- Every positive epoch up to the message's horizon is acknowledged after ingesting its
flags. -/
theorem recv_horizon_mem (s : ℤ) (hs : 0 < s) (hle : s ≤ ρ.sendingEpoch) :
    s ∈ (recvAck roleR stR.ack ρ).ctRec := by
  have m := recv_msgInv hS hmsg
  have hmemS := m.horizon_mem s hs hle
  rw [mem_recvAck_ctRec]
  rcases PartyInv.parity_cases roleR s with hp | hp
  · -- receiver's requester parity = peer's responder parity: the entry is the receiver's own
    left
    exact hS.ctRec_res_peer s hmemS (by simpa using hp)
  · -- receiver's responder parity = peer's requester parity
    obtain ⟨hle', heq⟩ := m.horizon_req s hs hle (by simpa using hp)
    by_cases hs' : s = ρ.tReq
    · right
      exact ⟨heq hs', hs'⟩
    · left
      have hreq := recv_tReq_le hR hS hmsg
      have hpar := recv_tReq_parity hS hmsg
      exact hR.ctRec_res_closed s hs hp (by omega)

/-- The message's horizon is at most the sending horizon of any acknowledgement set extending
the ingested one. -/
theorem recv_horizon_le (ack' : Acknowledgements)
    (hsub : (recvAck roleR stR.ack ρ).ctRec ⊆ ack'.ctRec) :
    ρ.sendingEpoch ≤ ack'.sendingHorizon := by
  by_cases h0 : ρ.sendingEpoch = 0
  · rw [h0]; exact Nat.zero_le _
  have hpos : (0 : ℤ) < ρ.sendingEpoch := by omega
  have hmem : (ρ.sendingEpoch : ℤ) ∈ ack'.ctRec :=
    hsub (recv_horizon_mem hR hS hmsg _ hpos le_rfl)
  have hmem' : (ρ.sendingEpoch : ℤ) - 1 ∈ ack'.ctRec := by
    by_cases h1 : ρ.sendingEpoch = 1
    · rw [h1]
      simpa using hsub (recvAck_ctRec_subset _ _ _ hR.init_acks.2)
    · exact hsub (recv_horizon_mem hR hS hmsg _ (by omega) (by omega))
  unfold Acknowledgements.sendingHorizon
  have hfilt : (ρ.sendingEpoch : ℤ) ∈ ack'.ctRec.filter (fun t => t - 1 ∈ ack'.ctRec) :=
    Finset.mem_filter.mpr ⟨hmem, hmem'⟩
  have := Finset.le_sup (f := Int.toNat) hfilt
  simpa using this

/-- The receiver's game horizon stays below the sending horizon of any acknowledgement set
extending the ingested one. -/
theorem recv_tcur_le (ack' : Acknowledgements)
    (hsub : (recvAck roleR stR.ack ρ).ctRec ⊆ ack'.ctRec) :
    max tcurR ρ.sendingEpoch ≤ ack'.sendingHorizon := by
  refine max_le ?_ (recv_horizon_le hR hS hmsg ack' hsub)
  exact hR.horizon.trans (Acknowledgements.sendingHorizon_mono _ _
    ((recvAck_ctRec_subset _ _ _).trans hsub))

/-! ### Transfer of message honesty to a later state of the same party -/

omit hR hS hmsg in
/-- Message honesty depends on the sender's state only through monotone fields. -/
theorem MessageInv.mono {role : Role} {st st' : State PK SK C Sym} {ρ' : Message Sym} {tsnd' : ℕ}
    (h : MessageInv role ecEk ecCt T st ρ' tsnd')
    (hres : st'.res.resEpoch = st.res.resEpoch) (hreq : st.req.reqEpoch ≤ st'.req.reqEpoch)
    (hct : st.ack.ctRec ⊆ st'.ack.ctRec) (hek : st.ack.ekRec ⊆ st'.ack.ekRec) :
    MessageInv role ecEk ecCt T st' ρ' tsnd' where
  epoch := h.epoch
  res_parity := h.res_parity
  req_parity := h.req_parity
  res_le := hres ▸ h.res_le
  req_le := h.req_le.trans hreq
  res_lower := h.res_lower
  req_lower := h.req_lower
  pk_chunk := h.pk_chunk
  ct_chunk := h.ct_chunk
  no_chunk := h.no_chunk
  ct_flag := fun hf => hct (h.ct_flag hf)
  ek_flag := fun hf => hek (h.ek_flag hf)
  bit1_acked := fun hb => hek (h.bit1_acked hb)
  horizon_mem := fun s hs hle => hct (h.horizon_mem s hs hle)
  horizon_req := h.horizon_req

/-! ### The post-state of a receive that emits no key -/

/-- Parity bookkeeping: the receiver's responder epoch and the carried requester epoch have the
responder parity; the carried responder epoch has the requester parity. -/
theorem recv_parity_facts :
    ρ.tReq % 2 = roleR.resParity ∧ ρ.tRes % 2 = roleR.reqParity ∧
      (ρ.tReq + roleR.offset) % 2 = roleR.reqParity ∧
      (ρ.tRes - roleR.offset) % 2 = roleR.resParity := by
  have h1 := recv_tReq_parity hS hmsg
  have h2 := recv_tRes_parity hS hmsg
  refine ⟨h1, h2, ?_, ?_⟩ <;>
    cases roleR <;> simp only [Role.offset, Role.reqParity, Role.resParity] at h1 h2 ⊢ <;> omega

/-- After a non-stale receive without a key, the invariant holds for both parties. The peer-key
map may have been extended (`ekPeer'`), with matching new `ekRec` entries (`ack'`); the buffer
of the post-state is supplied as a hypothesis. -/
theorem partyInv_recv_noKey (hns : ¬ ρ.tRes < stR.req.reqEpoch)
    (ekPeer' : ℤ → Option PK) (ack' : Acknowledgements) (chunks' : Finset (ℕ × Sym))
    (hstable : ∀ e, (stR.res.ekPeer e).isSome = true → ekPeer' e = stR.res.ekPeer e)
    (hekT : ∀ e pk, ekPeer' e = some pk → ∃ sk, (T e).keypair = some (pk, sk))
    (hekpar : ∀ e, (ekPeer' e).isSome = true →
      e % 2 = roleR.resParity ∧ e ≤ ρ.tRes - roleR.offset)
    (hct : ack'.ctRec = (recvAck roleR stR.ack ρ).ctRec)
    (hek : (recvAck roleR stR.ack ρ).ekRec ⊆ ack'.ekRec)
    (heknew : ∀ t ∈ ack'.ekRec, t ∉ (recvAck roleR stR.ack ρ).ekRec →
      t % 2 = roleR.resParity ∧ (ekPeer' t).isSome = true)
    (hbuf : BufferConsistent roleR ecEk ecCt T
      (recvFinish roleR stR ρ.tRes ekPeer' stR.req.dk chunks' ack')) :
    PartyInv roleR ecEk ecCt T (recvFinish roleR stR ρ.tRes ekPeer' stR.req.dk chunks' ack')
        stS msgsR keyR keyS (max tcurR ρ.sendingEpoch) ∧
      PartyInv roleR.peer ecEk ecCt T stS
        (recvFinish roleR stR ρ.tRes ekPeer' stR.req.dk chunks' ack') msgsS keyS keyR tcurS := by
  have m := recv_msgInv hS hmsg
  obtain ⟨hpReq, hpRes, hpReqO, hpResO⟩ := recv_parity_facts hR hS hmsg
  have hqle : stR.req.reqEpoch ≤ ρ.tRes := not_lt.mp hns
  have hqle2 := recv_tRes_le hS hmsg
  have hreqpar := hR.req_parity
  have hrespar := hR.res_parity
  have htReqle := recv_tReq_le hR hS hmsg
  -- membership in the post-state acknowledgements
  have hmemct : ∀ t, t ∈ ack'.ctRec ↔ t ∈ stR.ack.ctRec ∨ (ρ.ack.ctRec = true ∧ t = ρ.tReq) := by
    intro t; rw [hct, mem_recvAck_ctRec]
  have hctsub : stR.ack.ctRec ⊆ ack'.ctRec := fun t ht => (hmemct t).2 (Or.inl ht)
  have heksub : stR.ack.ekRec ⊆ ack'.ekRec := (recvAck_ekRec_subset _ _ _).trans hek
  -- a requester-parity epoch is in the new `ctRec` iff it was before
  have hmemreq : ∀ t, t % 2 = roleR.reqParity → (t ∈ ack'.ctRec ↔ t ∈ stR.ack.ctRec) := by
    intro t htp
    rw [hmemct]
    constructor
    · rintro (h | ⟨-, rfl⟩)
      · exact h
      · exfalso
        cases roleR <;> simp only [Role.reqParity, Role.resParity] at htp hpReq <;> omega
    · exact Or.inl
  have hresnot : stR.res.resEpoch % 2 ≠ roleR.reqParity := by
    cases roleR <;> simp only [Role.reqParity, Role.resParity] at hrespar ⊢ <;> omega
  set st' := recvFinish roleR stR ρ.tRes ekPeer' stR.req.dk chunks' ack' with hst'
  have hst'res : st'.res.resEpoch = stR.res.resEpoch := rfl
  have hst'req : st'.req.reqEpoch = ρ.tRes := rfl
  have hst'dk : st'.req.dk = stR.req.dk := rfl
  have hst'ack : st'.ack = ack' := rfl
  have hst'ekPeer : st'.res.ekPeer = ekPeer' := rfl
  have hst'ct : st'.res.ct = if stR.res.resEpoch ∈ ack'.ctRec then none else stR.res.ct := rfl
  have hst'ek : st'.req.ek =
      if stR.res.resEpoch + roleR.offset ∈ ack'.ekRec then none else stR.req.ek := rfl
  refine ⟨?_, ?_⟩
  · refine
      { res_parity := hrespar
        req_parity := hpRes
        res_lower := hR.res_lower
        req_lower := by have := hR.req_lower; rw [hst'req]; omega
        init_acks := ⟨hctsub hR.init_acks.1, hctsub hR.init_acks.2⟩
        res_le_peer_req := hR.res_le_peer_req
        peer_req_le_res := hR.peer_req_le_res
        keypair_pos := hR.keypair_pos
        keypair_future := hR.keypair_future
        ek_T := ?_
        dk_T := hR.dk_T
        T_dk := ?_
        dk_shape := hR.dk_shape
        ek_acked := ?_
        keypair_current := hR.keypair_current
        enc_future := hR.enc_future
        enc_current := ?_
        ct_T := ?_
        ct_acked := ?_
        enc_ekRec := fun e he henc => heksub (hR.enc_ekRec e he henc)
        ekPeer_T := hekT
        ekPeer_parity := fun e he => (hekpar e he).1
        ekPeer_le := fun e he => (hekpar e he).2
        key_zero := hR.key_zero
        key_res := hR.key_res
        key_req := ?_
        ctRec_req_enc := ?_
        ctRec_req_le := ?_
        ctRec_res_peer := ?_
        ctRec_res_le := ?_
        ctRec_req_closed := ?_
        ctRec_res_closed := fun t ht hp hlt => hctsub (hR.ctRec_res_closed t ht hp hlt)
        ekRec_res := ?_
        ekRec_req := ?_
        buffer := hbuf
        horizon := ?_
        msgs := ?_
        msgs_flag_mono := hR.msgs_flag_mono
        msgs_stale := hR.msgs_stale }
    · intro pk hpk
      rw [hst'ek] at hpk
      by_cases h : stR.res.resEpoch + roleR.offset ∈ ack'.ekRec
      · rw [if_pos h] at hpk
        exact absurd hpk (by simp)
      · rw [if_neg h] at hpk
        exact hR.ek_T pk hpk
    · intro e pk sk hkp hp hnot
      rw [hst'ack, hmemreq e hp] at hnot
      exact hR.T_dk e pk sk hkp hp hnot
    · intro hek
      rw [hst'ek] at hek
      change (T (stR.res.resEpoch + roleR.offset)).keypair = none ∨
        stR.res.resEpoch + roleR.offset ∈ ack'.ekRec
      by_cases h : stR.res.resEpoch + roleR.offset ∈ ack'.ekRec
      · exact Or.inr h
      · rw [if_neg h] at hek
        exact (hR.ek_acked hek).imp_right (fun h' => heksub h')
    · intro c k henc
      rw [hst'res] at henc
      rw [hst'ct, hst'ack]
      by_cases hin : stR.res.resEpoch ∈ ack'.ctRec
      · exact Or.inr hin
      · rw [if_neg hin]
        rcases hR.enc_current c k henc with h | h
        · exact Or.inl h
        · exact absurd (hctsub h) hin
    · intro c hc
      rw [hst'ct] at hc
      by_cases h : stR.res.resEpoch ∈ ack'.ctRec
      · rw [if_pos h] at hc
        exact absurd hc (by simp)
      · rw [if_neg h] at hc
        exact hR.ct_T c hc
    · intro hin
      have hin' : stR.res.resEpoch ∈ ack'.ctRec := hin
      change (if stR.res.resEpoch ∈ ack'.ctRec then none else stR.res.ct) = none
      rw [if_pos hin']
    · intro e he hp
      change keyR e.toNat = if e ∈ ack'.ctRec then (T e).key else none
      rw [hR.key_req e he hp]
      by_cases hin : e ∈ stR.ack.ctRec
      · rw [if_pos hin, if_pos ((hmemreq e hp).2 hin)]
      · rw [if_neg hin, if_neg (fun h => hin ((hmemreq e hp).1 h))]
    · intro t ht hpos hp
      rw [hst'ack, hmemreq t hp] at ht
      exact hR.ctRec_req_enc t ht hpos hp
    · intro t ht hp
      rw [hst'ack, hmemreq t hp] at ht
      rw [hst'req]
      exact (hR.ctRec_req_le t ht hp).trans hqle
    · intro t ht hp
      rw [hst'ack, hmemct] at ht
      rcases ht with h | ⟨hfl, rfl⟩
      · exact hR.ctRec_res_peer t h hp
      · exact recv_flag_ct_peer hS hmsg hfl
    · intro t ht hp
      rw [hst'ack, hmemct] at ht
      rw [hst'res]
      rcases ht with h | ⟨-, rfl⟩
      · exact hR.ctRec_res_le t h hp
      · exact htReqle
    · intro t ht hp hlt
      rw [hst'req] at hlt
      apply hctsub
      have hle : t ≤ stR.req.reqEpoch := by
        cases roleR <;> simp only [Role.reqParity] at hp hpRes hreqpar <;> omega
      rcases lt_or_eq_of_le hle with hlt' | rfl
      · exact hR.ctRec_req_closed t ht hp hlt'
      · exact recv_advance_prev hR hS hmsg (by omega)
    · intro t ht hp
      rw [hst'ack] at ht
      rw [hst'ekPeer]
      by_cases hold : t ∈ (recvAck roleR stR.ack ρ).ekRec
      · rw [mem_recvAck_ekRec] at hold
        rcases hold with h | ⟨-, rfl⟩
        · have := hR.ekRec_res t h hp
          rw [hstable t this]
          exact this
        · exfalso
          cases roleR <;> simp only [Role.reqParity, Role.resParity] at hp hpReqO <;> omega
      · exact (heknew t ht hold).2
    · intro t ht hp
      rw [hst'ack] at ht
      by_cases hold : t ∈ (recvAck roleR stR.ack ρ).ekRec
      · rw [mem_recvAck_ekRec] at hold
        rcases hold with h | ⟨hfl, rfl⟩
        · exact hR.ekRec_req t h hp
        · exact recv_flag_ek_peerKey hR hS hmsg hfl
      · exfalso
        have := (heknew t ht hold).1
        cases roleR <;> simp only [Role.reqParity, Role.resParity] at hp this <;> omega
    · rw [hst'ack]
      exact recv_tcur_le hR hS hmsg ack' (by rw [hct])
    · intro j ρ' t' hj
      exact (hR.msgs j ρ' t' hj).mono hst'res (by rw [hst'req]; exact hqle)
        (by rw [hst'ack]; exact hctsub) (by rw [hst'ack]; exact heksub)
  · refine
      { res_parity := hS.res_parity
        req_parity := hS.req_parity
        res_lower := hS.res_lower
        req_lower := hS.req_lower
        init_acks := hS.init_acks
        res_le_peer_req := by rw [hst'req]; exact hS.res_le_peer_req.trans (by omega)
        peer_req_le_res := by rw [hst'req]; exact m.res_le
        keypair_pos := hS.keypair_pos
        keypair_future := hS.keypair_future
        ek_T := hS.ek_T
        dk_T := hS.dk_T
        T_dk := hS.T_dk
        dk_shape := hS.dk_shape
        ek_acked := hS.ek_acked
        keypair_current := hS.keypair_current
        enc_future := hS.enc_future
        enc_current := hS.enc_current
        ct_T := hS.ct_T
        ct_acked := hS.ct_acked
        enc_ekRec := hS.enc_ekRec
        ekPeer_T := hS.ekPeer_T
        ekPeer_parity := hS.ekPeer_parity
        ekPeer_le := hS.ekPeer_le
        key_zero := hS.key_zero
        key_res := hS.key_res
        key_req := hS.key_req
        ctRec_req_enc := hS.ctRec_req_enc
        ctRec_req_le := hS.ctRec_req_le
        ctRec_res_peer := fun t ht hp => by rw [hst'ack]; exact hctsub (hS.ctRec_res_peer t ht hp)
        ctRec_res_le := hS.ctRec_res_le
        ctRec_req_closed := hS.ctRec_req_closed
        ctRec_res_closed := hS.ctRec_res_closed
        ekRec_res := hS.ekRec_res
        ekRec_req := fun t ht hp => by
          rw [hst'ekPeer]
          have := hS.ekRec_req t ht hp
          rw [hstable t this]
          exact this
        buffer := hS.buffer
        horizon := hS.horizon
        msgs := hS.msgs
        msgs_flag_mono := hS.msgs_flag_mono
        msgs_stale := ?_ }
    intro j ρ' t' hj hlt hfl
    rw [hst'req] at hlt
    rw [hst'ack, hmemct]
    have m' := hS.msgs j ρ' t' hj
    by_cases hold : ρ'.tRes < stR.req.reqEpoch
    · exact Or.inl (hS.msgs_stale j ρ' t' hj hold hfl)
    · -- `ρ'` becomes stale only on an advance; compare it with the received message.
      have heq : ρ'.tRes < ρ.tRes := hlt
      obtain ⟨hle, himp⟩ := hS.msgs_flag_mono j n ρ' ρ t' tsnd hj hmsg heq hfl
      by_cases hsame : ρ'.tReq = ρ.tReq
      · exact Or.inr ⟨himp hsame, hsame⟩
      · left
        have hpar' : ρ'.tReq % 2 = roleR.resParity := by simpa using m'.req_parity
        by_cases hpos : 0 < ρ'.tReq
        · apply hR.ctRec_res_closed ρ'.tReq hpos hpar'
          cases roleR <;> simp only [Role.resParity] at hpar' hpReq <;> omega
        · have hlow := m'.req_lower
          have : ρ'.tReq = -1 ∨ ρ'.tReq = 0 := by omega
          rcases this with h | h <;> rw [h]
          · exact hR.init_acks.1
          · exact hR.init_acks.2

/-! ### The decapsulation transition -/

omit hR hmsg in
/-- Decapsulating the current requester epoch `q` of an invariant state: the secret key for `q`
is dropped, `q` is acknowledged, and the game key table receives the transcript key. -/
theorem partyInv_decaps_local {st₁ : State PK SK C Sym} {ownKey : ℕ → Option K} {tcur : ℕ}
    (h₁ : PartyInv roleR ecEk ecCt T st₁ stS msgsR ownKey keyS tcur)
    (hS₁ : PartyInv roleR.peer ecEk ecCt T stS st₁ msgsS keyS ownKey tcurS)
    (q : ℤ) (hq : st₁.req.reqEpoch = q) (hqpos : 0 < q) (hqpar : q % 2 = roleR.reqParity)
    (hqnot : q ∉ st₁.ack.ctRec) (c : C) (k : K) (henc : (T q).enc = some (c, k))
    (hbuf : st₁.req.receivedChunks = ∅) :
    PartyInv roleR ecEk ecCt T
        { st₁ with req := { st₁.req with dk := st₁.req.dk.filter (fun p => p.1 != q) }
                   ack := { st₁.ack with ctRec := insert q st₁.ack.ctRec } }
        stS msgsR (Function.update ownKey q.toNat (some k)) keyS tcur ∧
      PartyInv roleR.peer ecEk ecCt T stS
        { st₁ with req := { st₁.req with dk := st₁.req.dk.filter (fun p => p.1 != q) }
                   ack := { st₁.ack with ctRec := insert q st₁.ack.ctRec } }
        msgsS keyS (Function.update ownKey q.toNat (some k)) tcurS := by
  have hqnat : ∀ e : ℤ, 0 < e → e.toNat = q.toNat → e = q := by
    intro e he h
    have h1 := Int.toNat_of_nonneg (le_of_lt he)
    have h2 := Int.toNat_of_nonneg (le_of_lt hqpos)
    omega
  have hrespar := h₁.res_parity
  have hresne : st₁.res.resEpoch ≠ q := by
    intro h
    rw [h] at hrespar
    cases roleR <;> simp only [Role.reqParity, Role.resParity] at hrespar hqpar <;> omega
  have hsub : st₁.ack.ctRec ⊆ insert q st₁.ack.ctRec := Finset.subset_insert _ _
  refine ⟨?_, ?_⟩
  · refine
      { res_parity := h₁.res_parity
        req_parity := h₁.req_parity
        res_lower := h₁.res_lower
        req_lower := h₁.req_lower
        init_acks := ⟨hsub h₁.init_acks.1, hsub h₁.init_acks.2⟩
        res_le_peer_req := h₁.res_le_peer_req
        peer_req_le_res := h₁.peer_req_le_res
        keypair_pos := h₁.keypair_pos
        keypair_future := h₁.keypair_future
        ek_T := h₁.ek_T
        dk_T := ?_
        T_dk := ?_
        dk_shape := ?_
        ek_acked := h₁.ek_acked
        keypair_current := h₁.keypair_current
        enc_future := h₁.enc_future
        enc_current := fun c' k' h => (h₁.enc_current c' k' h).imp_right (fun h' => hsub h')
        ct_T := h₁.ct_T
        ct_acked := ?_
        enc_ekRec := h₁.enc_ekRec
        ekPeer_T := h₁.ekPeer_T
        ekPeer_parity := h₁.ekPeer_parity
        ekPeer_le := h₁.ekPeer_le
        key_zero := ?_
        key_res := ?_
        key_req := ?_
        ctRec_req_enc := ?_
        ctRec_req_le := ?_
        ctRec_res_peer := ?_
        ctRec_res_le := ?_
        ctRec_req_closed := fun t ht hp hlt => hsub (h₁.ctRec_req_closed t ht hp hlt)
        ctRec_res_closed := fun t ht hp hlt => hsub (h₁.ctRec_res_closed t ht hp hlt)
        ekRec_res := h₁.ekRec_res
        ekRec_req := h₁.ekRec_req
        buffer := bufferConsistent_of_empty _ _ _ _ _ hbuf
        horizon := h₁.horizon.trans (Acknowledgements.sendingHorizon_mono _ _ hsub)
        msgs := fun j ρ' t' hj => (h₁.msgs j ρ' t' hj).mono rfl le_rfl hsub (fun _ h => h)
        msgs_flag_mono := h₁.msgs_flag_mono
        msgs_stale := h₁.msgs_stale }
    · intro e sk hmem
      simp only [List.mem_filter, bne_iff_ne, ne_eq] at hmem
      obtain ⟨hp, hpos, hle, hkey, hkp⟩ := h₁.dk_T e sk hmem.1
      refine ⟨hp, hpos, hle, ?_, hkp⟩
      rw [Function.update_of_ne (fun h => hmem.2 (hqnat e hpos h))]
      exact hkey
    · intro e pk sk hkp hp hnot
      simp only [Finset.mem_insert, not_or] at hnot
      simp only [List.mem_filter, bne_iff_ne, ne_eq]
      exact ⟨h₁.T_dk e pk sk hkp hp hnot.2, hnot.1⟩
    · rcases h₁.dk_shape with h | ⟨sk, h⟩
      · left
        simp [h]
      · by_cases heq : st₁.res.resEpoch + roleR.offset = q
        · left
          simp [h, heq]
        · right
          exact ⟨sk, by simp [h, heq]⟩
    · intro hin
      simp only [Finset.mem_insert] at hin
      rcases hin with h | h
      · exact absurd h hresne
      · exact h₁.ct_acked h
    · rw [Function.update_of_ne (by omega)]
      exact h₁.key_zero
    · intro e he hp
      have hne : e.toNat ≠ q.toNat := by
        intro h
        have := hqnat e he h
        subst this
        cases roleR <;> simp only [Role.reqParity, Role.resParity] at hp hqpar <;> omega
      rw [Function.update_of_ne hne]
      exact h₁.key_res e he hp
    · intro e he hp
      by_cases heq : e = q
      · subst heq
        rw [Function.update_self, if_pos (Finset.mem_insert_self _ _), EpochTranscript.key, henc]
        rfl
      · have hne : e.toNat ≠ q.toNat := fun h => heq (hqnat e he h)
        rw [Function.update_of_ne hne, h₁.key_req e he hp]
        simp only [Finset.mem_insert, heq, false_or]
    · intro t ht hpos hp
      simp only [Finset.mem_insert] at ht
      rcases ht with rfl | ht
      · rw [henc]; rfl
      · exact h₁.ctRec_req_enc t ht hpos hp
    · intro t ht hp
      simp only [Finset.mem_insert] at ht
      rcases ht with rfl | ht
      · exact le_of_eq hq.symm
      · exact h₁.ctRec_req_le t ht hp
    · intro t ht hp
      simp only [Finset.mem_insert] at ht
      rcases ht with rfl | ht
      · exfalso
        cases roleR <;> simp only [Role.reqParity, Role.resParity] at hp hqpar <;> omega
      · exact h₁.ctRec_res_peer t ht hp
    · intro t ht hp
      simp only [Finset.mem_insert] at ht
      rcases ht with rfl | ht
      · exfalso
        cases roleR <;> simp only [Role.reqParity, Role.resParity] at hp hqpar <;> omega
      · exact h₁.ctRec_res_le t ht hp
  · refine
      { res_parity := hS₁.res_parity
        req_parity := hS₁.req_parity
        res_lower := hS₁.res_lower
        req_lower := hS₁.req_lower
        init_acks := hS₁.init_acks
        res_le_peer_req := hS₁.res_le_peer_req
        peer_req_le_res := hS₁.peer_req_le_res
        keypair_pos := hS₁.keypair_pos
        keypair_future := hS₁.keypair_future
        ek_T := hS₁.ek_T
        dk_T := hS₁.dk_T
        T_dk := hS₁.T_dk
        dk_shape := hS₁.dk_shape
        ek_acked := hS₁.ek_acked
        keypair_current := hS₁.keypair_current
        enc_future := hS₁.enc_future
        enc_current := hS₁.enc_current
        ct_T := hS₁.ct_T
        ct_acked := hS₁.ct_acked
        enc_ekRec := hS₁.enc_ekRec
        ekPeer_T := hS₁.ekPeer_T
        ekPeer_parity := hS₁.ekPeer_parity
        ekPeer_le := hS₁.ekPeer_le
        key_zero := hS₁.key_zero
        key_res := hS₁.key_res
        key_req := hS₁.key_req
        ctRec_req_enc := hS₁.ctRec_req_enc
        ctRec_req_le := hS₁.ctRec_req_le
        ctRec_res_peer := fun t ht hp => hsub (hS₁.ctRec_res_peer t ht hp)
        ctRec_res_le := hS₁.ctRec_res_le
        ctRec_req_closed := hS₁.ctRec_req_closed
        ctRec_res_closed := hS₁.ctRec_res_closed
        ekRec_res := hS₁.ekRec_res
        ekRec_req := hS₁.ekRec_req
        buffer := hS₁.buffer
        horizon := hS₁.horizon
        msgs := hS₁.msgs
        msgs_flag_mono := hS₁.msgs_flag_mono
        msgs_stale := fun j ρ' t' hj hlt hfl => hsub (hS₁.msgs_stale j ρ' t' hj hlt hfl) }

omit hR hS hmsg in
/-- `BufferConsistent` for a `recvFinish` state, stated on the supplied fields. -/
theorem bufferConsistent_recvFinish (role : Role) (st : State PK SK C Sym) (q : ℤ)
    (ekPeer' : ℤ → Option PK) (dk' : List (ℤ × SK)) (chunks' : Finset (ℕ × Sym))
    (ack' : Acknowledgements)
    (h : if q ∈ ack'.ctRec then chunks' = ∅
      else if (ekPeer' (q - role.offset)).isNone = true then
        match (T (q - role.offset)).keypair with
        | none => chunks' = ∅
        | some (pk, _) => ∃ I, chunks' = payloadChunks ecEk pk I ∧ I.card < ecEk.ec.nchunk
      else
        match (T q).enc with
        | none => chunks' = ∅
        | some (c, _) => ∃ I, chunks' = payloadChunks ecCt c I ∧ I.card < ecCt.ec.nchunk) :
    BufferConsistent role ecEk ecCt T (recvFinish role st q ekPeer' dk' chunks' ack') := h

/-! ### The buffer before a payload chunk is processed -/

omit hR hS hmsg in
theorem payloadChunks_empty {M : Type} (ecp : ErasureCodePayload M Sym) (m : M) :
    payloadChunks ecp m ∅ = ∅ := by
  simp [payloadChunks, ErasureCode.encodeChunks]

omit hR in
/-- A non-stale message's responder epoch is positive once the transcript has material for it. -/
theorem recv_tRes_pos_of_keypair (hkp : ((T (ρ.tRes - roleR.offset)).keypair).isSome = true) :
    0 < ρ.tRes := by
  have hpar : (ρ.tRes - roleR.offset) % 2 = roleR.peer.reqParity := by
    have := recv_tRes_parity hS hmsg
    cases roleR <;> simp only [Role.peer, Role.offset, Role.reqParity] at this ⊢ <;> omega
  have hpos := hS.keypair_pos _ hpar hkp
  have := recv_tRes_parity hS hmsg
  cases roleR <;> simp only [Role.offset, Role.reqParity] at hpos this <;> omega

/-- If the current epoch's ciphertext is acknowledged, the peer key for it is installed. -/
theorem recv_ekPeer_of_ctRec (hpos : 0 < ρ.tRes) (hin : ρ.tRes ∈ stR.ack.ctRec) :
    (stR.res.ekPeer (ρ.tRes - roleR.offset)).isSome = true := by
  have hpar := recv_tRes_parity hS hmsg
  have henc := hR.ctRec_req_enc _ hin hpos hpar
  have hparS : ρ.tRes % 2 = roleR.peer.resParity := by simpa using hpar
  have hek := hS.enc_ekRec _ hparS henc
  have hidx : ρ.tRes + roleR.peer.offset = ρ.tRes - roleR.offset := by
    rw [Role.peer_offset]; omega
  rw [hidx] at hek
  have hparS' : (ρ.tRes - roleR.offset) % 2 = roleR.peer.reqParity := by
    cases roleR <;> simp only [Role.peer, Role.offset, Role.reqParity] at hpar ⊢ <;> omega
  exact hS.ekRec_req _ hek hparS'

/-- On the public-key path the buffer is an honest sub-threshold chunk set of the peer's key
for the message's epoch, and the message carries a chunk of that key. -/
theorem recv_buffer_pk (hns : ¬ ρ.tRes < stR.req.reqEpoch) (hbit : ρ.bit = some 0)
    (hnone : (stR.res.ekPeer (ρ.tRes - roleR.offset)).isNone = true) :
    ρ.tRes ∉ stR.ack.ctRec ∧
    ∃ pk sk i I, (T (ρ.tRes - roleR.offset)).keypair = some (pk, sk) ∧
      ρ.ch = some (ecEk.encode pk i) ∧
      stR.req.receivedChunks = payloadChunks ecEk pk I ∧ I.card < ecEk.ec.nchunk := by
  have m := recv_msgInv hS hmsg
  obtain ⟨pk, sk, i, hkp, hch⟩ := m.pk_chunk hbit
  have hidx : ρ.tRes + roleR.peer.offset = ρ.tRes - roleR.offset := by
    rw [Role.peer_offset]; omega
  rw [hidx] at hkp
  have hpos := recv_tRes_pos_of_keypair hS hmsg (by rw [hkp]; rfl)
  have hqnot : ρ.tRes ∉ stR.ack.ctRec := by
    intro hin
    have := recv_ekPeer_of_ctRec hR hS hmsg hpos hin
    rw [Option.isNone_iff_eq_none] at hnone
    rw [hnone] at this
    cases this
  refine ⟨hqnot, pk, sk, i, ?_⟩
  have hbuf := hR.buffer
  unfold BufferConsistent at hbuf
  by_cases hadv : stR.req.reqEpoch < ρ.tRes
  · -- advance: the previous epoch is acknowledged, so the buffer is empty
    have hprev := recv_advance_prev hR hS hmsg hadv
    rw [if_pos hprev] at hbuf
    exact ⟨∅, hkp, hch, by rw [hbuf, payloadChunks_empty], by simpa using ecEk.ec.nchunk_pos⟩
  · have hq : stR.req.reqEpoch = ρ.tRes := by omega
    rw [hq, if_neg hqnot, if_pos hnone, hkp] at hbuf
    obtain ⟨I, hI, hcard⟩ := hbuf
    exact ⟨I, hkp, hch, hI, hcard⟩

/-- On the ciphertext path with a chunk present, the buffer is an honest sub-threshold chunk
set of the message epoch's ciphertext, and the chunk encodes that ciphertext. -/
theorem recv_buffer_ct (hns : ¬ ρ.tRes < stR.req.reqEpoch) (hbit : ρ.bit = some 1)
    (hqnot : ρ.tRes ∉ stR.ack.ctRec) (ch : ℕ × Sym) (hch : ρ.ch = some ch) :
    ∃ c k i I, (T ρ.tRes).enc = some (c, k) ∧ ch = ecCt.encode c i ∧
      stR.req.receivedChunks = payloadChunks ecCt c I ∧ I.card < ecCt.ec.nchunk := by
  have m := recv_msgInv hS hmsg
  obtain ⟨c, k, i, henc, hchi⟩ := m.ct_chunk hbit ch hch
  have hsome := recv_bit1_ekPeer hR hS hmsg hbit
  have hbuf := hR.buffer
  unfold BufferConsistent at hbuf
  by_cases hadv : stR.req.reqEpoch < ρ.tRes
  · have hprev := recv_advance_prev hR hS hmsg hadv
    rw [if_pos hprev] at hbuf
    exact ⟨c, k, i, ∅, henc, hchi, by rw [hbuf, payloadChunks_empty],
      by simpa using ecCt.ec.nchunk_pos⟩
  · have hq : stR.req.reqEpoch = ρ.tRes := by omega
    have hnotnone : ¬ (stR.res.ekPeer (ρ.tRes - roleR.offset)).isNone = true := by
      intro h
      rw [Option.isNone_iff_eq_none] at h
      rw [h] at hsome
      exact absurd hsome (by simp)
    rw [hq, if_neg hqnot, if_neg hnotnone, henc] at hbuf
    obtain ⟨I, hI, hcard⟩ := hbuf
    exact ⟨c, k, i, I, henc, hchi, hI, hcard⟩

/-- When the buffer is left unchanged by a non-stale receive, it stays consistent. -/
theorem recv_buffer_unchanged (hns : ¬ ρ.tRes < stR.req.reqEpoch) :
    BufferConsistent roleR ecEk ecCt T
      (recvFinish roleR stR ρ.tRes stR.res.ekPeer stR.req.dk stR.req.receivedChunks
        (recvAck roleR stR.ack ρ)) := by
  by_cases hadv : stR.req.reqEpoch < ρ.tRes
  · have hprev := recv_advance_prev hR hS hmsg hadv
    have hbuf := hR.buffer
    unfold BufferConsistent at hbuf
    rw [if_pos hprev] at hbuf
    exact bufferConsistent_of_empty _ _ _ _ _ hbuf
  · have hq : stR.req.reqEpoch = ρ.tRes := by omega
    have hiff : (ρ.tRes ∈ (recvAck roleR stR.ack ρ).ctRec) = (ρ.tRes ∈ stR.ack.ctRec) := by
      apply propext
      rw [mem_recvAck_ctRec]
      constructor
      · rintro (h | ⟨-, h⟩)
        · exact h
        · exfalso
          have h1 := recv_tRes_parity hS hmsg
          have h2 := recv_tReq_parity hS hmsg
          rw [h] at h1
          cases roleR <;> simp only [Role.reqParity, Role.resParity] at h1 h2 <;> omega
      · exact Or.inl
    have hbuf := hR.buffer
    unfold BufferConsistent at hbuf ⊢
    simp only [recvFinish, hiff]
    rw [hq] at hbuf
    exact hbuf

/-! ### The stale case -/

/-- A stale message changes only the acknowledgements, and its ciphertext flag is already
recorded. -/
theorem partyInv_recv_stale (hst : ρ.tRes < stR.req.reqEpoch) :
    PartyInv roleR ecEk ecCt T { stR with ack := recvAck roleR stR.ack ρ } stS msgsR keyR keyS
        (max tcurR ρ.sendingEpoch) ∧
      PartyInv roleR.peer ecEk ecCt T stS { stR with ack := recvAck roleR stR.ack ρ } msgsS keyS
        keyR tcurS := by
  have hct : (recvAck roleR stR.ack ρ).ctRec = stR.ack.ctRec := by
    ext t
    rw [mem_recvAck_ctRec]
    constructor
    · rintro (h | ⟨hfl, rfl⟩)
      · exact h
      · exact recv_stale_flag hS hmsg hst hfl
    · exact Or.inl
  have heksub : stR.ack.ekRec ⊆ (recvAck roleR stR.ack ρ).ekRec := recvAck_ekRec_subset _ _ _
  obtain ⟨hpReq, hpRes, hpReqO, hpResO⟩ := recv_parity_facts hR hS hmsg
  refine ⟨?_, ?_⟩
  · refine
      { res_parity := hR.res_parity
        req_parity := hR.req_parity
        res_lower := hR.res_lower
        req_lower := hR.req_lower
        init_acks := by rw [hct]; exact hR.init_acks
        res_le_peer_req := hR.res_le_peer_req
        peer_req_le_res := hR.peer_req_le_res
        keypair_pos := hR.keypair_pos
        keypair_future := hR.keypair_future
        ek_T := hR.ek_T
        dk_T := hR.dk_T
        T_dk := fun e pk sk hkp hp hnot => hR.T_dk e pk sk hkp hp (by rwa [hct] at hnot)
        dk_shape := hR.dk_shape
        ek_acked := fun hek => (hR.ek_acked hek).imp_right (fun h' => heksub h')
        keypair_current := hR.keypair_current
        enc_future := hR.enc_future
        enc_current := fun c k h => by rw [hct]; exact hR.enc_current c k h
        ct_T := hR.ct_T
        ct_acked := fun h => hR.ct_acked (by rwa [hct] at h)
        enc_ekRec := fun e he henc => heksub (hR.enc_ekRec e he henc)
        ekPeer_T := hR.ekPeer_T
        ekPeer_parity := hR.ekPeer_parity
        ekPeer_le := hR.ekPeer_le
        key_zero := hR.key_zero
        key_res := hR.key_res
        key_req := fun e he hp => by rw [hct]; exact hR.key_req e he hp
        ctRec_req_enc := fun t ht hpos hp => hR.ctRec_req_enc t (by rwa [hct] at ht) hpos hp
        ctRec_req_le := fun t ht hp => hR.ctRec_req_le t (by rwa [hct] at ht) hp
        ctRec_res_peer := fun t ht hp => hR.ctRec_res_peer t (by rwa [hct] at ht) hp
        ctRec_res_le := fun t ht hp => hR.ctRec_res_le t (by rwa [hct] at ht) hp
        ctRec_req_closed := fun t ht hp hlt => by rw [hct]; exact hR.ctRec_req_closed t ht hp hlt
        ctRec_res_closed := fun t ht hp hlt => by rw [hct]; exact hR.ctRec_res_closed t ht hp hlt
        ekRec_res := ?_
        ekRec_req := ?_
        buffer := ?_
        horizon := ?_
        msgs := fun j ρ' t' hj => (hR.msgs j ρ' t' hj).mono rfl le_rfl (by rw [hct]) heksub
        msgs_flag_mono := hR.msgs_flag_mono
        msgs_stale := hR.msgs_stale }
    · intro t ht hp
      rw [mem_recvAck_ekRec] at ht
      rcases ht with h | ⟨-, rfl⟩
      · exact hR.ekRec_res t h hp
      · exfalso
        cases roleR <;> simp only [Role.reqParity, Role.resParity] at hp hpReqO <;> omega
    · intro t ht hp
      rw [mem_recvAck_ekRec] at ht
      rcases ht with h | ⟨hfl, rfl⟩
      · exact hR.ekRec_req t h hp
      · exact recv_flag_ek_peerKey hR hS hmsg hfl
    · have hbuf := hR.buffer
      unfold BufferConsistent at hbuf ⊢
      simp only [hct]
      exact hbuf
    · change max tcurR ρ.sendingEpoch ≤ (recvAck roleR stR.ack ρ).sendingHorizon
      exact recv_tcur_le hR hS hmsg _ (fun _ h => h)
  · refine
      { res_parity := hS.res_parity
        req_parity := hS.req_parity
        res_lower := hS.res_lower
        req_lower := hS.req_lower
        init_acks := hS.init_acks
        res_le_peer_req := hS.res_le_peer_req
        peer_req_le_res := hS.peer_req_le_res
        keypair_pos := hS.keypair_pos
        keypair_future := hS.keypair_future
        ek_T := hS.ek_T
        dk_T := hS.dk_T
        T_dk := hS.T_dk
        dk_shape := hS.dk_shape
        ek_acked := hS.ek_acked
        keypair_current := hS.keypair_current
        enc_future := hS.enc_future
        enc_current := hS.enc_current
        ct_T := hS.ct_T
        ct_acked := hS.ct_acked
        enc_ekRec := hS.enc_ekRec
        ekPeer_T := hS.ekPeer_T
        ekPeer_parity := hS.ekPeer_parity
        ekPeer_le := hS.ekPeer_le
        key_zero := hS.key_zero
        key_res := hS.key_res
        key_req := hS.key_req
        ctRec_req_enc := hS.ctRec_req_enc
        ctRec_req_le := hS.ctRec_req_le
        ctRec_res_peer := fun t ht hp => by
          change t ∈ (recvAck roleR stR.ack ρ).ctRec
          rw [hct]; exact hS.ctRec_res_peer t ht hp
        ctRec_res_le := hS.ctRec_res_le
        ctRec_req_closed := hS.ctRec_req_closed
        ctRec_res_closed := hS.ctRec_res_closed
        ekRec_res := hS.ekRec_res
        ekRec_req := hS.ekRec_req
        buffer := hS.buffer
        horizon := hS.horizon
        msgs := hS.msgs
        msgs_flag_mono := hS.msgs_flag_mono
        msgs_stale := fun j ρ' t' hj hlt hfl => by
          change ρ'.tReq ∈ (recvAck roleR stR.ack ρ).ctRec
          rw [hct]; exact hS.msgs_stale j ρ' t' hj hlt hfl }

/-! ### The receive step -/

/-- A receive of a recorded peer message succeeds, satisfies the game's assertions, and
preserves the main invariant for both parties with the transcript unchanged. The emitted key,
if any, is the transcript key of the decapsulated epoch; `hdec` is the only place KEM
correctness enters, and it is needed only for the received epoch, and only when that epoch
has not been acknowledged yet. -/
theorem partyInv_recv_step [DecidableEq Sym] (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct)
    (hdec : ρ.tRes ∉ stR.ack.ctRec → ∀ pk sk c k, (T ρ.tRes).keypair = some (pk, sk) →
      (T ρ.tRes).enc = some (c, k) → hDet.decapsDet sk c = some k) :
    (∃ key? trcv stR', recv roleR kem hDet ecEk ecCt stR ρ = some (key?, trcv, stR')) ∧
    ∀ key? trcv stR', recv roleR kem hDet ecEk ecCt stR ρ = some (key?, trcv, stR') →
      trcv = tsnd ∧
      (List.range (max tcurR trcv + 1)).all
        (fun t => t = 0 || (recordKey keyR key? t).isSome) = true ∧
      (∀ tI k, key? = some (tI, k) → keyR tI = none ∧ (keyS tI = none ∨ keyS tI = some k)) ∧
      PartyInv roleR ecEk ecCt T stR' stS msgsR (recordKey keyR key?) keyS (max tcurR trcv) ∧
      PartyInv roleR.peer ecEk ecCt T stS stR' msgsS keyS (recordKey keyR key?) tcurS := by
  have m := recv_msgInv hS hmsg
  have hepoch : tsnd = ρ.sendingEpoch := m.epoch
  -- Reduce the conclusion for a receive without key to the two invariants.
  have finish : ∀ stR' : State PK SK C Sym,
      PartyInv roleR ecEk ecCt T stR' stS msgsR keyR keyS (max tcurR ρ.sendingEpoch) →
      PartyInv roleR.peer ecEk ecCt T stS stR' msgsS keyS keyR tcurS →
      ∀ key? trcv stR'', some (none, ρ.sendingEpoch, stR') = some (key?, trcv, stR'') →
        trcv = tsnd ∧
        (List.range (max tcurR trcv + 1)).all
          (fun t => t = 0 || (recordKey keyR key? t).isSome) = true ∧
        (∀ tI k, key? = some (tI, k) → keyR tI = none ∧ (keyS tI = none ∨ keyS tI = some k)) ∧
        PartyInv roleR ecEk ecCt T stR'' stS msgsR (recordKey keyR key?) keyS (max tcurR trcv) ∧
        PartyInv roleR.peer ecEk ecCt T stS stR'' msgsS keyS (recordKey keyR key?) tcurS := by
    intro stR' hR' hS' key? trcv stR'' h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨hepoch.symm, ?_, by simp, hR', hS'⟩
    simpa using knownPrefix_of_partyInv hR' hS' _ hR'.horizon
  rw [recv_eq_recvSpec]
  unfold recvSpec
  by_cases hst : ρ.tRes < stR.req.reqEpoch
  · simp only [hst, if_true]
    obtain ⟨hR', hS'⟩ := partyInv_recv_stale hR hS hmsg hst
    exact ⟨⟨_, _, _, rfl⟩, finish _ hR' hS'⟩
  · simp only [hst, if_false, recvReq_eq_tRes hR hS hmsg hst]
    by_cases hg1 : (stR.res.ekPeer (ρ.tRes - roleR.offset)).isNone = true ∧ ρ.bit = some 0
    · rw [if_pos hg1]
      obtain ⟨hqnot, pk, sk, i, I, hkp, hch, hbufI, hcard⟩ :=
        recv_buffer_pk hR hS hmsg hst hg1.2 hg1.1
      have hpos := recv_tRes_pos_of_keypair hS hmsg (by rw [hkp]; rfl)
      rw [hch, hbufI]
      simp only [insertChunkAndDecode]
      rw [insert_payloadChunks]
      have hle : (insert (counterIndex ecEk i) I).card ≤ ecEk.ec.nchunk := by
        have := Finset.card_insert_le (counterIndex ecEk i) I
        omega
      set I' := insert (counterIndex ecEk i) I with hI'
      -- the installed key is the transcript's key; the extended map is honest
      have hekT : ∀ e pk', Function.update stR.res.ekPeer (ρ.tRes - roleR.offset) (some pk) e =
          some pk' → ∃ sk', (T e).keypair = some (pk', sk') := by
        intro e pk' h
        by_cases he : e = ρ.tRes - roleR.offset
        · subst he
          rw [Function.update_self, Option.some.injEq] at h
          subst h
          exact ⟨sk, hkp⟩
        · rw [Function.update_of_ne he] at h
          exact hR.ekPeer_T e pk' h
      have hstable : ∀ e, (stR.res.ekPeer e).isSome = true →
          Function.update stR.res.ekPeer (ρ.tRes - roleR.offset) (some pk) e =
            stR.res.ekPeer e := by
        intro e he
        have hne : e ≠ ρ.tRes - roleR.offset := by
          intro h; subst h
          rw [Option.isNone_iff_eq_none] at hg1
          rw [hg1.1] at he; cases he
        exact Function.update_of_ne hne _ _
      obtain ⟨-, hpRes, -, hpResO⟩ := recv_parity_facts hR hS hmsg
      have hekpar : ∀ e, (Function.update stR.res.ekPeer (ρ.tRes - roleR.offset) (some pk) e).isSome
          = true → e % 2 = roleR.resParity ∧ e ≤ ρ.tRes - roleR.offset := by
        intro e he
        by_cases heq : e = ρ.tRes - roleR.offset
        · subst heq; exact ⟨hpResO, le_rfl⟩
        · rw [Function.update_of_ne heq] at he
          refine ⟨hR.ekPeer_parity e he, ?_⟩
          have := hR.ekPeer_le e he
          have := not_lt.mp hst
          omega
      rcases Nat.lt_or_eq_of_le hle with hlt | heq
      · -- below threshold: no decode, the chunk joins the buffer
        rw [decode_payloadChunks_none ecEk hEk pk I' hlt]
        simp only
        have hbuf : BufferConsistent roleR ecEk ecCt T
            (recvFinish roleR stR ρ.tRes stR.res.ekPeer stR.req.dk (payloadChunks ecEk pk I')
              (recvAck roleR stR.ack ρ)) := by
          have hnot : ρ.tRes ∉ (recvAck roleR stR.ack ρ).ctRec := by
            rw [mem_recvAck_ctRec]
            rintro (h | ⟨-, h⟩)
            · exact hqnot h
            · have h2 := recv_tReq_parity hS hmsg
              rw [← h] at h2
              cases roleR <;> simp only [Role.reqParity, Role.resParity] at h2 hpRes <;> omega
          apply bufferConsistent_recvFinish
          rw [if_neg hnot, if_pos hg1.1, hkp]
          exact ⟨I', rfl, hlt⟩
        obtain ⟨hR', hS'⟩ := partyInv_recv_noKey hR hS hmsg hst stR.res.ekPeer
          (recvAck roleR stR.ack ρ) (payloadChunks ecEk pk I') (fun _ _ => rfl) hR.ekPeer_T
          (fun e he => ⟨hR.ekPeer_parity e he, by
            have := hR.ekPeer_le e he; have := not_lt.mp hst; omega⟩) rfl (fun _ h => h)
          (fun t ht hnot => absurd ht hnot) hbuf
        exact ⟨⟨_, _, _, rfl⟩, finish _ hR' hS'⟩
      · -- threshold reached: decode the peer's key and install it
        rw [decode_payloadChunks ecEk hEk pk I' heq.ge]
        simp only
        set ack' : Acknowledgements :=
          { recvAck roleR stR.ack ρ with
            ekRec := insert (ρ.tRes - roleR.offset) (recvAck roleR stR.ack ρ).ekRec } with hack'
        have hbuf : BufferConsistent roleR ecEk ecCt T
            (recvFinish roleR stR ρ.tRes
              (Function.update stR.res.ekPeer (ρ.tRes - roleR.offset) (some pk)) stR.req.dk ∅
              ack') :=
          bufferConsistent_of_empty _ _ _ _ _ rfl
        obtain ⟨hR', hS'⟩ := partyInv_recv_noKey hR hS hmsg hst
          (Function.update stR.res.ekPeer (ρ.tRes - roleR.offset) (some pk)) ack' ∅
          hstable hekT hekpar rfl (Finset.subset_insert _ _)
          (fun t ht hnot => by
            simp only [hack', Finset.mem_insert] at ht
            rcases ht with rfl | ht
            · exact ⟨hpResO, by rw [Function.update_self]; rfl⟩
            · exact absurd ht hnot) hbuf
        exact ⟨⟨_, _, _, rfl⟩, finish _ hR' hS'⟩
    · rw [if_neg hg1]
      by_cases hg2 : ρ.tRes ∉ (recvAck roleR stR.ack ρ).ctRec ∧ ρ.bit = some 1
      · rw [if_pos hg2]
        have hqnot : ρ.tRes ∉ stR.ack.ctRec := fun h => hg2.1 (recvAck_ctRec_subset _ _ _ h)
        have hsome := recv_bit1_ekPeer hR hS hmsg hg2.2
        rcases hch : ρ.ch with _ | ch
        · -- no chunk: nothing decoded, buffer unchanged
          simp only [insertChunkAndDecode]
          obtain ⟨hR', hS'⟩ := partyInv_recv_noKey hR hS hmsg hst stR.res.ekPeer
            (recvAck roleR stR.ack ρ) stR.req.receivedChunks (fun _ _ => rfl) hR.ekPeer_T
            (fun e he => ⟨hR.ekPeer_parity e he, by
              have := hR.ekPeer_le e he; have := not_lt.mp hst; omega⟩) rfl (fun _ h => h)
            (fun t ht hnot => absurd ht hnot) (recv_buffer_unchanged hR hS hmsg hst)
          exact ⟨⟨_, _, _, rfl⟩, finish _ hR' hS'⟩
        · obtain ⟨c, k, i, I, henc, hchi, hbufI, hcard⟩ :=
            recv_buffer_ct hR hS hmsg hst hg2.2 hqnot ch hch
          subst hchi
          rw [hbufI]
          simp only [insertChunkAndDecode]
          rw [insert_payloadChunks]
          have hle : (insert (counterIndex ecCt i) I).card ≤ ecCt.ec.nchunk := by
            have := Finset.card_insert_le (counterIndex ecCt i) I
            omega
          set I' := insert (counterIndex ecCt i) I with hI'
          have hnotnone : ¬ (stR.res.ekPeer (ρ.tRes - roleR.offset)).isNone = true := by
            intro h
            rw [Option.isNone_iff_eq_none] at h
            rw [h] at hsome
            exact absurd hsome (by simp)
          rcases Nat.lt_or_eq_of_le hle with hlt | heq
          · rw [decode_payloadChunks_none ecCt hCt c I' hlt]
            simp only
            have hbuf : BufferConsistent roleR ecEk ecCt T
                (recvFinish roleR stR ρ.tRes stR.res.ekPeer stR.req.dk (payloadChunks ecCt c I')
                  (recvAck roleR stR.ack ρ)) := by
              apply bufferConsistent_recvFinish
              rw [if_neg hg2.1, if_neg hnotnone, henc]
              exact ⟨I', rfl, hlt⟩
            obtain ⟨hR', hS'⟩ := partyInv_recv_noKey hR hS hmsg hst stR.res.ekPeer
              (recvAck roleR stR.ack ρ) (payloadChunks ecCt c I') (fun _ _ => rfl) hR.ekPeer_T
              (fun e he => ⟨hR.ekPeer_parity e he, by
                have := hR.ekPeer_le e he; have := not_lt.mp hst; omega⟩) rfl (fun _ h => h)
              (fun t ht hnot => absurd ht hnot) hbuf
            exact ⟨⟨_, _, _, rfl⟩, finish _ hR' hS'⟩
          · -- threshold reached: decode the ciphertext and decapsulate
            rw [decode_payloadChunks ecCt hCt c I' heq.ge]
            simp only
            have hkpS : (T ρ.tRes).keypair.isSome = true :=
              (T ρ.tRes).enc_keypair (by rw [henc]; rfl)
            obtain ⟨⟨pk, sk⟩, hkp⟩ := Option.isSome_iff_exists.mp hkpS
            have hpar := recv_tRes_parity hS hmsg
            have hpos : 0 < ρ.tRes := hR.keypair_pos _ hpar hkpS
            have hmem : (ρ.tRes, sk) ∈ stR.req.dk := hR.T_dk _ pk sk hkp hpar hqnot
            have hlk : stR.req.dk.lookup ρ.tRes = some sk := by
              cases h : stR.req.dk.lookup ρ.tRes with
              | none =>
                  exfalso
                  have := List.lookup_eq_none_iff.mp h (ρ.tRes, sk) hmem
                  simp at this
              | some sk' =>
                  have hmem' : (ρ.tRes, sk') ∈ stR.req.dk := by
                    obtain ⟨before, after, hlist, _⟩ := List.lookup_eq_some_iff.mp h
                    simp only [hlist, List.mem_append, List.mem_cons, true_or, or_true]
                  obtain ⟨-, -, -, -, pk', hkp'⟩ := hR.dk_T _ sk' hmem'
                  rw [hkp] at hkp'
                  simp only [Option.some.injEq, Prod.mk.injEq] at hkp'
                  rw [hkp'.2]
            rw [hlk]
            simp only [Option.bind_eq_bind, Option.bind, hdec hqnot pk sk c k hkp henc]
            -- the plain post-state, then the decapsulation transition on it
            obtain ⟨hR₁, hS₁⟩ := partyInv_recv_noKey hR hS hmsg hst stR.res.ekPeer
              (recvAck roleR stR.ack ρ) ∅ (fun _ _ => rfl) hR.ekPeer_T
              (fun e he => ⟨hR.ekPeer_parity e he, by
                have := hR.ekPeer_le e he; have := not_lt.mp hst; omega⟩) rfl (fun _ h => h)
              (fun t ht hnot => absurd ht hnot) (bufferConsistent_of_empty _ _ _ _ _ rfl)
            obtain ⟨hR₂, hS₂⟩ := partyInv_decaps_local hS hR₁ hS₁ ρ.tRes rfl hpos hpar hg2.1 c k
              henc rfl
            have hstate :
                recvFinish roleR stR ρ.tRes stR.res.ekPeer
                    (stR.req.dk.filter (fun p => p.1 != ρ.tRes)) ∅
                    { recvAck roleR stR.ack ρ with
                      ctRec := insert ρ.tRes (recvAck roleR stR.ack ρ).ctRec } =
                  { recvFinish roleR stR ρ.tRes stR.res.ekPeer stR.req.dk ∅
                      (recvAck roleR stR.ack ρ) with
                    req := { (recvFinish roleR stR ρ.tRes stR.res.ekPeer stR.req.dk ∅
                      (recvAck roleR stR.ack ρ)).req with
                        dk := stR.req.dk.filter (fun p => p.1 != ρ.tRes) }
                    ack := { recvAck roleR stR.ack ρ with
                      ctRec := insert ρ.tRes (recvAck roleR stR.ack ρ).ctRec } } := by
              have hne : stR.res.resEpoch ≠ ρ.tRes := by
                intro h
                have := hR.res_parity
                rw [h] at this
                cases roleR <;> simp only [Role.reqParity, Role.resParity] at this hpar <;> omega
              simp only [recvFinish, Finset.mem_insert, hne, false_or]
            rw [hstate]
            refine ⟨⟨_, _, _, rfl⟩, ?_⟩
            intro key? trcv stR'' h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            refine ⟨hepoch.symm, ?_, ?_, hR₂, hS₂⟩
            · simpa using knownPrefix_of_partyInv hR₂ hS₂ _ hR₂.horizon
            · intro tI k' h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨?_, Or.inr ?_⟩
              · rw [hR.key_req _ hpos hpar, if_neg hqnot]
              · have hparS : ρ.tRes % 2 = roleR.peer.resParity := by simpa using hpar
                rw [hS.key_res _ hpos hparS, EpochTranscript.key, henc]
                rfl
      · rw [if_neg hg2]
        obtain ⟨hR', hS'⟩ := partyInv_recv_noKey hR hS hmsg hst stR.res.ekPeer
          (recvAck roleR stR.ack ρ) stR.req.receivedChunks (fun _ _ => rfl) hR.ekPeer_T
          (fun e he => ⟨hR.ekPeer_parity e he, by
            have := hR.ekPeer_le e he; have := not_lt.mp hst; omega⟩) rfl (fun _ h => h)
          (fun t ht hnot => absurd ht hnot) (recv_buffer_unchanged hR hS hmsg hst)
        exact ⟨⟨_, _, _, rfl⟩, finish _ hR' hS'⟩

end Receive

end oppBiKemCKA
