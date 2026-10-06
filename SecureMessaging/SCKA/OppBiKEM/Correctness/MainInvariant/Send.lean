/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Gavran, Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Correctness.MainInvariant
import SecureMessaging.SCKA.OppBiKEM.Correctness.PhaseCausality

/-!
# Opp-BiKEM main invariant — the send step

A supported send by one party preserves `PartyInv` for both parties, for a transcript
updated in at most one epoch: the fresh key pair when the responder epoch advances, or the
fresh encapsulation when a key is emitted. The two cannot happen in one send, because a
freshly generated key is not yet acknowledged. The send step also discharges the game's
send-side assertions: monotonicity of the sending epoch, the known-prefix check, and
uniqueness and consistency of an emitted key.
-/

open OracleComp KEMScheme ErasureCodePayload

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-! ### Parity helpers -/

/-- The two parities of a role differ. -/
theorem Role.reqParity_ne_resParity (role : Role) : role.reqParity ≠ role.resParity := by
  cases role <;> decide

/-- Shifting by the role's offset exchanges the two parities. -/
theorem Role.offset_parity (role : Role) (e : ℤ) :
    (e + role.offset) % 2 = role.reqParity ↔ e % 2 = role.resParity := by
  cases role <;> simp only [Role.offset, Role.reqParity, Role.resParity] <;> omega

/-- An epoch has the requester parity iff it does not have the responder parity. -/
theorem Role.reqParity_iff_not_resParity (role : Role) (e : ℤ) :
    e % 2 = role.reqParity ↔ e % 2 ≠ role.resParity := by
  cases role <;> simp only [Role.reqParity, Role.resParity] <;> omega

/-! ### The advance gate of `sendWith` -/

/-- Advancing the responder epoch in a supported send requires both adjacent ciphertext
acknowledgements (the gate of `sendWith`). Local copy of `send_advance_guard`
(`Lockstep.lean`), whose module cannot be imported here because its `GameInv` clashes with
the main invariant's. -/
private theorem send_advance_gate (role : Role) (kem : KEMScheme ProbComp K PK SK C)
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

/-! ### Transcript updates -/

namespace EpochTranscript

variable {kem : KEMScheme ProbComp K PK SK C}

/-- An epoch without a key pair has no encapsulation. -/
theorem enc_eq_none_of_keypair_eq_none (tr : EpochTranscript kem) (h : tr.keypair = none) :
    tr.enc = none := by
  cases henc : tr.enc with
  | none => rfl
  | some ck =>
    have := tr.enc_keypair (by rw [henc]; rfl)
    rw [h] at this
    cases this

/-- An epoch without a key pair has no key. -/
theorem key_eq_none_of_keypair_eq_none (tr : EpochTranscript kem) (h : tr.keypair = none) :
    tr.key = none := by
  rw [key, enc_eq_none_of_keypair_eq_none tr h]
  rfl

@[simp] theorem key_ofKeypair (pk : PK) (sk : SK) (hmem : (pk, sk) ∈ support kem.keygen) :
    (ofKeypair pk sk hmem : EpochTranscript kem).key = none := rfl

@[simp] theorem key_setEnc (tr : EpochTranscript kem) (pk sk c k hkp hmem) :
    (tr.setEnc pk sk c k hkp hmem).key = some k := rfl

end EpochTranscript

/-- The honest chunk set at no positions is empty. -/
theorem payloadChunks_empty {M : Type} (ecp : ErasureCodePayload M Sym)
    (payload : M) : payloadChunks ecp payload ∅ = ∅ := by
  simp [payloadChunks, ErasureCode.encodeChunks]

/-! ### Transfer of message honesty -/

/-- Honesty of a recorded message transfers to a later state of the same party, with the
same acknowledgements and requester epoch, and to a transcript agreeing on the slots the
message references. -/
theorem MessageInv.transfer {role : Role} {kem : KEMScheme ProbComp K PK SK C}
    {ecEk : ErasureCodePayload PK Sym} {ecCt : ErasureCodePayload C Sym}
    {T T' : Transcript kem} {st st' : State PK SK C Sym} {ρ : Message Sym} {tsnd : ℕ}
    (h : MessageInv role ecEk ecCt T st ρ tsnd)
    (hres : st.res.resEpoch ≤ st'.res.resEpoch) (hreq : st'.req.reqEpoch = st.req.reqEpoch)
    (hack : st'.ack = st.ack)
    (hkp : ∀ e, e ≤ st.res.resEpoch + role.offset → e % 2 = role.reqParity →
      (T' e).keypair = (T e).keypair)
    (henc : ∀ e, (T e).enc.isSome = true → (T' e).enc = (T e).enc) :
    MessageInv role ecEk ecCt T' st' ρ tsnd where
  epoch := h.epoch
  res_parity := h.res_parity
  req_parity := h.req_parity
  res_le := h.res_le.trans hres
  req_le := by rw [hreq]; exact h.req_le
  res_lower := h.res_lower
  req_lower := h.req_lower
  pk_chunk := by
    intro hbit
    obtain ⟨pk, sk, i, hT, hch⟩ := h.pk_chunk hbit
    refine ⟨pk, sk, i, ?_, hch⟩
    have hle := h.res_le
    rw [hkp _ (by omega) ((Role.offset_parity role _).2 h.res_parity)]
    exact hT
  ct_chunk := by
    intro hbit ch hch
    obtain ⟨c, k, i, hT, hc⟩ := h.ct_chunk hbit ch hch
    refine ⟨c, k, i, ?_, hc⟩
    rw [henc _ (by rw [hT]; rfl)]
    exact hT
  no_chunk := h.no_chunk
  ct_flag := by rw [hack]; exact h.ct_flag
  ek_flag := by rw [hack]; exact h.ek_flag
  bit1_acked := by rw [hack]; exact h.bit1_acked
  horizon_mem := by rw [hack]; exact h.horizon_mem
  horizon_req := h.horizon_req

/-! ### The peer after a send -/

/-- The peer's invariant after a send by `roleS`. The sender's requester epoch, peer keys and
acknowledgements are unchanged and its responder epoch does not decrease; the new transcript
agrees with the old one on every slot the peer's invariant reads. -/
theorem partyInv_peer_of_send (roleS : Role) {kem : KEMScheme ProbComp K PK SK C}
    {ecEk : ErasureCodePayload PK Sym} {ecCt : ErasureCodePayload C Sym}
    {T T' : Transcript kem} {stS stS' stR : State PK SK C Sym}
    {msgsS msgsR : ℕ → Option (Message Sym × ℕ)} {keyR keyS keyS' : ℕ → Option K}
    {tcurR tcurS : ℕ}
    (hS : PartyInv roleS ecEk ecCt T stS stR msgsS keyS keyR tcurS)
    (hR : PartyInv roleS.peer ecEk ecCt T stR stS msgsR keyR keyS tcurR)
    (hreq : stS'.req.reqEpoch = stS.req.reqEpoch) (hekPeer : stS'.res.ekPeer = stS.res.ekPeer)
    (hack : stS'.ack = stS.ack)
    (k1 : ∀ e, e % 2 = roleS.resParity → (T' e).keypair = (T e).keypair)
    (k2 : ∀ e pk sk, (T e).keypair = some (pk, sk) → (T' e).keypair = some (pk, sk))
    (k3 : ∀ e, e % 2 = roleS.reqParity → (T' e).key = (T e).key)
    (k4 : ∀ e, e % 2 = roleS.reqParity → e ≤ stS.res.resEpoch + roleS.offset →
      (T' e).keypair = (T e).keypair)
    (e1 : ∀ e, e % 2 = roleS.reqParity → (T' e).enc = (T e).enc)
    (e2 : ∀ e, (T e).enc.isSome = true → (T' e).enc = (T e).enc) :
    PartyInv roleS.peer ecEk ecCt T' stR stS' msgsR keyR keyS' tcurR where
  res_parity := hR.res_parity
  req_parity := hR.req_parity
  res_lower := hR.res_lower
  req_lower := hR.req_lower
  init_acks := hR.init_acks
  res_le_peer_req := by rw [hreq]; exact hR.res_le_peer_req
  peer_req_le_res := by rw [hreq]; exact hR.peer_req_le_res
  keypair_pos := by
    intro e hp hs
    rw [k1 e (by simpa using hp)] at hs
    exact hR.keypair_pos e hp hs
  keypair_future := by
    intro e hp hlt
    rw [k1 e (by simpa using hp)]
    exact hR.keypair_future e hp hlt
  ek_T := by
    intro pk hpk
    rw [k1 _ (by
      have := (Role.offset_parity roleS.peer stR.res.resEpoch).2 hR.res_parity
      simpa using this)]
    exact hR.ek_T pk hpk
  dk_T := by
    intro e sk hmem
    obtain ⟨hp, hpos, hle, hkey, pk, hT⟩ := hR.dk_T e sk hmem
    exact ⟨hp, hpos, hle, hkey, pk, by rw [k1 e (by simpa using hp)]; exact hT⟩
  T_dk := by
    intro e pk sk hT hp hnot
    rw [k1 e (by simpa using hp)] at hT
    exact hR.T_dk e pk sk hT hp hnot
  dk_shape := hR.dk_shape
  ek_acked := by
    intro h
    rw [k1 _ (by
      have := (Role.offset_parity roleS.peer stR.res.resEpoch).2 hR.res_parity
      simpa using this)]
    exact hR.ek_acked h
  keypair_current := by
    intro h
    rw [k1 _ (by
      have := (Role.offset_parity roleS.peer stR.res.resEpoch).2 hR.res_parity
      simpa using this)]
    exact hR.keypair_current h
  enc_future := by
    intro e hp hlt
    rw [e1 e (by simpa using hp)]
    exact hR.enc_future e hp hlt
  enc_current := by
    intro c k hT
    rw [e1 _ (by simpa using hR.res_parity)] at hT
    exact hR.enc_current c k hT
  ct_T := by
    intro c hc
    obtain ⟨k, hT⟩ := hR.ct_T c hc
    exact ⟨k, by rw [e1 _ (by simpa using hR.res_parity)]; exact hT⟩
  ct_acked := hR.ct_acked
  enc_ekRec := by
    intro e hp hs
    rw [e1 e (by simpa using hp)] at hs
    exact hR.enc_ekRec e hp hs
  ekPeer_T := by
    intro e pk hpk
    obtain ⟨sk, hT⟩ := hR.ekPeer_T e pk hpk
    exact ⟨sk, k2 e pk sk hT⟩
  ekPeer_parity := hR.ekPeer_parity
  ekPeer_le := hR.ekPeer_le
  key_zero := hR.key_zero
  key_res := by
    intro e hpos hp
    rw [k3 e (by simpa using hp)]
    exact hR.key_res e hpos hp
  key_req := by
    intro e hpos hp
    have h := hR.key_req e hpos hp
    by_cases hmem : e ∈ stR.ack.ctRec
    · rw [if_pos hmem] at h ⊢
      rw [h]
      unfold EpochTranscript.key
      rw [e2 e (hR.ctRec_req_enc e hmem hpos hp)]
    · rw [if_neg hmem] at h ⊢
      exact h
  ctRec_req_enc := by
    intro t ht hpos hp
    rw [e2 t (hR.ctRec_req_enc t ht hpos hp)]
    exact hR.ctRec_req_enc t ht hpos hp
  ctRec_req_le := hR.ctRec_req_le
  ctRec_res_peer := by rw [hack]; exact hR.ctRec_res_peer
  ctRec_res_le := hR.ctRec_res_le
  ctRec_req_closed := hR.ctRec_req_closed
  ctRec_res_closed := hR.ctRec_res_closed
  ekRec_res := hR.ekRec_res
  ekRec_req := by rw [hekPeer]; exact hR.ekRec_req
  buffer := by
    have hb := hR.buffer
    unfold BufferConsistent at hb ⊢
    have hkp : (T' (stR.req.reqEpoch - roleS.peer.offset)).keypair =
        (T (stR.req.reqEpoch - roleS.peer.offset)).keypair := by
      apply k4
      · have hpar := hR.req_parity
        have := (Role.offset_parity roleS stR.req.reqEpoch).2 (by simpa using hpar)
        rw [Role.peer_offset]
        simpa [sub_neg_eq_add] using this
      · have := hS.peer_req_le_res
        rw [Role.peer_offset]
        omega
    rw [hkp]
    by_cases hmem : stR.req.reqEpoch ∈ stR.ack.ctRec
    · rw [if_pos hmem] at hb ⊢
      exact hb
    · rw [if_neg hmem] at hb ⊢
      by_cases hnone : (stR.res.ekPeer (stR.req.reqEpoch - roleS.peer.offset)).isNone = true
      · rw [if_pos hnone] at hb ⊢
        exact hb
      · rw [if_neg hnone] at hb ⊢
        cases henc : (T stR.req.reqEpoch).enc with
        | none =>
          simp only [henc] at hb
          cases henc' : (T' stR.req.reqEpoch).enc with
          | none => exact hb
          | some ck =>
            obtain ⟨c, k⟩ := ck
            refine ⟨∅, ?_, ?_⟩
            · rw [hb, payloadChunks_empty]
            · simpa using ecCt.ec.nchunk_pos
        | some ck =>
          rw [e2 _ (by rw [henc]; rfl), henc]
          simpa only [henc] using hb
  horizon := hR.horizon
  msgs := by
    intro n ρ tsnd hmsg
    refine (hR.msgs n ρ tsnd hmsg).transfer le_rfl rfl rfl ?_ e2
    intro e _ hp
    exact k1 e (by simpa using hp)
  msgs_flag_mono := hR.msgs_flag_mono
  msgs_stale := by
    intro n ρ tsnd hmsg hlt hflag
    rw [hreq] at hlt
    rw [hack]
    exact hR.msgs_stale n ρ tsnd hmsg hlt hflag

/-! ### The message emitted by a send -/

/-- Honesty of the message emitted by a supported send, given the sender's post-state
public-key and ciphertext transcript links. -/
theorem MessageInv.of_send (roleS : Role) {kem : KEMScheme ProbComp K PK SK C}
    {ecEk : ErasureCodePayload PK Sym} {ecCt : ErasureCodePayload C Sym}
    {T T' : Transcript kem} {stS stS' stR : State PK SK C Sym}
    {msgsS : ℕ → Option (Message Sym × ℕ)} {keyS keyR : ℕ → Option K} {tcurS : ℕ}
    (hS : PartyInv roleS ecEk ecCt T stS stR msgsS keyS keyR tcurS)
    {key? : Option (ℕ × K)} {ρ : Message Sym} {tsnd : ℕ}
    (hout : some (key?, ρ, tsnd, stS') ∈ support (send roleS kem ecEk ecCt stS))
    (hres_par : stS'.res.resEpoch % 2 = roleS.resParity) (hres_lower : -1 ≤ stS'.res.resEpoch)
    (hek : ∀ pk, stS'.req.ek = some pk →
      ∃ sk, (T' (stS'.res.resEpoch + roleS.offset)).keypair = some (pk, sk))
    (hct : ∀ c, stS'.res.ct = some c → ∃ k, (T' stS'.res.resEpoch).enc = some (c, k)) :
    MessageInv roleS ecEk ecCt T' stS' ρ tsnd := by
  have hp := send_provenance roleS kem ecEk ecCt stS key? ρ tsnd stS' hout
  have hhor : (ρ.sendingEpoch : ℤ) = stS.ack.sendingHorizon := by
    rw [← hp.message_sendingEpoch, hp.sending_horizon]
  exact {
    epoch := hp.message_sendingEpoch
    res_parity := by rw [hp.message_resEpoch]; exact hres_par
    req_parity := by rw [hp.message_reqEpoch]; exact hS.req_parity
    res_le := by rw [hp.message_resEpoch]
    req_le := by rw [hp.message_reqEpoch, hp.requester_epoch]
    res_lower := by rw [hp.message_resEpoch]; exact hres_lower
    req_lower := by rw [hp.message_reqEpoch]; exact hS.req_lower
    pk_chunk := by
      intro hbit
      obtain ⟨pk, hek', hch⟩ := hp.public_key_chunk hbit
      obtain ⟨sk, hT⟩ := hek pk hek'
      exact ⟨pk, sk, stS'.res.ich, by rw [hp.message_resEpoch]; exact hT, hch⟩
    ct_chunk := by
      intro hbit ch hch
      rw [hp.ciphertext_chunk hbit, Option.map_eq_some_iff] at hch
      obtain ⟨c, hc, hch⟩ := hch
      obtain ⟨k, hT⟩ := hct c hc
      exact ⟨c, k, stS'.res.ich, by rw [hp.message_resEpoch]; exact hT, hch.symm⟩
    no_chunk := hp.absent_payload
    ct_flag := by
      intro hflag
      have h := hp.advertised_acknowledgements.2
      rw [hflag] at h
      rw [hp.message_reqEpoch, hp.acknowledgements]
      exact of_decide_eq_true h.symm
    ek_flag := by
      intro hflag
      have h := hp.advertised_acknowledgements.1
      rw [hflag] at h
      rw [hp.message_reqEpoch, hp.acknowledgements]
      exact of_decide_eq_true h.symm
    bit1_acked := by
      intro hbit
      rw [hp.acknowledgements]
      exact send_ciphertextMessage_keyAck roleS kem ecEk ecCt stS key? ρ tsnd stS' hout hbit
    horizon_mem := by
      intro s hs hle
      rw [hp.acknowledgements]
      exact hS.horizon_prefix s hs (by rw [← hhor]; exact hle)
    horizon_req := by
      intro s hs hle hpar
      have hmem := hS.horizon_prefix s hs (by rw [← hhor]; exact hle)
      have hsle := hS.ctRec_req_le s hmem hpar
      rw [hp.message_reqEpoch]
      refine ⟨hsle, fun heq => ?_⟩
      rw [hp.advertised_acknowledgements.2]
      exact decide_eq_true (heq ▸ hmem) }

/-! ### The sender after a send -/

/-- The sender's invariant after a supported send, given the transcript-dependent fields that
differ between the three kinds of send (plain, advance, encapsulation) and the way the new
transcript and key table relate to the old ones. -/
theorem partyInv_sender_of_send (roleS : Role) {kem : KEMScheme ProbComp K PK SK C}
    {ecEk : ErasureCodePayload PK Sym} {ecCt : ErasureCodePayload C Sym}
    {T T' : Transcript kem} {stS stS' stR : State PK SK C Sym}
    {msgsS msgsR : ℕ → Option (Message Sym × ℕ)} {keyS keyS' keyR : ℕ → Option K}
    {tcurS tcurR : ℕ}
    (hS : PartyInv roleS ecEk ecCt T stS stR msgsS keyS keyR tcurS)
    (hR : PartyInv roleS.peer ecEk ecCt T stR stS msgsR keyR keyS tcurR)
    (n : ℕ) {key? : Option (ℕ × K)} {ρ : Message Sym} {tsnd : ℕ}
    (hout : some (key?, ρ, tsnd, stS') ∈ support (send roleS kem ecEk ecCt stS))
    -- how the new transcript relates to the old one
    (hkp2 : ∀ e, e % 2 = roleS.reqParity → (T' e).keypair.isSome = true →
      (T e).keypair.isSome = true ∨
        (e = stS'.res.resEpoch + roleS.offset ∧ stS'.res.resEpoch = stS.res.resEpoch + 2))
    (hkpLe : ∀ e, e ≤ stS.res.resEpoch + roleS.offset → e % 2 = roleS.reqParity →
      (T' e).keypair = (T e).keypair)
    (hkpRes : ∀ e, e % 2 = roleS.resParity → (T' e).keypair = (T e).keypair)
    (hencNe : ∀ e, e ≠ stS'.res.resEpoch → (T' e).enc = (T e).enc)
    (hencReq : ∀ e, e % 2 = roleS.reqParity → (T' e).enc = (T e).enc)
    (hencMono : ∀ e, (T e).enc.isSome = true → (T' e).enc = (T e).enc)
    (hkeyNe : ∀ i, i ≠ stS'.res.resEpoch.toNat → keyS' i = keyS i)
    -- the fields that depend on the kind of send
    (f_ek_T : ∀ pk, stS'.req.ek = some pk →
      ∃ sk, (T' (stS'.res.resEpoch + roleS.offset)).keypair = some (pk, sk))
    (f_dk_T : ∀ e sk, (e, sk) ∈ stS'.req.dk →
      e % 2 = roleS.reqParity ∧ 0 < e ∧ e ≤ stS'.res.resEpoch + roleS.offset ∧
        keyS' e.toNat = none ∧ ∃ pk, (T' e).keypair = some (pk, sk))
    (f_T_dk : ∀ e pk sk, (T' e).keypair = some (pk, sk) → e % 2 = roleS.reqParity →
      e ∉ stS'.ack.ctRec → (e, sk) ∈ stS'.req.dk)
    (f_dk_shape : stS'.req.dk = [] ∨
      ∃ sk, stS'.req.dk = [(stS'.res.resEpoch + roleS.offset, sk)])
    (f_ek_acked : stS'.req.ek = none →
      (T' (stS'.res.resEpoch + roleS.offset)).keypair = none ∨
        stS'.res.resEpoch + roleS.offset ∈ stS'.ack.ekRec)
    (f_keypair_current : 0 < stS'.res.resEpoch + roleS.offset →
      (T' (stS'.res.resEpoch + roleS.offset)).keypair.isSome = true)
    (f_enc_current : ∀ c k, (T' stS'.res.resEpoch).enc = some (c, k) →
      stS'.res.ct = some c ∨ stS'.res.resEpoch ∈ stS'.ack.ctRec)
    (f_ct_T : ∀ c, stS'.res.ct = some c → ∃ k, (T' stS'.res.resEpoch).enc = some (c, k))
    (f_ct_acked : stS'.res.resEpoch ∈ stS'.ack.ctRec → stS'.res.ct = none)
    (f_enc_ekRec_cur : (T' stS'.res.resEpoch).enc.isSome = true →
      stS'.res.resEpoch + roleS.offset ∈ stS'.ack.ekRec)
    (f_key_cur : keyS' stS'.res.resEpoch.toNat = (T' stS'.res.resEpoch).key)
    (f_key_zero : keyS' 0 = none) :
    PartyInv roleS ecEk ecCt T' stS' stR (Function.update msgsS n (some (ρ, tsnd)))
      keyS' keyR tsnd := by
  have hp := send_provenance roleS kem ecEk ecCt stS key? ρ tsnd stS' hout
  obtain ⟨hack, htsnd, hres_or, -, -⟩ :=
    send_support_facts roleS kem ecEk ecCt stS key? ρ tsnd stS' hout
  have hres_le : stS.res.resEpoch ≤ stS'.res.resEpoch := by rcases hres_or with h | h <;> omega
  have hres_par : stS'.res.resEpoch % 2 = roleS.resParity := by
    have := hS.res_parity
    rcases hres_or with h | h <;> omega
  have hgate : stS'.res.resEpoch = stS.res.resEpoch + 2 →
      stS.res.resEpoch ∈ stS.ack.ctRec ∧ stS.res.resEpoch + roleS.offset ∈ stS.ack.ctRec :=
    fun h => send_advance_gate roleS kem ecEk ecCt stS key? ρ tsnd stS' hout (by omega)
  have hkeyT' : ∀ e, e ≠ stS'.res.resEpoch → (T' e).key = (T e).key := by
    intro e he
    unfold EpochTranscript.key
    rw [hencNe e he]
  have hres_lower : -1 ≤ stS'.res.resEpoch := hS.res_lower.trans hres_le
  have hnewMsg : MessageInv roleS ecEk ecCt T' stS' ρ tsnd :=
    MessageInv.of_send roleS hS hout hres_par hres_lower f_ek_T f_ct_T
  exact {
    res_parity := hres_par
    req_parity := by rw [hp.requester_epoch]; exact hS.req_parity
    res_lower := hres_lower
    req_lower := by rw [hp.requester_epoch]; exact hS.req_lower
    init_acks := by rw [hack]; exact hS.init_acks
    res_le_peer_req := by
      rcases hres_or with h | h
      · rw [h]; exact hS.res_le_peer_req
      · have hg := (hgate h).1
        have hmem := hS.ctRec_res_peer _ hg hS.res_parity
        have hle := hR.ctRec_req_le _ hmem (by simpa using hS.res_parity)
        omega
    peer_req_le_res := hS.peer_req_le_res.trans hres_le
    keypair_pos := by
      intro e hpe hs
      rcases hkp2 e hpe hs with h | ⟨rfl, hadv⟩
      · exact hS.keypair_pos e hpe h
      · have h1 := hS.res_lower
        have h2 := hS.res_parity
        cases roleS <;> simp only [Role.offset, Role.resParity] at h2 ⊢ <;> omega
    keypair_future := by
      intro e hpe hlt
      by_contra hne
      have hs : (T' e).keypair.isSome = true := Option.isSome_iff_ne_none.mpr hne
      rcases hkp2 e hpe hs with h | ⟨rfl, -⟩
      · have := hS.keypair_future e hpe (by omega)
        rw [this] at h
        cases h
      · omega
    ek_T := f_ek_T
    dk_T := f_dk_T
    T_dk := f_T_dk
    dk_shape := f_dk_shape
    ek_acked := f_ek_acked
    keypair_current := f_keypair_current
    enc_future := by
      intro e hpe hlt
      rw [hencNe e (by omega)]
      exact hS.enc_future e hpe (by omega)
    enc_current := f_enc_current
    ct_T := f_ct_T
    ct_acked := f_ct_acked
    enc_ekRec := by
      intro e hpe hs
      by_cases he : e = stS'.res.resEpoch
      · subst he
        exact f_enc_ekRec_cur hs
      · rw [hencNe e he] at hs
        rw [hack]
        exact hS.enc_ekRec e hpe hs
    ekPeer_T := by
      intro e pk hpk
      rw [hp.peer_keys] at hpk
      obtain ⟨sk, hT⟩ := hS.ekPeer_T e pk hpk
      refine ⟨sk, ?_⟩
      rw [hkpRes e (hS.ekPeer_parity e (by rw [hpk]; rfl))]
      exact hT
    ekPeer_parity := by rw [hp.peer_keys]; exact hS.ekPeer_parity
    ekPeer_le := by rw [hp.peer_keys, hp.requester_epoch]; exact hS.ekPeer_le
    key_zero := f_key_zero
    key_res := by
      intro e hpos hpe
      by_cases he : e = stS'.res.resEpoch
      · subst he
        exact f_key_cur
      · rw [hkeyNe _ (by omega), hkeyT' e he]
        exact hS.key_res e hpos hpe
    key_req := by
      intro e hpos hpe
      have hne : e ≠ stS'.res.resEpoch := by
        intro h
        exact Role.reqParity_ne_resParity roleS (hpe.symm.trans (h ▸ hres_par))
      rw [hack, hkeyNe _ (by omega), hkeyT' e hne]
      exact hS.key_req e hpos hpe
    ctRec_req_enc := by
      intro t ht hpos hpt
      rw [hack] at ht
      have h := hS.ctRec_req_enc t ht hpos hpt
      rw [hencMono t h]
      exact h
    ctRec_req_le := by rw [hack, hp.requester_epoch]; exact hS.ctRec_req_le
    ctRec_res_peer := by rw [hack]; exact hS.ctRec_res_peer
    ctRec_res_le := by
      intro t ht hpt
      rw [hack] at ht
      exact (hS.ctRec_res_le t ht hpt).trans hres_le
    ctRec_req_closed := by rw [hack, hp.requester_epoch]; exact hS.ctRec_req_closed
    ctRec_res_closed := by
      intro t hpos hpt hlt
      rw [hack]
      rcases hres_or with h | h
      · rw [h] at hlt
        exact hS.ctRec_res_closed t hpos hpt hlt
      · by_cases ht : t = stS.res.resEpoch
        · subst ht
          exact (hgate h).1
        · have := hS.res_parity
          exact hS.ctRec_res_closed t hpos hpt (by omega)
    ekRec_res := by rw [hack, hp.peer_keys]; exact hS.ekRec_res
    ekRec_req := by rw [hack]; exact hS.ekRec_req
    buffer := by
      have hb := hS.buffer
      unfold BufferConsistent at hb ⊢
      have hpar : (stS.req.reqEpoch - roleS.offset) % 2 = roleS.resParity := by
        rw [← Role.offset_parity roleS]
        simpa using hS.req_parity
      rw [hp.requester_epoch, hack, hp.peer_keys, hp.received_chunks,
        hkpRes _ hpar, hencReq _ hS.req_parity]
      exact hb
    horizon := by rw [hack]; exact le_of_eq htsnd
    msgs := by
      intro n' ρ' tsnd' h
      by_cases hn : n' = n
      · subst hn
        rw [Function.update_self, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hnewMsg
      · rw [Function.update_of_ne hn] at h
        exact (hS.msgs n' ρ' tsnd' h).transfer hres_le hp.requester_epoch hack hkpLe hencMono
    msgs_flag_mono := by
      intro n₁ n₂ ρ₁ ρ₂ t₁ t₂ h₁ h₂ hlt hflag
      by_cases hn₁ : n₁ = n <;> by_cases hn₂ : n₂ = n
      · subst hn₁ hn₂
        rw [Function.update_self, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
        obtain ⟨rfl, rfl⟩ := h₁
        obtain ⟨rfl, rfl⟩ := h₂
        exact absurd hlt (lt_irrefl _)
      · subst hn₁
        rw [Function.update_self, Option.some.injEq, Prod.mk.injEq] at h₁
        obtain ⟨rfl, rfl⟩ := h₁
        rw [Function.update_of_ne hn₂] at h₂
        have hold := hS.msgs n₂ ρ₂ t₂ h₂
        have := hold.res_le
        rw [hp.message_resEpoch] at hlt
        omega
      · subst hn₂
        rw [Function.update_self, Option.some.injEq, Prod.mk.injEq] at h₂
        obtain ⟨rfl, rfl⟩ := h₂
        rw [Function.update_of_ne hn₁] at h₁
        have hold := hS.msgs n₁ ρ₁ t₁ h₁
        refine ⟨by rw [hp.message_reqEpoch]; exact hold.req_le, ?_⟩
        intro heq
        rw [hp.advertised_acknowledgements.2]
        apply decide_eq_true
        rw [← hp.message_reqEpoch, ← heq]
        exact hold.ct_flag hflag
      · rw [Function.update_of_ne hn₁] at h₁
        rw [Function.update_of_ne hn₂] at h₂
        exact hS.msgs_flag_mono n₁ n₂ ρ₁ ρ₂ t₁ t₂ h₁ h₂ hlt hflag
    msgs_stale := by
      intro n' ρ' t' h hlt hflag
      by_cases hn : n' = n
      · subst hn
        rw [Function.update_self, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have := hS.peer_req_le_res
        rw [hp.message_resEpoch] at hlt
        omega
      · rw [Function.update_of_ne hn] at h
        exact hS.msgs_stale n' ρ' t' h hlt hflag }

/-! ### The three kinds of send -/

/-- The sender's key table at its current responder epoch is the transcript key. -/
private theorem key_res_current {roleS : Role} {kem : KEMScheme ProbComp K PK SK C}
    {ecEk : ErasureCodePayload PK Sym} {ecCt : ErasureCodePayload C Sym}
    {T : Transcript kem} {stS stR : State PK SK C Sym}
    {msgsS msgsR : ℕ → Option (Message Sym × ℕ)} {keyS keyR : ℕ → Option K} {tcurS tcurR : ℕ}
    (hS : PartyInv roleS ecEk ecCt T stS stR msgsS keyS keyR tcurS)
    (hR : PartyInv roleS.peer ecEk ecCt T stR stS msgsR keyR keyS tcurR) :
    keyS stS.res.resEpoch.toNat = (T stS.res.resEpoch).key := by
  by_cases hpos : 0 < stS.res.resEpoch
  · exact hS.key_res _ hpos hS.res_parity
  · have hzero : stS.res.resEpoch.toNat = 0 := by omega
    rw [hzero, hS.key_zero]
    symm
    apply EpochTranscript.key_eq_none_of_keypair_eq_none
    by_contra hne
    have := hR.keypair_pos _ (by simpa using hS.res_parity) (Option.isSome_iff_ne_none.mpr hne)
    omega

/-- A plain send: neither an epoch advance nor an emitted key; the transcript is unchanged. -/
private theorem send_step_plain (roleS : Role) {kem : KEMScheme ProbComp K PK SK C}
    {ecEk : ErasureCodePayload PK Sym} {ecCt : ErasureCodePayload C Sym}
    {T : Transcript kem} {stS stS' stR : State PK SK C Sym}
    {msgsS msgsR : ℕ → Option (Message Sym × ℕ)} {keyS keyR : ℕ → Option K} {tcurS tcurR : ℕ}
    (hS : PartyInv roleS ecEk ecCt T stS stR msgsS keyS keyR tcurS)
    (hR : PartyInv roleS.peer ecEk ecCt T stR stS msgsR keyR keyS tcurR)
    (n : ℕ) {ρ : Message Sym} {tsnd : ℕ}
    (hout : some (none, ρ, tsnd, stS') ∈ support (send roleS kem ecEk ecCt stS))
    (hres : stS'.res.resEpoch = stS.res.resEpoch) (hdk : stS'.req.dk = stS.req.dk)
    (hek : stS'.req.ek = stS.req.ek) :
    PartyInv roleS ecEk ecCt T stS' stR (Function.update msgsS n (some (ρ, tsnd)))
        keyS keyR tsnd ∧
      PartyInv roleS.peer ecEk ecCt T stR stS' msgsR keyR keyS tcurR := by
  have hp := send_provenance roleS kem ecEk ecCt stS none ρ tsnd stS' hout
  have hct : stS'.res.ct = stS.res.ct := hp.no_key_ciphertext rfl
  refine ⟨partyInv_sender_of_send roleS hS hR n hout (fun _ _ hs => Or.inl hs)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) ?_ ?_ ?_ ?_ ?_ (by rw [hres]; exact hS.keypair_current) ?_ ?_ ?_ ?_ ?_
    hS.key_zero,
    partyInv_peer_of_send roleS hS hR hp.requester_epoch hp.peer_keys hp.acknowledgements
      (fun _ _ => rfl) (fun _ _ _ h => h) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl)⟩
  · intro pk h
    rw [hek] at h
    rw [hres]
    exact hS.ek_T pk h
  · intro e sk h
    rw [hdk] at h
    rw [hres]
    exact hS.dk_T e sk h
  · intro e pk sk hT hpe hnot
    rw [hp.acknowledgements] at hnot
    rw [hdk]
    exact hS.T_dk e pk sk hT hpe hnot
  · rw [hdk, hres]
    exact hS.dk_shape
  · intro h
    rw [hek] at h
    rw [hres, hp.acknowledgements]
    exact hS.ek_acked h
  · rw [hres, hct, hp.acknowledgements]
    exact hS.enc_current
  · rw [hct, hres]
    exact hS.ct_T
  · rw [hres, hp.acknowledgements, hct]
    exact hS.ct_acked
  · rw [hres, hp.acknowledgements]
    exact hS.enc_ekRec _ hS.res_parity
  · rw [hres]
    exact key_res_current hS hR

/-- An advancing send: a fresh key pair is generated for the next exchange and no key is
emitted; the transcript gains the key pair at the new key epoch. -/
private theorem send_step_advance (roleS : Role) {kem : KEMScheme ProbComp K PK SK C}
    {ecEk : ErasureCodePayload PK Sym} {ecCt : ErasureCodePayload C Sym}
    {T : Transcript kem} {stS stS' stR : State PK SK C Sym}
    {msgsS msgsR : ℕ → Option (Message Sym × ℕ)} {keyS keyR : ℕ → Option K} {tcurS tcurR : ℕ}
    (hS : PartyInv roleS ecEk ecCt T stS stR msgsS keyS keyR tcurS)
    (hR : PartyInv roleS.peer ecEk ecCt T stR stS msgsR keyR keyS tcurR)
    (n : ℕ) {ρ : Message Sym} {tsnd : ℕ}
    (hout : some (none, ρ, tsnd, stS') ∈ support (send roleS kem ecEk ecCt stS))
    (pk₀ : PK) (sk₀ : SK) (hmem : (pk₀, sk₀) ∈ support kem.keygen)
    (hres : stS'.res.resEpoch = stS.res.resEpoch + 2) (hek : stS'.req.ek = some pk₀)
    (hdk : stS'.req.dk = (stS'.res.resEpoch + roleS.offset, sk₀) ::
      stS.req.dk.filter (fun p => p.1 != (stS'.res.resEpoch + roleS.offset))) :
    ∃ T' : Transcript kem,
      PartyInv roleS ecEk ecCt T' stS' stR (Function.update msgsS n (some (ρ, tsnd)))
          keyS keyR tsnd ∧
        PartyInv roleS.peer ecEk ecCt T' stR stS' msgsR keyR keyS tcurR := by
  have hp := send_provenance roleS kem ecEk ecCt stS none ρ tsnd stS' hout
  have hct : stS'.res.ct = stS.res.ct := hp.no_key_ciphertext rfl
  have hgate := send_advance_gate roleS kem ecEk ecCt stS none ρ tsnd stS' hout (by omega)
  have hctnone : stS.res.ct = none := hS.ct_acked hgate.1
  have hres_par : stS'.res.resEpoch % 2 = roleS.resParity := by
    have := hS.res_parity
    omega
  set eA := stS'.res.resEpoch + roleS.offset with heA
  have hparA : eA % 2 = roleS.reqParity := (Role.offset_parity roleS _).2 hres_par
  have hTA : (T eA).keypair = none := hS.keypair_future eA hparA (by omega)
  have hencA : (T eA).enc = none := EpochTranscript.enc_eq_none_of_keypair_eq_none _ hTA
  have hApos : 0 < eA := by
    have h1 := hS.res_lower
    have h2 := hS.res_parity
    cases roleS <;> simp only [Role.offset, Role.resParity] at h2 heA ⊢ <;> omega
  let T' : Transcript kem := Function.update T eA (EpochTranscript.ofKeypair pk₀ sk₀ hmem)
  have hT'kp : ∀ e, (T' e).keypair = if e = eA then some (pk₀, sk₀) else (T e).keypair := by
    intro e
    change (Function.update T eA _ e).keypair = _
    rw [Function.update_apply]
    split_ifs <;> rfl
  have hT'enc : ∀ e, (T' e).enc = (T e).enc := by
    intro e
    change (Function.update T eA _ e).enc = _
    rw [Function.update_apply]
    split_ifs with h
    · subst h
      rw [hencA]
      rfl
    · rfl
  have hT'key : ∀ e, (T' e).key = (T e).key := by
    intro e
    unfold EpochTranscript.key
    rw [hT'enc]
  have hneA : ∀ e, e % 2 = roleS.resParity → e ≠ eA := by
    intro e hpe h
    subst h
    exact Role.reqParity_ne_resParity roleS (hparA.symm.trans hpe)
  refine ⟨T', partyInv_sender_of_send roleS hS hR n hout ?_ ?_ ?_ (fun e _ => hT'enc e)
    (fun e _ => hT'enc e) (fun e _ => hT'enc e) (fun _ _ => rfl) ?_ ?_ ?_ ?_ ?_
    (fun _ => by rw [hT'kp, if_pos heA.symm]; rfl) ?_ ?_ ?_ ?_ ?_ hS.key_zero,
    partyInv_peer_of_send roleS hS hR hp.requester_epoch hp.peer_keys hp.acknowledgements
      (fun e hpe => by rw [hT'kp, if_neg (hneA e hpe)]) ?_ (fun e _ => hT'key e) ?_
      (fun e _ => hT'enc e) (fun e _ => hT'enc e)⟩
  · intro e hpe hs
    by_cases h : e = eA
    · exact Or.inr ⟨h, hres⟩
    · left
      rw [hT'kp, if_neg h] at hs
      exact hs
  · intro e hle hpe
    rw [hT'kp, if_neg (by omega)]
  · intro e hpe
    rw [hT'kp, if_neg (hneA e hpe)]
  · intro pk h
    rw [hek, Option.some.injEq] at h
    subst h
    exact ⟨sk₀, by rw [hT'kp, if_pos rfl]⟩
  · intro e sk h
    rw [hdk, List.mem_cons] at h
    rcases h with h | h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨hparA, hApos, le_rfl, ?_, pk₀, by rw [hT'kp, if_pos rfl]⟩
      have hk := hS.key_req eA hApos hparA
      rw [EpochTranscript.key_eq_none_of_keypair_eq_none _ hTA] at hk
      rw [hk]
      split_ifs <;> rfl
    · rw [List.mem_filter] at h
      obtain ⟨hmem', hne⟩ := h
      have hne' : e ≠ eA := by simpa using hne
      obtain ⟨hpe, hpos, hle, hkey, pk, hT⟩ := hS.dk_T e sk hmem'
      exact ⟨hpe, hpos, by omega, hkey, pk, by rw [hT'kp, if_neg hne']; exact hT⟩
  · intro e pk sk hT hpe hnot
    rw [hp.acknowledgements] at hnot
    rw [hdk]
    by_cases h : e = eA
    · subst h
      rw [hT'kp, if_pos rfl] at hT
      simp only [Option.some.injEq, Prod.mk.injEq] at hT
      obtain ⟨-, rfl⟩ := hT
      exact List.mem_cons.mpr (Or.inl rfl)
    · rw [hT'kp, if_neg h] at hT
      exact List.mem_cons.mpr (Or.inr (List.mem_filter.mpr
        ⟨hS.T_dk e pk sk hT hpe hnot, by simpa using h⟩))
  · -- Before an advance the secret-key list is empty: a retained key for the previous
    -- exchange would be undecapsulated, but the gate says that epoch is acknowledged.
    have hempty : stS.req.dk = [] := by
      rcases hS.dk_shape with h0 | ⟨sk₁, h1⟩
      · exact h0
      · exfalso
        have hmem₁ : (stS.res.resEpoch + roleS.offset, sk₁) ∈ stS.req.dk := by
          rw [h1]
          exact List.mem_singleton.mpr rfl
        obtain ⟨hpe, hpos, -, hkey, -⟩ := hS.dk_T _ sk₁ hmem₁
        have hk := hS.key_req _ hpos hpe
        rw [if_pos hgate.2, hkey] at hk
        have henc := hS.ctRec_req_enc _ hgate.2 hpos hpe
        obtain ⟨⟨c, k⟩, hck⟩ := Option.isSome_iff_exists.mp henc
        rw [EpochTranscript.key, hck] at hk
        cases hk
    right
    exact ⟨sk₀, by rw [hdk, hempty]; rfl⟩
  · intro h
    rw [hek] at h
    cases h
  · intro c k h
    rw [hT'enc, hS.enc_future _ hres_par (by omega)] at h
    cases h
  · intro c h
    rw [hct, hctnone] at h
    cases h
  · intro _
    rw [hct]
    exact hctnone
  · intro h
    rw [hT'enc, hS.enc_future _ hres_par (by omega)] at h
    cases h
  · rw [hT'key]
    exact hS.key_res _ (by have := hS.res_lower; omega) hres_par
  · intro e pk sk hT
    rw [hT'kp, if_neg]
    · exact hT
    · intro h
      subst h
      rw [hTA] at hT
      cases hT
  · intro e _ hle
    rw [hT'kp, if_neg (by omega)]

/-- An encapsulating send: no epoch advance, the current epoch's ciphertext is produced and
its key emitted; the transcript gains the encapsulation at the responder epoch. -/
private theorem send_step_encaps (roleS : Role) {kem : KEMScheme ProbComp K PK SK C}
    {ecEk : ErasureCodePayload PK Sym} {ecCt : ErasureCodePayload C Sym}
    {T : Transcript kem} {stS stS' stR : State PK SK C Sym}
    {msgsS msgsR : ℕ → Option (Message Sym × ℕ)} {keyS keyR : ℕ → Option K} {tcurS tcurR : ℕ}
    (hS : PartyInv roleS ecEk ecCt T stS stR msgsS keyS keyR tcurS)
    (hR : PartyInv roleS.peer ecEk ecCt T stR stS msgsR keyR keyS tcurR)
    (n : ℕ) (tI : ℕ) (k₀ : K) {ρ : Message Sym} {tsnd : ℕ}
    (hout : some (some (tI, k₀), ρ, tsnd, stS') ∈ support (send roleS kem ecEk ecCt stS))
    (hres : stS'.res.resEpoch = stS.res.resEpoch) (hdk : stS'.req.dk = stS.req.dk)
    (hek : stS'.req.ek = stS.req.ek) :
    ∃ T' : Transcript kem,
      PartyInv roleS ecEk ecCt T' stS' stR (Function.update msgsS n (some (ρ, tsnd)))
          (Function.update keyS tI (some k₀)) keyR tsnd ∧
        PartyInv roleS.peer ecEk ecCt T' stR stS' msgsR keyR
          (Function.update keyS tI (some k₀)) tcurR := by
  have hp := send_provenance roleS kem ecEk ecCt stS (some (tI, k₀)) ρ tsnd stS' hout
  obtain ⟨-, -, -, -, hkeyf⟩ :=
    send_support_facts roleS kem ecEk ecCt stS (some (tI, k₀)) ρ tsnd stS' hout
  obtain ⟨htI, hnotin, hctnone, -⟩ := hkeyf tI k₀ rfl
  obtain ⟨-, hbit, pk₀, c₀, hpeer, hmemc, hct'⟩ := hp.emitted_key tI k₀ rfl
  rw [hres] at htI hnotin hpeer
  subst htI
  obtain ⟨sk₀, hkp₀⟩ := hS.ekPeer_T _ pk₀ hpeer
  have hpos : 0 < stS.res.resEpoch :=
    hR.keypair_pos _ (by simpa using hS.res_parity) (by rw [hkp₀]; rfl)
  have hencB : (T stS.res.resEpoch).enc = none := by
    cases h : (T stS.res.resEpoch).enc with
    | none => rfl
    | some ck =>
      obtain ⟨c, k⟩ := ck
      rcases hS.enc_current c k h with h1 | h1
      · rw [hctnone] at h1
        cases h1
      · exact absurd h1 hnotin
  have hackk := send_ciphertextMessage_keyAck roleS kem ecEk ecCt stS _ ρ tsnd stS' hout hbit
  rw [hp.message_resEpoch] at hackk
  let T' : Transcript kem :=
    Function.update T stS.res.resEpoch ((T _).setEnc pk₀ sk₀ c₀ k₀ hkp₀ hmemc)
  have hT'kp : ∀ e, (T' e).keypair = (T e).keypair := by
    intro e
    change (Function.update T _ _ e).keypair = _
    rw [Function.update_apply]
    split_ifs with h
    · subst h
      rfl
    · rfl
  have hT'enc : ∀ e, (T' e).enc =
      if e = stS.res.resEpoch then some (c₀, k₀) else (T e).enc := by
    intro e
    change (Function.update T _ _ e).enc = _
    rw [Function.update_apply]
    split_ifs <;> rfl
  have hencReq : ∀ e, e % 2 = roleS.reqParity → (T' e).enc = (T e).enc := by
    intro e hpe
    rw [hT'enc, if_neg]
    intro h
    subst h
    exact Role.reqParity_ne_resParity roleS (hpe.symm.trans hS.res_parity)
  have hencMono : ∀ e, (T e).enc.isSome = true → (T' e).enc = (T e).enc := by
    intro e hs
    rw [hT'enc, if_neg]
    intro h
    subst h
    rw [hencB] at hs
    cases hs
  refine ⟨T', partyInv_sender_of_send roleS hS hR n hout
    (fun e _ hs => Or.inl (by rw [← hT'kp]; exact hs)) (fun e _ _ => hT'kp e)
    (fun e _ => hT'kp e) ?_ hencReq hencMono ?_ ?_ ?_ ?_ ?_ ?_
    (by rw [hres, hT'kp]; exact hS.keypair_current) ?_ ?_ ?_ ?_ ?_ ?_,
    partyInv_peer_of_send roleS hS hR hp.requester_epoch hp.peer_keys hp.acknowledgements
      (fun e _ => hT'kp e) (fun e pk sk hT => by rw [hT'kp]; exact hT)
      (fun e hpe => by unfold EpochTranscript.key; rw [hencReq e hpe]) (fun e _ _ => hT'kp e)
      hencReq hencMono⟩
  · intro e he
    rw [hres] at he
    rw [hT'enc, if_neg he]
  · intro i hi
    rw [hres] at hi
    exact Function.update_of_ne hi _ _
  · intro pk h
    rw [hek] at h
    rw [hres, hT'kp]
    exact hS.ek_T pk h
  · intro e sk h
    rw [hdk] at h
    obtain ⟨hpe, hpos', hle, hkey, pk, hT⟩ := hS.dk_T e sk h
    refine ⟨hpe, hpos', by rw [hres]; exact hle, ?_, pk, by rw [hT'kp]; exact hT⟩
    have hne : e ≠ stS.res.resEpoch := fun h =>
      Role.reqParity_ne_resParity roleS (hpe.symm.trans (h ▸ hS.res_parity))
    rw [Function.update_of_ne (by omega)]
    exact hkey
  · intro e pk sk hT hpe hnot
    rw [hp.acknowledgements] at hnot
    rw [hdk]
    rw [hT'kp] at hT
    exact hS.T_dk e pk sk hT hpe hnot
  · rw [hdk, hres]
    exact hS.dk_shape
  · intro h
    rw [hek] at h
    rw [hres, hp.acknowledgements, hT'kp]
    exact hS.ek_acked h
  · intro c k h
    rw [hres, hT'enc, if_pos rfl] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl hct'
  · intro c h
    rw [hct', Option.some.injEq] at h
    subst h
    exact ⟨k₀, by rw [hres, hT'enc, if_pos rfl]⟩
  · intro h
    rw [hp.acknowledgements, hres] at h
    exact absurd h hnotin
  · intro _
    rw [hp.acknowledgements]
    exact hackk
  · rw [hres, Function.update_self]
    unfold EpochTranscript.key
    rw [hT'enc, if_pos rfl]
    rfl
  · rw [Function.update_of_ne (by omega)]
    exact hS.key_zero

/-! ### The send step -/

/-- A supported send by `roleS` preserves the main invariant for both parties, for a suitably
updated transcript, and satisfies the game's send-side assertions: monotonicity of the
sending epoch, the known-prefix check, and uniqueness and consistency of an emitted key. -/
theorem partyInv_send_step (roleS : Role) (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (T : Transcript kem) (stS stR : State PK SK C Sym)
    (msgsS msgsR : ℕ → Option (Message Sym × ℕ)) (keyS keyR : ℕ → Option K)
    (tcurS tcurR : ℕ)
    (hS : PartyInv roleS ecEk ecCt T stS stR msgsS keyS keyR tcurS)
    (hR : PartyInv roleS.peer ecEk ecCt T stR stS msgsR keyR keyS tcurR)
    (n : ℕ) (key? : Option (ℕ × K)) (ρ : Message Sym) (tsnd : ℕ) (stS' : State PK SK C Sym)
    (hout : some (key?, ρ, tsnd, stS') ∈ support (send roleS kem ecEk ecCt stS)) :
    tcurS ≤ tsnd ∧
    (List.range (tsnd + 1)).all (fun t => t = 0 || (recordKey keyS key? t).isSome) = true ∧
    (∀ tI k, key? = some (tI, k) → keyS tI = none ∧ (keyR tI = none ∨ keyR tI = some k)) ∧
    ∃ T' : Transcript kem,
      PartyInv roleS ecEk ecCt T' stS' stR (Function.update msgsS n (some (ρ, tsnd)))
        (recordKey keyS key?) keyR tsnd ∧
      PartyInv roleS.peer ecEk ecCt T' stR stS' msgsR keyR (recordKey keyS key?) tcurR := by
  have hp := send_provenance roleS kem ecEk ecCt stS key? ρ tsnd stS' hout
  obtain ⟨hack, htsnd, hres_or, -, hkeyf⟩ :=
    send_support_facts roleS kem ecEk ecCt stS key? ρ tsnd stS' hout
  -- An emitted key excludes an advance: a fresh key is not yet acknowledged.
  have hnoadv : ∀ tI k, key? = some (tI, k) → stS'.res.resEpoch = stS.res.resEpoch := by
    intro tI k hkey
    rcases hres_or with h | h
    · exact h
    · exfalso
      obtain ⟨-, hbit, -⟩ := hp.emitted_key tI k hkey
      have hackk :=
        send_ciphertextMessage_keyAck roleS kem ecEk ecCt stS key? ρ tsnd stS' hout hbit
      rw [hp.message_resEpoch, h] at hackk
      have hpar : (stS.res.resEpoch + 2 + roleS.offset) % 2 = roleS.reqParity := by
        rw [Role.offset_parity]
        have := hS.res_parity
        omega
      obtain ⟨pk, hpk⟩ := Option.isSome_iff_exists.mp (hS.ekRec_req _ hackk hpar)
      obtain ⟨sk, hT⟩ := hR.ekPeer_T _ pk hpk
      rw [hS.keypair_future _ hpar (by omega)] at hT
      cases hT
  refine ⟨htsnd ▸ hS.horizon, ?_, ?_, ?_⟩
  · have hkp := knownPrefix_of_partyInv hS hR tsnd (le_of_eq htsnd)
    rcases key? with _ | ⟨tI, k⟩
    · exact hkp
    · rw [List.all_eq_true] at hkp ⊢
      intro t ht
      have := hkp t ht
      by_cases h : t = tI
      · subst h
        simp
      · simpa only [recordKey_some, Function.update_of_ne h] using this
  · intro tI k hkey
    have hres := hnoadv tI k hkey
    obtain ⟨htI, hnotin, hctnone, -⟩ := hkeyf tI k hkey
    obtain ⟨-, -, pk₀, c₀, hpeer, -, -⟩ := hp.emitted_key tI k hkey
    rw [hres] at htI hnotin hpeer
    obtain ⟨sk₀, hkp₀⟩ := hS.ekPeer_T _ pk₀ hpeer
    have hpos : 0 < stS.res.resEpoch :=
      hR.keypair_pos _ (by simpa using hS.res_parity) (by rw [hkp₀]; rfl)
    have hencB : (T stS.res.resEpoch).enc = none := by
      cases h : (T stS.res.resEpoch).enc with
      | none => rfl
      | some ck =>
        obtain ⟨c, k'⟩ := ck
        rcases hS.enc_current c k' h with h1 | h1
        · rw [hctnone] at h1
          cases h1
        · exact absurd h1 hnotin
    subst htI
    refine ⟨?_, Or.inl ?_⟩
    · rw [hS.key_res _ hpos hS.res_parity]
      unfold EpochTranscript.key
      rw [hencB]
      rfl
    · rw [hR.key_req _ hpos (by simpa using hS.res_parity)]
      split_ifs with hmem
      · exfalso
        have := hR.ctRec_req_enc _ hmem hpos (by simpa using hS.res_parity)
        rw [hencB] at this
        cases this
      · rfl
  · rcases hp.keygen_transition with ⟨hres, hdk, hek⟩ | ⟨pk₀, sk₀, hmem, hres, hek, hdk⟩
    · rcases key? with _ | ⟨tI, k₀⟩
      · exact ⟨T, send_step_plain roleS hS hR n hout hres hdk hek⟩
      · exact send_step_encaps roleS hS hR n tI k₀ hout hres hdk hek
    · have hkeynone : key? = none := by
        rcases key? with _ | ⟨tI, k⟩
        · rfl
        · have := hnoadv tI k rfl
          omega
      subst hkeynone
      exact send_step_advance roleS hS hR n hout pk₀ sk₀ hmem hres hek hdk

end oppBiKemCKA
