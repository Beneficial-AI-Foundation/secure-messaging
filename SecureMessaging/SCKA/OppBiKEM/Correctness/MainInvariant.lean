/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Gavran, Beneficial AI Foundation
-/

import SecureMessaging.ErasureCode.Payload
import SecureMessaging.SCKA.OppBiKEM.Correctness.Transcript
import SecureMessaging.SCKA.OppBiKEM.Correctness.SendFacts

/-!
# Opp-BiKEM-CKA — Main invariant

The module introduces:

* `BufferConsistent role ecEk ecCt T st` — the party's chunk buffer is an honest
  below-threshold chunk set of the payload it currently expects;
* `MessageInv role ecEk ecCt T st ρ tsnd` — the recorded outgoing message `(ρ, tsnd)` of the
  party in state `st` is honest with respect to the transcript `T`;
* `PartyInv role ecEk ecCt T st peer ownMsgs ownKey peerKey tcur` — the main per-party
  invariant: the party's state, outgoing message table, key table and game horizon agree with
  `T` and with the peer's state;
* `recordKey keys key?` — the key table after recording an optional emitted key;
* `GameInv s` — the game invariant: `s.correct = true`, and one transcript `T` satisfies
  `PartyInv` for both A and B.

The fields of `PartyInv` are grouped as shape (parities, lower bounds, lockstep of the two
parties' epochs), own key pairs, own encapsulations, decoded peer keys, key tables,
acknowledgements, buffer, horizon, and messages. The *key epoch* of a party is
`resEpoch + role.offset`, the requester-parity epoch of its current own key pair.

This file derives the game's known-prefix assertion from `PartyInv`
(`knownPrefix_of_partyInv`). `GameInv` holds initially (`MainInvariant.Init`) and is preserved
by a send (`MainInvariant.Send`), by a receive (`MainInvariant.Recv`), and hence by every oracle
(`MainInvariant.Game`); KEM correctness is used only for the key emitted by a decapsulation.
The support-level facts about one `send` or `recv` that these proofs use are in `SendFacts`
and `RecvFacts`.
-/

open OracleComp KEMScheme ErasureCodePayload

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-- The chunk buffer holds an honest below-threshold chunk set of the payload the requester
currently expects: nothing once `reqEpoch ∈ ctRec`; chunks of the peer's public key for epoch
`reqEpoch - role.offset` while that key is undecoded; chunks of the ciphertext for `reqEpoch`
afterwards. If the transcript has not produced that payload yet, the buffer is empty. -/
def BufferConsistent (role : Role) {kem : KEMScheme ProbComp K PK SK C}
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (T : Transcript kem) (st : State PK SK C Sym) : Prop :=
  if st.req.reqEpoch ∈ st.ack.ctRec then st.req.receivedChunks = ∅
  else if (st.res.ekPeer (st.req.reqEpoch - role.offset)).isNone = true then
    match (T (st.req.reqEpoch - role.offset)).keypair with
    | none => st.req.receivedChunks = ∅
    | some (pk, _) => ∃ I, st.req.receivedChunks = payloadChunks ecEk pk I ∧ I.card < ecEk.ec.nchunk
  else
    match (T st.req.reqEpoch).enc with
    | none => st.req.receivedChunks = ∅
    | some (c, _) => ∃ I, st.req.receivedChunks = payloadChunks ecCt c I ∧ I.card < ecCt.ec.nchunk

/-- Honesty of one recorded outgoing message `(ρ, tsnd)` of the party `role` in state `st`,
with respect to the transcript `T`. -/
structure MessageInv (role : Role) {kem : KEMScheme ProbComp K PK SK C}
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (T : Transcript kem) (st : State PK SK C Sym) (ρ : Message Sym) (tsnd : ℕ) : Prop where
  /-- The recorded sending epoch is the one carried by the message. -/
  epoch : tsnd = ρ.sendingEpoch
  /-- The message carries the sender's responder parity. -/
  res_parity : ρ.tRes % 2 = role.resParity
  /-- The message carries the sender's requester parity. -/
  req_parity : ρ.tReq % 2 = role.reqParity
  /-- The carried responder epoch is at most the sender's current responder epoch. -/
  res_le : ρ.tRes ≤ st.res.resEpoch
  /-- The carried requester epoch is at most the sender's current requester epoch. -/
  req_le : ρ.tReq ≤ st.req.reqEpoch
  /-- Carried epochs never go below the bootstrap value `-1`. -/
  res_lower : -1 ≤ ρ.tRes
  /-- Carried epochs never go below the bootstrap value `-1`. -/
  req_lower : -1 ≤ ρ.tReq
  /-- A public-key message carries a chunk of the transcript's public key for the key epoch
  `ρ.tRes + role.offset`. -/
  pk_chunk : ρ.bit = some 0 → ∃ pk sk i,
    (T (ρ.tRes + role.offset)).keypair = some (pk, sk) ∧ ρ.ch = some (ecEk.encode pk i)
  /-- A chunk on a ciphertext message encodes the transcript's ciphertext for `ρ.tRes`. -/
  ct_chunk : ρ.bit = some 1 → ∀ ch, ρ.ch = some ch → ∃ c k i,
    (T ρ.tRes).enc = some (c, k) ∧ ch = ecCt.encode c i
  /-- A message without payload selector carries no chunk. -/
  no_chunk : ρ.bit = none → ρ.ch = none
  /-- A set ciphertext flag is backed by `ρ.tReq ∈ ctRec` in the sender's state. -/
  ct_flag : ρ.ack.ctRec = true → ρ.tReq ∈ st.ack.ctRec
  /-- A set public-key flag is backed by `ρ.tReq - role.offset ∈ ekRec` in the sender's state. -/
  ek_flag : ρ.ack.ekRec = true → ρ.tReq - role.offset ∈ st.ack.ekRec
  /-- A ciphertext message implies that the sender's own public key for `ρ.tRes + role.offset`
  is acknowledged (`ekRec`). -/
  bit1_acked : ρ.bit = some 1 → ρ.tRes + role.offset ∈ st.ack.ekRec
  /-- Every positive epoch up to the advertised sending epoch is in the sender's `ctRec`. -/
  horizon_mem : ∀ s : ℤ, 0 < s → s ≤ ρ.sendingEpoch → s ∈ st.ack.ctRec
  /-- A positive requester-parity epoch up to the advertised sending epoch is at most the
  carried requester epoch, and the ciphertext flag is set when it equals it. -/
  horizon_req : ∀ s : ℤ, 0 < s → s ≤ ρ.sendingEpoch → s % 2 = role.reqParity →
    s ≤ ρ.tReq ∧ (s = ρ.tReq → ρ.ack.ctRec = true)

/-- The main per-party invariant. `st` is the party's state, `peer` the peer's, `ownMsgs` the
party's outgoing table, `ownKey`/`peerKey` the two game key tables, and `tcur` the party's
game horizon. -/
structure PartyInv (role : Role) {kem : KEMScheme ProbComp K PK SK C}
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (T : Transcript kem) (st peer : State PK SK C Sym)
    (ownMsgs : ℕ → Option (Message Sym × ℕ))
    (ownKey peerKey : ℕ → Option K) (tcur : ℕ) : Prop where
  -- shape
  /-- The responder epoch has the role's responder parity. -/
  res_parity : st.res.resEpoch % 2 = role.resParity
  /-- The requester epoch has the role's requester parity. -/
  req_parity : st.req.reqEpoch % 2 = role.reqParity
  /-- Epochs never go below the bootstrap value `-1`. -/
  res_lower : -1 ≤ st.res.resEpoch
  /-- Epochs never go below the bootstrap value `-1`. -/
  req_lower : -1 ≤ st.req.reqEpoch
  /-- The bootstrap epochs `-1` and `0` are in `ctRec`. -/
  init_acks : (-1 : ℤ) ∈ st.ack.ctRec ∧ (0 : ℤ) ∈ st.ack.ctRec
  /-- Lockstep: the responder is at most one exchange ahead of the peer's requester. -/
  res_le_peer_req : st.res.resEpoch ≤ peer.req.reqEpoch + 2
  /-- Lockstep: the peer's requester never overtakes the responder driving it. -/
  peer_req_le_res : peer.req.reqEpoch ≤ st.res.resEpoch
  -- own key pairs (requester parity)
  /-- Key pairs at the requester parity exist only at positive epochs. -/
  keypair_pos : ∀ e, e % 2 = role.reqParity → (T e).keypair.isSome = true → 0 < e
  /-- No key pair at the requester parity beyond the key epoch. -/
  keypair_future : ∀ e, e % 2 = role.reqParity → st.res.resEpoch + role.offset < e →
    (T e).keypair = none
  /-- The retained public key is the transcript's public key for the key epoch. -/
  ek_T : ∀ pk, st.req.ek = some pk →
    ∃ sk, (T (st.res.resEpoch + role.offset)).keypair = some (pk, sk)
  /-- Every retained secret key is the transcript's, for a positive requester-parity epoch at
  most the key epoch and without an entry in the own key table. -/
  dk_T : ∀ e sk, (e, sk) ∈ st.req.dk →
    e % 2 = role.reqParity ∧ 0 < e ∧ e ≤ st.res.resEpoch + role.offset ∧
      ownKey e.toNat = none ∧ ∃ pk, (T e).keypair = some (pk, sk)
  /-- Every requester-parity secret key of the transcript whose epoch is not in `ctRec` is
  retained. -/
  T_dk : ∀ e pk sk, (T e).keypair = some (pk, sk) → e % 2 = role.reqParity →
    e ∉ st.ack.ctRec → (e, sk) ∈ st.req.dk
  /-- At most one secret key is retained, and it belongs to the key epoch: the advance gate
  requires the previous key epoch to be decapsulated. -/
  dk_shape : st.req.dk = [] ∨ ∃ sk, st.req.dk = [(st.res.resEpoch + role.offset, sk)]
  /-- If no own public key is retained, then none was generated for the key epoch or it is
  acknowledged (`ekRec`). -/
  ek_acked : st.req.ek = none →
    (T (st.res.resEpoch + role.offset)).keypair = none ∨
      st.res.resEpoch + role.offset ∈ st.ack.ekRec
  /-- If the key epoch is positive, the transcript has a key pair for it. -/
  keypair_current : 0 < st.res.resEpoch + role.offset →
    (T (st.res.resEpoch + role.offset)).keypair.isSome = true
  -- own encapsulations (responder parity)
  /-- No encapsulation beyond the current responder epoch. -/
  enc_future : ∀ e, e % 2 = role.resParity → st.res.resEpoch < e → (T e).enc = none
  /-- The current epoch's encapsulation, if any, is retained or acknowledged. -/
  enc_current : ∀ c k, (T st.res.resEpoch).enc = some (c, k) →
    st.res.ct = some c ∨ st.res.resEpoch ∈ st.ack.ctRec
  /-- The retained ciphertext is the transcript's for the current responder epoch. -/
  ct_T : ∀ c, st.res.ct = some c → ∃ k, (T st.res.resEpoch).enc = some (c, k)
  /-- An acknowledged ciphertext is no longer retained. -/
  ct_acked : st.res.resEpoch ∈ st.ack.ctRec → st.res.ct = none
  /-- An encapsulation at `e` implies that the own public key for `e + role.offset` is
  acknowledged (`ekRec`). -/
  enc_ekRec : ∀ e, e % 2 = role.resParity → (T e).enc.isSome = true →
    e + role.offset ∈ st.ack.ekRec
  -- decoded peer keys
  /-- A decoded peer key is the transcript's public key for that epoch. -/
  ekPeer_T : ∀ e pk, st.res.ekPeer e = some pk → ∃ sk, (T e).keypair = some (pk, sk)
  /-- Peer keys sit at the responder parity. -/
  ekPeer_parity : ∀ e, (st.res.ekPeer e).isSome = true → e % 2 = role.resParity
  /-- Peer keys are decoded only up to epoch `reqEpoch - role.offset`. -/
  ekPeer_le : ∀ e, (st.res.ekPeer e).isSome = true → e ≤ st.req.reqEpoch - role.offset
  -- key tables
  /-- Epoch `0` never gets a key. -/
  key_zero : ownKey 0 = none
  /-- At positive responder-parity epochs the key table is the transcript key (written at
  encapsulation). -/
  key_res : ∀ e : ℤ, 0 < e → e % 2 = role.resParity → ownKey e.toNat = (T e).key
  /-- At positive requester-parity epochs the key table is the transcript key once the epoch is
  in `ctRec` (written at decapsulation), and empty before. -/
  key_req : ∀ e : ℤ, 0 < e → e % 2 = role.reqParity →
    ownKey e.toNat = if e ∈ st.ack.ctRec then (T e).key else none
  -- acknowledgements: ciphertexts
  /-- A positive requester-parity `ctRec` entry (an own decapsulation) has an encapsulation in
  the transcript. -/
  ctRec_req_enc : ∀ t ∈ st.ack.ctRec, 0 < t → t % 2 = role.reqParity → (T t).enc.isSome = true
  /-- Requester-parity `ctRec` entries are at or below the requester epoch. -/
  ctRec_req_le : ∀ t ∈ st.ack.ctRec, t % 2 = role.reqParity → t ≤ st.req.reqEpoch
  /-- A responder-parity `ctRec` entry is in the peer's `ctRec` (the peer decapsulated it). -/
  ctRec_res_peer : ∀ t ∈ st.ack.ctRec, t % 2 = role.resParity → t ∈ peer.ack.ctRec
  /-- Responder-parity `ctRec` entries are at or below the responder epoch. -/
  ctRec_res_le : ∀ t ∈ st.ack.ctRec, t % 2 = role.resParity → t ≤ st.res.resEpoch
  /-- Every positive requester-parity epoch below the requester epoch is in `ctRec`. -/
  ctRec_req_closed : ∀ t : ℤ, 0 < t → t % 2 = role.reqParity → t < st.req.reqEpoch →
    t ∈ st.ack.ctRec
  /-- Every positive responder-parity epoch below the responder epoch is in `ctRec`. -/
  ctRec_res_closed : ∀ t : ℤ, 0 < t → t % 2 = role.resParity → t < st.res.resEpoch →
    t ∈ st.ack.ctRec
  -- acknowledgements: public keys
  /-- A responder-parity `ekRec` entry has a decoded peer key. -/
  ekRec_res : ∀ t ∈ st.ack.ekRec, t % 2 = role.resParity → (st.res.ekPeer t).isSome = true
  /-- A requester-parity `ekRec` entry has been decoded by the peer. -/
  ekRec_req : ∀ t ∈ st.ack.ekRec, t % 2 = role.reqParity → (peer.res.ekPeer t).isSome = true
  -- buffer
  /-- The shared chunk buffer is honest for the payload currently expected. -/
  buffer : BufferConsistent role ecEk ecCt T st
  -- horizon
  /-- The game horizon is at most the sending horizon. -/
  horizon : tcur ≤ st.ack.sendingHorizon
  -- messages
  /-- Every recorded outgoing message is honest. -/
  msgs : ∀ n ρ tsnd, ownMsgs n = some (ρ, tsnd) → MessageInv role ecEk ecCt T st ρ tsnd
  /-- A ciphertext flag on a message at a lower responder epoch is at most the requester epoch
  of any message at a higher responder epoch, and the flag transfers when they are equal. -/
  msgs_flag_mono : ∀ n n' ρ ρ' tsnd tsnd', ownMsgs n = some (ρ, tsnd) →
    ownMsgs n' = some (ρ', tsnd') → ρ.tRes < ρ'.tRes → ρ.ack.ctRec = true →
    ρ.tReq ≤ ρ'.tReq ∧ (ρ.tReq = ρ'.tReq → ρ'.ack.ctRec = true)
  /-- A recorded message the peer already considers stale carries no new ciphertext
  acknowledgement: the stale receive path skips the cleanup, so this is what keeps `ct_acked`. -/
  msgs_stale : ∀ n ρ tsnd, ownMsgs n = some (ρ, tsnd) → ρ.tRes < peer.req.reqEpoch →
    ρ.ack.ctRec = true → ρ.tReq ∈ peer.ack.ctRec

/-- Key table after recording an optional emitted key. -/
def recordKey (keys : ℕ → Option K) : Option (ℕ × K) → ℕ → Option K
  | none => keys
  | some (tI, k) => Function.update keys tI (some k)

/-- Recording no key leaves the table unchanged. -/
@[simp] theorem recordKey_none (keys : ℕ → Option K) : recordKey keys none = keys := rfl
/-- Recording `(tI, k)` updates the table at `tI`. -/
@[simp] theorem recordKey_some (keys : ℕ → Option K) (tI : ℕ) (k : K) :
    recordKey keys (some (tI, k)) = Function.update keys tI (some k) := rfl

/-- The game invariant: the correctness flag is set, and one transcript `T` satisfies `PartyInv`
for both A and B. -/
def GameInv (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) : Prop :=
  s.correct = true ∧ ∃ T : Transcript kem,
    PartyInv .A ecEk ecCt T s.stA s.stB s.msgA s.keyA s.keyB s.tcurA ∧
    PartyInv .B ecEk ecCt T s.stB s.stA s.msgB s.keyB s.keyA s.tcurB

/-! ### Consequences -/

namespace PartyInv

variable {role : Role} {kem : KEMScheme ProbComp K PK SK C}
  {ecEk : ErasureCodePayload PK Sym} {ecCt : ErasureCodePayload C Sym}
  {T : Transcript kem} {st peer : State PK SK C Sym}
  {ownMsgs : ℕ → Option (Message Sym × ℕ)} {ownKey peerKey : ℕ → Option K} {tcur : ℕ}

/-- The two parities of a role are the two residues mod 2. -/
theorem parity_cases (role : Role) (t : ℤ) :
    t % 2 = role.reqParity ∨ t % 2 = role.resParity := by
  cases role <;> simp only [Role.reqParity, Role.resParity] <;> omega

/-- If `t` and `t - 1` are in `ctRec`, so is every positive epoch up to `t`. -/
theorem ctRec_prefix (h : PartyInv role ecEk ecCt T st peer ownMsgs ownKey peerKey tcur)
    (t : ℤ) (ht : t ∈ st.ack.ctRec) (ht' : t - 1 ∈ st.ack.ctRec) :
    ∀ s : ℤ, 0 < s → s ≤ t → s ∈ st.ack.ctRec := by
  intro s hs hst
  rcases parity_cases role t with hpt | hpt
  · have hle := h.ctRec_req_le t ht hpt
    have hle' := h.ctRec_res_le (t - 1) ht' (by
      cases role <;> simp only [Role.reqParity, Role.resParity] at hpt ⊢ <;> omega)
    rcases parity_cases role s with hps | hps
    · rcases lt_or_eq_of_le hst with hlt | rfl
      · exact h.ctRec_req_closed s hs hps (by omega)
      · exact ht
    · by_cases hst' : s = t - 1
      · subst hst'; exact ht'
      · exact h.ctRec_res_closed s hs hps (by
          cases role <;> simp only [Role.reqParity, Role.resParity] at hpt hps ⊢ <;> omega)
  · have hle := h.ctRec_res_le t ht hpt
    have hle' := h.ctRec_req_le (t - 1) ht' (by
      cases role <;> simp only [Role.reqParity, Role.resParity] at hpt ⊢ <;> omega)
    rcases parity_cases role s with hps | hps
    · by_cases hst' : s = t - 1
      · subst hst'; exact ht'
      · exact h.ctRec_req_closed s hs hps (by
          cases role <;> simp only [Role.reqParity, Role.resParity] at hpt hps ⊢ <;> omega)
    · rcases lt_or_eq_of_le hst with hlt | rfl
      · exact h.ctRec_res_closed s hs hps (by omega)
      · exact ht

/-- A positive sending horizon `t` has `t` and `t - 1` in `ctRec`. -/
theorem sendingHorizon_attained (ack : Acknowledgements) (hpos : 0 < ack.sendingHorizon) :
    (ack.sendingHorizon : ℤ) ∈ ack.ctRec ∧ (ack.sendingHorizon : ℤ) - 1 ∈ ack.ctRec := by
  unfold Acknowledgements.sendingHorizon at *
  set F := ack.ctRec.filter fun t => t - 1 ∈ ack.ctRec with hF
  rcases F.eq_empty_or_nonempty with hemp | hne
  · rw [hemp] at hpos
    simp at hpos
  · obtain ⟨t, htF, hsup⟩ := Finset.exists_mem_eq_sup F hne Int.toNat
    rw [hsup] at hpos ⊢
    rw [Finset.mem_filter] at htF
    have hcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg (by omega)
    rw [hcast]
    exact htF

/-- Every positive epoch up to the sending horizon is in `ctRec`. -/
theorem horizon_prefix (h : PartyInv role ecEk ecCt T st peer ownMsgs ownKey peerKey tcur) :
    ∀ s : ℤ, 0 < s → s ≤ st.ack.sendingHorizon → s ∈ st.ack.ctRec := by
  intro s hs hle
  have hpos : 0 < st.ack.sendingHorizon := by omega
  obtain ⟨ht, ht'⟩ := sendingHorizon_attained st.ack hpos
  exact h.ctRec_prefix _ ht ht' s hs hle

end PartyInv

/-- For every positive epoch in a party's `ctRec`, both game key tables hold a key. -/
theorem keys_of_ctRec {kem : KEMScheme ProbComp K PK SK C}
    {ecEk : ErasureCodePayload PK Sym} {ecCt : ErasureCodePayload C Sym}
    {T : Transcript kem} {role : Role} {st peer : State PK SK C Sym}
    {ownMsgs peerMsgs : ℕ → Option (Message Sym × ℕ)} {ownKey peerKey : ℕ → Option K}
    {tcur tcur' : ℕ}
    (h : PartyInv role ecEk ecCt T st peer ownMsgs ownKey peerKey tcur)
    (h' : PartyInv role.peer ecEk ecCt T peer st peerMsgs peerKey ownKey tcur')
    (t : ℤ) (ht : t ∈ st.ack.ctRec) (hpos : 0 < t) :
    ownKey t.toNat ≠ none ∧ peerKey t.toNat ≠ none := by
  rcases PartyInv.parity_cases role t with hp | hp
  · have henc := h.ctRec_req_enc t ht hpos hp
    obtain ⟨⟨c, k⟩, hck⟩ := Option.isSome_iff_exists.mp henc
    have hp' : t % 2 = role.peer.resParity := by simpa using hp
    refine ⟨?_, ?_⟩
    · rw [h.key_req t hpos hp, if_pos ht, EpochTranscript.key, hck]
      simp
    · rw [h'.key_res t hpos hp', EpochTranscript.key, hck]
      simp
  · have hpeer := h.ctRec_res_peer t ht hp
    have hp' : t % 2 = role.peer.reqParity := by simpa using hp
    have henc := h'.ctRec_req_enc t hpeer hpos hp'
    obtain ⟨⟨c, k⟩, hck⟩ := Option.isSome_iff_exists.mp henc
    refine ⟨?_, ?_⟩
    · rw [h.key_res t hpos hp, EpochTranscript.key, hck]
      simp
    · rw [h'.key_req t hpos hp', if_pos hpeer, EpochTranscript.key, hck]
      simp

/-- The game's known-prefix assertion: for every bound at most the sending horizon, the party's
key table holds a key for every positive epoch up to the bound. -/
theorem knownPrefix_of_partyInv {kem : KEMScheme ProbComp K PK SK C}
    {ecEk : ErasureCodePayload PK Sym} {ecCt : ErasureCodePayload C Sym}
    {T : Transcript kem} {role : Role} {st peer : State PK SK C Sym}
    {ownMsgs peerMsgs : ℕ → Option (Message Sym × ℕ)} {ownKey peerKey : ℕ → Option K}
    {tcur tcur' : ℕ}
    (h : PartyInv role ecEk ecCt T st peer ownMsgs ownKey peerKey tcur)
    (h' : PartyInv role.peer ecEk ecCt T peer st peerMsgs peerKey ownKey tcur')
    (bound : ℕ) (hbound : bound ≤ st.ack.sendingHorizon) :
    (List.range (bound + 1)).all (fun t => t = 0 || (ownKey t).isSome) = true := by
  rw [List.all_eq_true]
  intro t ht
  have htle : t ≤ bound := by simpa using List.mem_range.mp ht
  by_cases ht0 : t = 0
  · simp [ht0]
  have hpos : (0 : ℤ) < t := by omega
  have hmem := h.horizon_prefix t hpos (by omega)
  have hk := (keys_of_ctRec h h' t hmem hpos).1
  simp only [Int.toNat_natCast] at hk
  simp [ht0, Option.isSome_iff_ne_none, hk]

end oppBiKemCKA
