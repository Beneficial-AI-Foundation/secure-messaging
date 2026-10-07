/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Construction
import SecureMessaging.SCKA.Correctness.OracleSupport

/-!
# Opp-BiKEM-CKA — Facts about a single send

Support-level facts about `send`, used by the main-invariant proofs: the sending horizon
(`Acknowledgements.sendingHorizon`), what every successful send preserves
(`send_support_facts`), the full provenance record of a successful send (`SendProvenance`,
`send_provenance`), the key-acknowledgement guard on ciphertext messages
(`send_ciphertextMessage_keyAck`), and the advance guard (`send_advance_guard`).
-/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-- The sending horizon of an acknowledgement set: the largest nonnegative epoch `t` such that
both `t` and `t - 1` are acknowledged ciphertext epochs. It is the `sendingEpoch` a party puts on
its messages. -/
def Acknowledgements.sendingHorizon (ack : Acknowledgements) : ℕ :=
  (ack.ctRec.filter fun t => t - 1 ∈ ack.ctRec).sup Int.toNat

/-- The sending horizon is monotone in the ciphertext acknowledgements. -/
theorem Acknowledgements.sendingHorizon_mono
    (ack ack' : Acknowledgements)
    (hct : ack.ctRec ⊆ ack'.ctRec) :
    ack.sendingHorizon ≤ ack'.sendingHorizon := by
  unfold sendingHorizon
  apply Finset.sup_mono
  intro t ht
  rw [Finset.mem_filter] at ht ⊢
  exact ⟨hct ht.1, hct ht.2⟩

/-- The `A` case of `send_support_facts`, for `sendWith` with arbitrary samplers. -/
private theorem sendWith_support_facts
    {RKey REnc : Type} (keygen : ProbComp ((PK × SK) × RKey))
    (encaps : PK → ProbComp ((C × K) × REnc))
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : StA PK SK C Sym) (key? : Option (ℕ × K)) (ρ : Message Sym) (tsnd : ℕ)
    (st' : StA PK SK C Sym) (rand : SendRand RKey REnc)
    (hout : some (key?, ρ, tsnd, st', rand) ∈
      support (sendWith .A keygen encaps ecEk ecCt st)) :
    st'.ack = st.ack ∧ tsnd = st.ack.sendingHorizon ∧
    (st'.res.resEpoch = st.res.resEpoch ∨ st'.res.resEpoch = st.res.resEpoch + 2) ∧
    (key? = none → st'.res.ct = st.res.ct) ∧
    (∀ tI key, key? = some (tI, key) → tI = st'.res.resEpoch.toNat ∧
      st'.res.resEpoch ∉ st.ack.ctRec ∧ st.res.ct = none ∧ st'.res.ct.isSome) := by
  unfold sendWith at hout
  dsimp only at hout
  repeat' first
    | split at hout
    | (rw [mem_support_bind_iff] at hout; obtain ⟨x, _, hout⟩ := hout)
  all_goals simp only [support_pure, Set.mem_singleton_iff,
    Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hout
  all_goals obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hout
  all_goals simp_all [Acknowledgements.sendingHorizon, Role.offset]

/-- `send_support_facts` for `sendA`. -/
theorem sendA_support_facts (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : StA PK SK C Sym) (key? : Option (ℕ × K)) (ρ : Message Sym) (tsnd : ℕ)
    (st' : StA PK SK C Sym)
    (hout : some (key?, ρ, tsnd, st') ∈ support (sendA kem ecEk ecCt st)) :
    st'.ack = st.ack ∧ tsnd = st.ack.sendingHorizon ∧
    (st'.res.resEpoch = st.res.resEpoch ∨ st'.res.resEpoch = st.res.resEpoch + 2) ∧
    (key? = none → st'.res.ct = st.res.ct) ∧
    (∀ tI key, key? = some (tI, key) → tI = st'.res.resEpoch.toNat ∧
      st'.res.resEpoch ∉ st.ack.ctRec ∧ st.res.ct = none ∧ st'.res.ct.isSome) := by
  rw [sendA, send, mem_support_bind_iff] at hout
  obtain ⟨out, hout, hpure⟩ := hout
  cases out with
  | none => simp at hpure
  | some out =>
    rcases out with ⟨key, msg, epoch, state, rand⟩
    simp only [support_pure, Set.mem_singleton_iff, Option.map_some,
      Option.some.injEq, Prod.mk.injEq] at hpure
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hpure
    exact sendWith_support_facts _ _ ecEk ecCt st _ _ _ _ rand hout

/-- The `B` case of `send_support_facts`, for `sendWith` with arbitrary samplers. -/
private theorem sendWithB_support_facts
    {RKey REnc : Type}
    (keygen : ProbComp ((PK × SK) × RKey))
    (encaps : PK → ProbComp ((C × K) × REnc))
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (key? : Option (ℕ × K))
    (ρ : Message Sym) (tsnd : ℕ) (st' : State PK SK C Sym)
    (rand : SendRand RKey REnc)
    (hout : some (key?, ρ, tsnd, st', rand) ∈
      support (sendWith .B keygen encaps ecEk ecCt st)) :
    st'.ack = st.ack ∧ tsnd = st.ack.sendingHorizon ∧
    (st'.res.resEpoch = st.res.resEpoch ∨ st'.res.resEpoch = st.res.resEpoch + 2) ∧
    (key? = none → st'.res.ct = st.res.ct) ∧
    (∀ tI key, key? = some (tI, key) → tI = st'.res.resEpoch.toNat ∧
      st'.res.resEpoch ∉ st.ack.ctRec ∧ st.res.ct = none ∧ st'.res.ct.isSome) := by
  unfold sendWith at hout
  dsimp only at hout
  repeat' first
    | split at hout
    | (rw [mem_support_bind_iff] at hout; obtain ⟨x, _, hout⟩ := hout)
  all_goals simp only [support_pure, Set.mem_singleton_iff,
    Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hout
  all_goals obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hout
  all_goals simp_all [Acknowledgements.sendingHorizon, Role.offset]

/-- A successful supported send keeps the acknowledgements, reports the sending horizon as its
sending epoch, advances the responder epoch by `0` or `2`, keeps the retained ciphertext unless
it emits a key, and emits a key only for the post-send responder epoch, which was unacknowledged,
had no retained ciphertext before the send, and has one after it. -/
theorem send_support_facts
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (key? : Option (ℕ × K))
    (ρ : Message Sym) (tsnd : ℕ) (st' : State PK SK C Sym)
    (hout : some (key?, ρ, tsnd, st') ∈ support (send role kem ecEk ecCt st)) :
    st'.ack = st.ack ∧ tsnd = st.ack.sendingHorizon ∧
    (st'.res.resEpoch = st.res.resEpoch ∨ st'.res.resEpoch = st.res.resEpoch + 2) ∧
    (key? = none → st'.res.ct = st.res.ct) ∧
    (∀ tI key, key? = some (tI, key) → tI = st'.res.resEpoch.toNat ∧
      st'.res.resEpoch ∉ st.ack.ctRec ∧ st.res.ct = none ∧ st'.res.ct.isSome) := by
  cases role with
  | A =>
      exact sendA_support_facts kem ecEk ecCt st key? ρ tsnd st' (by
        simpa only [sendA] using hout)
  | B =>
      rw [send, mem_support_bind_iff] at hout
      obtain ⟨out, hout, hpure⟩ := hout
      cases out with
      | none => simp at hpure
      | some out =>
        rcases out with ⟨key, msg, epoch, state, rand⟩
        simp only [support_pure, Set.mem_singleton_iff, Option.map_some,
          Option.some.injEq, Prod.mk.injEq] at hpure
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hpure
        exact sendWithB_support_facts _ _ ecEk ecCt st _ _ _ _ rand hout

/-- Everything a successful supported send `some (key?, ρ, tsnd, st')` from `st` guarantees about
the outgoing message, the sending epoch, the emitted key, and the post-state. -/
structure SendProvenance
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (key? : Option (ℕ × K))
    (ρ : Message Sym) (tsnd : ℕ) (st' : State PK SK C Sym) : Prop where
  /-- The message carries the post-send responder epoch. -/
  message_resEpoch : ρ.tRes = st'.res.resEpoch
  /-- The message carries the requester epoch, which the send does not change. -/
  message_reqEpoch : ρ.tReq = st.req.reqEpoch
  /-- The reported sending epoch is the one carried by the message. -/
  message_sendingEpoch : tsnd = ρ.sendingEpoch
  /-- The requester epoch is unchanged. -/
  requester_epoch : st'.req.reqEpoch = st.req.reqEpoch
  /-- The decoded peer keys are unchanged. -/
  peer_keys : st'.res.ekPeer = st.res.ekPeer
  /-- The incoming chunk buffer is unchanged. -/
  received_chunks : st'.req.receivedChunks = st.req.receivedChunks
  /-- The acknowledgements are unchanged. -/
  acknowledgements : st'.ack = st.ack
  /-- The reported sending epoch is the sending horizon of the acknowledgements. -/
  sending_horizon : tsnd = st.ack.sendingHorizon
  /-- The message's flags advertise whether `reqEpoch - role.offset ∈ ekRec` and whether
  `reqEpoch ∈ ctRec`. -/
  advertised_acknowledgements :
    ρ.ack.ekRec =
        decide (st.req.reqEpoch - role.offset ∈ st.ack.ekRec) ∧
      ρ.ack.ctRec = decide (st.req.reqEpoch ∈ st.ack.ctRec)
  /-- Either the responder epoch and the own key material are unchanged, or the responder epoch
  advances by two with a fresh supported key pair: its public key is retained, and its secret key
  is recorded at the new key epoch `resEpoch + role.offset`, replacing any older entry there. -/
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
  /-- Without an emitted key the retained ciphertext is unchanged. -/
  no_key_ciphertext : key? = none → st'.res.ct = st.res.ct
  /-- An emitted key `(t, key)` is for the post-send responder epoch `t` and comes with a
  ciphertext message; it is encapsulated, in the support of `kem.encaps pk`, to the decoded peer
  key `pk` for that epoch, and its ciphertext is retained. -/
  emitted_key :
    ∀ (t : ℕ) (key : K), key? = some (t, key) →
      t = st'.res.resEpoch.toNat ∧ ρ.bit = some 1 ∧
      ∃ (pk : PK) (ciphertext : C),
        st.res.ekPeer st'.res.resEpoch = some pk ∧
        (ciphertext, key) ∈ support (kem.encaps pk) ∧
        st'.res.ct = some ciphertext
  /-- A public-key message carries the chunk of the retained public key at the post-send chunk
  index. -/
  public_key_chunk :
    ρ.bit = some 0 →
      ∃ pk : PK,
        st'.req.ek = some pk ∧
        ρ.ch = some (ecEk.encode pk st'.res.ich)
  /-- A ciphertext message carries the chunk of the retained ciphertext at the post-send chunk
  index, or no chunk if no ciphertext is retained. -/
  ciphertext_chunk :
    ρ.bit = some 1 →
      ρ.ch = st'.res.ct.map
        (fun ciphertext => ecCt.encode ciphertext st'.res.ich)
  /-- A message without payload selector carries no chunk. -/
  absent_payload : ρ.bit = none → ρ.ch = none
  /-- The chunk index is reset to `0` by an advance or an emitted key, then incremented once if
  the message has a payload selector. -/
  chunk_counter :
    st'.res.ich =
      (if st'.res.resEpoch = st.res.resEpoch ∧ key? = none then
        st.res.ich else 0) +
        (if ρ.bit = none then 0 else 1)

/-- Every successful supported send satisfies `SendProvenance`. -/
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

/-- A supported send that emits a ciphertext message (`ρ.bit = some 1`) took the `else` branch
of the `sendWith` guard `tRes + role.offset ∉ ack.ekRec`, so the sender's own-key epoch
`ρ.tRes + role.offset` is in the acknowledgements the send read. -/
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
    -- or no payload) lies in the `else` of the guard `tRes + role.offset ∉ ack.ekRec` and
    -- carries its negation.
    all_goals first
      | exact absurd (Option.some.inj hbit) (by decide)
      | exact Decidable.of_not_not ‹_›

/-- If a supported send changes the responder epoch, the advance gate of `sendWith` held:
`resEpoch` and `resEpoch + role.offset` are both in `ctRec`. -/
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

end oppBiKemCKA
