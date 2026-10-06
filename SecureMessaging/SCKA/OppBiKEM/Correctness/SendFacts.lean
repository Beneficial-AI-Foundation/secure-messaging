/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Gavran, Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Construction
import SecureMessaging.SCKA.Correctness.OracleSupport

/-!
# Opp-BiKEM — facts about a single send

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

theorem Acknowledgements.sendingHorizon_mono
    (ack ack' : Acknowledgements)
    (hct : ack.ctRec ⊆ ack'.ctRec) :
    ack.sendingHorizon ≤ ack'.sendingHorizon := by
  unfold sendingHorizon
  apply Finset.sup_mono
  intro t ht
  rw [Finset.mem_filter] at ht ⊢
  exact ⟨hct ht.1, hct ht.2⟩

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
  message_resEpoch : ρ.tRes = st'.res.resEpoch
  message_reqEpoch : ρ.tReq = st.req.reqEpoch
  message_sendingEpoch : tsnd = ρ.sendingEpoch
  requester_epoch : st'.req.reqEpoch = st.req.reqEpoch
  peer_keys : st'.res.ekPeer = st.res.ekPeer
  received_chunks : st'.req.receivedChunks = st.req.receivedChunks
  acknowledgements : st'.ack = st.ack
  sending_horizon : tsnd = st.ack.sendingHorizon
  advertised_acknowledgements :
    ρ.ack.ekRec =
        decide (st.req.reqEpoch - role.offset ∈ st.ack.ekRec) ∧
      ρ.ack.ctRec = decide (st.req.reqEpoch ∈ st.ack.ctRec)
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
  no_key_ciphertext : key? = none → st'.res.ct = st.res.ct
  emitted_key :
    ∀ (t : ℕ) (key : K), key? = some (t, key) →
      t = st'.res.resEpoch.toNat ∧ ρ.bit = some 1 ∧
      ∃ (pk : PK) (ciphertext : C),
        st.res.ekPeer st'.res.resEpoch = some pk ∧
        (ciphertext, key) ∈ support (kem.encaps pk) ∧
        st'.res.ct = some ciphertext
  public_key_chunk :
    ρ.bit = some 0 →
      ∃ pk : PK,
        st'.req.ek = some pk ∧
        ρ.ch = some (ecEk.encode pk st'.res.ich)
  ciphertext_chunk :
    ρ.bit = some 1 →
      ρ.ch = st'.res.ct.map
        (fun ciphertext => ecCt.encode ciphertext st'.res.ich)
  absent_payload : ρ.bit = none → ρ.ch = none
  chunk_counter :
    st'.res.ich =
      (if st'.res.resEpoch = st.res.resEpoch ∧ key? = none then
        st.res.ich else 0) +
        (if ρ.bit = none then 0 else 1)

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

end oppBiKemCKA
