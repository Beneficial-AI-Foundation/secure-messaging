/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Security.Reduction

/-!
# Opp-BiKEM — The injected-state invariant

**Setting.** Fix a target epoch `t > 0` and a *supported honest injection*: a key pair
`(pk, sk) ∈ support kem.keygen` and an encapsulation `(c, k) ∈ support (kem.encaps pk)`. The
injected oracles `injectedSecurityImpl t ⟨pk, sk, c, k⟩ random` (`Reduction`) are the ideal
security oracles whose ordinary sends return `(pk, sk)` at the generation of `t`'s key pair and
`(c, k)` at the encapsulation for `t`, for any challenge selection `random`.

**Main result** (`injectedSecurityImpl_preservesInv_continuing`). With correct erasure codes,
every injected query keeps the *injected-state invariant* `InjInv ⟨pk, sk, c, k⟩` on every
successor that leaves `t` unexposed:

- `GameInv` holds, because on such states the injected send's outputs are outputs of the honest
  send (`injectedSend_support_subset`);
- the target's material is pinned to the injected values wherever the state holds it
  (`TargetInv`): the owner's retained public key while its key epoch is `t`, the owner's
  retained secret for `t`, the peer's decoded key for `t`, and both tables at `t`.

Pinning the key the peer decodes follows from the owner's retained public key, which the owner
clears only after the peer decoded it, together with three state clauses saying that the peer
decoded `t`'s key before any ciphertext for `t` could exist (`ctRec_decoded`, `ctMsg_decoded`,
`ct_decoded`); no transcript tracking is needed.

Successors exposing `t` carry no obligation: an honest leaking send that generates or
encapsulates for `t` stores fresh honest values, and it exposes `t`
(`mem_rleakEpochs_of_target`), so the stopped run discards it before the adversary continues.
The reduction's own injection, with its placeholder secret and candidate key, is related to
these runs by the state map of `Simulation`; the invariant is never claimed for it directly.

The module also provides the state-level facts of one `sendWith` step with arbitrary samplers
(`SendWithFacts`) and of one `recvWith` step (`RecvWithFacts`), and the first-use predicates
`targetGenerated` and `targetEncapsulated` with their monotonicity and first-use lemmas, which
the eager-sampling argument consumes (`Eager`).
-/

open OracleSpec OracleComp KEMScheme

namespace SCKAScheme

/-! ## Support of the leaking-send oracles -/

/-- Support of A's leaking-send query from `s`: a rejection leaves the state unchanged, and an
acceptance is a supported leaking send whose leaked epochs avoid the challenged set, applied as
the ordinary send is, with the leaked epochs exposed. -/
lemma oracleSendArleak_support {IK StA StB I Rho Rand : Type} [DecidableEq I]
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) (leak : StA → Rand → Finset ℕ)
    (s : SCKAScheme.GameState StA StB I Rho)
    (z : Option (ℕ × Option ℕ × Rho × Rand) × SCKAScheme.GameState StA StB I Rho)
    (hz : z ∈ support ((SCKAScheme.oracleSendArleak leak scka ()).run s)) :
    z = (none, s) ∨
      ∃ key? ρ tsnd stA' rand,
        some (key?, ρ, tsnd, stA', rand) ∈ support (scka.sendArleak s.stA) ∧
        leak s.stA rand ∩ s.challenged = ∅ ∧
        z.2 = { SCKAScheme.sendAUpdate s key? ρ tsnd stA' with
          exposed := s.exposed ∪ leak s.stA rand } := by
  simp only [SCKAScheme.oracleSendArleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc] at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨out, hout, hz⟩ := hz
  cases out with
  | none => exact Or.inl (by simpa using (mem_support_pure_iff _ _).mp hz)
  | some out =>
      rcases out with ⟨key, msg, epoch, state, coins⟩
      dsimp only at hz
      split at hz
      · exact Or.inl (by simpa using (mem_support_pure_iff _ _).mp hz)
      · rename_i hvuln
        cases key <;>
          simp only [StateT.run_bind, StateT.run_set, pure_bind,
            StateT.run_pure, mem_support_pure_iff] at hz
        all_goals
          obtain rfl := hz
          exact Or.inr ⟨_, _, _, _, _, hout, not_not.mp hvuln, rfl⟩

/-- The version of `oracleSendArleak_support` for B. -/
lemma oracleSendBrleak_support {IK StA StB I Rho Rand : Type} [DecidableEq I]
    (scka : SCKAScheme ProbComp IK StA StB I Rho Rand) (leak : StB → Rand → Finset ℕ)
    (s : SCKAScheme.GameState StA StB I Rho)
    (z : Option (ℕ × Option ℕ × Rho × Rand) × SCKAScheme.GameState StA StB I Rho)
    (hz : z ∈ support ((SCKAScheme.oracleSendBrleak leak scka ()).run s)) :
    z = (none, s) ∨
      ∃ key? ρ tsnd stB' rand,
        some (key?, ρ, tsnd, stB', rand) ∈ support (scka.sendBrleak s.stB) ∧
        leak s.stB rand ∩ s.challenged = ∅ ∧
        z.2 = { SCKAScheme.sendBUpdate s key? ρ tsnd stB' with
          exposed := s.exposed ∪ leak s.stB rand } := by
  simp only [SCKAScheme.oracleSendBrleak, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, bind_assoc] at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨out, hout, hz⟩ := hz
  cases out with
  | none => exact Or.inl (by simpa using (mem_support_pure_iff _ _).mp hz)
  | some out =>
      rcases out with ⟨key, msg, epoch, state, coins⟩
      dsimp only at hz
      split at hz
      · exact Or.inl (by simpa using (mem_support_pure_iff _ _).mp hz)
      · rename_i hvuln
        cases key <;>
          simp only [StateT.run_bind, StateT.run_set, pure_bind,
            StateT.run_pure, mem_support_pure_iff] at hz
        all_goals
          obtain rfl := hz
          exact Or.inr ⟨_, _, _, _, _, hout, not_not.mp hvuln, rfl⟩

end SCKAScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

/-! ## One `sendWith` step with arbitrary samplers -/

/-- What a successful supported `sendWith` output `some (key?, ρ, tsnd, st', rand)` guarantees,
for arbitrary samplers: the unchanged components, and the generated and encapsulated values with
their support memberships, keyed by the randomness flags. -/
structure SendWithFacts {RK RE : Type} (role : Role)
    (keygen : ProbComp ((PK × SK) × RK)) (encaps : PK → ProbComp ((C × K) × RE))
    (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (key? : Option (ℕ × K)) (ρ : Message Sym)
    (st' : State PK SK C Sym) (rand : SendRand RK RE) : Prop where
  /-- The message carries the post-send responder epoch. -/
  message_resEpoch : ρ.tRes = st'.res.resEpoch
  /-- The decoded peer keys are unchanged. -/
  peer_keys : st'.res.ekPeer = st.res.ekPeer
  /-- The acknowledgements are unchanged. -/
  acknowledgements : st'.ack = st.ack
  /-- With key-generation randomness, a supported key pair was generated: its public key is
  retained and its secret key is recorded at the new key epoch. -/
  keygen : ∀ rk, rand.keygenRand = some rk → ∃ pk sk, ((pk, sk), rk) ∈ support keygen ∧
    st'.req.ek = some pk ∧
    st'.req.dk = (st'.res.resEpoch + role.offset, sk) ::
      st.req.dk.filter (fun p => p.1 != st'.res.resEpoch + role.offset)
  /-- Without key-generation randomness the own key material is unchanged. -/
  no_keygen : rand.keygenRand = none → st'.req.ek = st.req.ek ∧ st'.req.dk = st.req.dk
  /-- With encapsulation randomness, a supported encapsulation to the decoded peer key of the
  post-send responder epoch was performed: its key is emitted and its ciphertext retained. -/
  encaps : ∀ re, rand.encapsRand = some re → ∃ pk c k,
    st.res.ekPeer st'.res.resEpoch = some pk ∧ ((c, k), re) ∈ support (encaps pk) ∧
    key? = some (st'.res.resEpoch.toNat, k) ∧ st'.res.ct = some c
  /-- Without encapsulation randomness no key is emitted and the ciphertext is unchanged. -/
  no_encaps : rand.encapsRand = none → key? = none ∧ st'.res.ct = st.res.ct
  /-- A ciphertext message carries the chunk of the retained ciphertext, if any. -/
  ciphertext_chunk : ρ.bit = some 1 →
    ρ.ch = st'.res.ct.map (fun c => ecCt.encode c st'.res.ich)

/-- Every successful supported `sendWith` output satisfies `SendWithFacts`. -/
lemma sendWith_facts {RK RE : Type} (role : Role)
    (keygen : ProbComp ((PK × SK) × RK)) (encaps : PK → ProbComp ((C × K) × RE))
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (key? : Option (ℕ × K)) (ρ : Message Sym) (tsnd : ℕ)
    (st' : State PK SK C Sym) (rand : SendRand RK RE)
    (hout : some (key?, ρ, tsnd, st', rand) ∈ support (sendWith role keygen encaps ecEk ecCt st)) :
    SendWithFacts role keygen encaps ecCt st key? ρ st' rand := by
  unfold sendWith at hout
  dsimp only at hout
  repeat' first
    | split at hout
    | (rw [mem_support_bind_iff] at hout; obtain ⟨x, hx, hout⟩ := hout)
  all_goals simp only [support_pure, Set.mem_singleton_iff,
    Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hout
  all_goals obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hout
  all_goals constructor <;> simp_all

/-- Support inclusion of a bind from support inclusions of its parts. -/
lemma support_bind_mono {α β : Type} (oa₁ oa₂ : ProbComp α) (f₁ f₂ : α → ProbComp β)
    (h₁ : support oa₁ ⊆ support oa₂)
    (h₂ : ∀ x ∈ support oa₁, support (f₁ x) ⊆ support (f₂ x)) :
    support (oa₁ >>= f₁) ⊆ support (oa₂ >>= f₂) := by
  intro y hy
  rw [mem_support_bind_iff] at hy ⊢
  obtain ⟨x, hx, hy⟩ := hy
  exact ⟨x, h₁ hx, h₂ x hx hy⟩

/-- `sendWith` is monotone in the supports of its samplers: it suffices that the encapsulation
supports are included at the peer key the send reads, the decoded key of the post-advance
responder epoch. -/
lemma sendWith_support_mono {RK RE : Type} (role : Role)
    (keygen₁ keygen₂ : ProbComp ((PK × SK) × RK))
    (encaps₁ encaps₂ : PK → ProbComp ((C × K) × RE))
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym)
    (hk : support keygen₁ ⊆ support keygen₂)
    (he : ∀ pk, st.res.ekPeer (st.res.resEpoch + if sendKeygenGuard role st then 2 else 0) =
      some pk → support (encaps₁ pk) ⊆ support (encaps₂ pk)) :
    support (sendWith role keygen₁ encaps₁ ecEk ecCt st) ⊆
      support (sendWith role keygen₂ encaps₂ ecEk ecCt st) := by
  by_cases hg : sendKeygenGuard role st = true
  · simp only [hg, if_true] at he
    have hc : (st.req.ek.isNone && decide (st.res.resEpoch ∈ st.ack.ctRec ∧
        st.res.resEpoch + role.offset ∈ st.ack.ctRec)) = true := hg
    unfold sendWith
    dsimp only
    rw [if_pos hc, if_pos hc]
    intro y hy
    rw [mem_support_bind_iff] at hy ⊢
    obtain ⟨x, hx, hy⟩ := hy
    refine ⟨x, hk hx, ?_⟩
    rcases x with ⟨⟨pk, sk⟩, r⟩
    dsimp only at hy ⊢
    split_ifs at hy ⊢ <;> (try exact hy)
    generalize hpeer : st.res.ekPeer (st.res.resEpoch + 2) = o at hy ⊢
    cases o with
    | none => exact hy
    | some peerEk =>
      dsimp only at hy ⊢
      rw [mem_support_bind_iff] at hy ⊢
      obtain ⟨z, hz, hy⟩ := hy
      exact ⟨z, he _ hpeer hz, hy⟩
  · have hg' : sendKeygenGuard role st = false := by simpa using hg
    simp only [hg', Bool.false_eq_true, if_false, add_zero] at he
    have hc : ¬ (st.req.ek.isNone && decide (st.res.resEpoch ∈ st.ack.ctRec ∧
        st.res.resEpoch + role.offset ∈ st.ack.ctRec)) = true := hg
    unfold sendWith
    dsimp only
    rw [if_neg hc, if_neg hc]
    intro y hy
    split_ifs at hy ⊢ <;> (try exact hy)
    generalize hpeer : st.res.ekPeer st.res.resEpoch = o at hy ⊢
    cases o with
    | none => exact hy
    | some peerEk =>
      dsimp only at hy ⊢
      rw [mem_support_bind_iff] at hy ⊢
      obtain ⟨z, hz, hy⟩ := hy
      exact ⟨z, he _ hpeer hz, hy⟩

/-- On a state where the target's injected values are supported at the sites that use them, the
injected send's outputs are outputs of the honest send. -/
lemma injectedSend_support_subset (kem : KEMScheme ProbComp K PK SK C) (role : Role)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym) (t : ℕ)
    (inj : TargetInjection PK SK C K) (st : State PK SK C Sym)
    (hgen : sendGeneratesTarget role t st = true → (inj.pk, inj.sk) ∈ support kem.keygen)
    (henc : sendEncapsulatesTarget role t st = true → ∀ pk, st.res.ekPeer (t : ℤ) = some pk →
      (inj.ct, inj.key) ∈ support (kem.encaps pk)) :
    support (injectedSend kem role ecEk ecCt t inj st) ⊆ support (send role kem ecEk ecCt st) := by
  unfold injectedSend send
  refine support_bind_mono _ _ _ _
    (sendWith_support_mono role _ _ _ _ ecEk ecCt st ?_ ?_) fun _ _ => subset_rfl
  · intro x hx
    unfold injectedKeygen at hx
    split_ifs at hx with h
    · simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx
      rw [mem_support_bind_iff]
      exact ⟨_, hgen h, by simp⟩
    · exact hx
  · intro pk hpk x hx
    unfold injectedEncaps at hx
    split_ifs at hx with h
    · simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx
      simp only [sendEncapsulatesTarget, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.2] at hpk
      rw [mem_support_bind_iff]
      exact ⟨_, henc (by simp [sendEncapsulatesTarget, h.1, h.2]) pk hpk, by simp⟩
    · exact hx

/-- A supported leaking send that generates or encapsulates for the positive epoch `t` leaks
`t`. -/
lemma mem_rleakEpochs_of_target {RK RE : Type} (role : Role)
    (keygen : ProbComp ((PK × SK) × RK)) (encaps : PK → ProbComp ((C × K) × RE))
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (key? : Option (ℕ × K)) (ρ : Message Sym) (tsnd : ℕ)
    (st' : State PK SK C Sym) (rand : SendRand RK RE)
    (hout : some (key?, ρ, tsnd, st', rand) ∈ support (sendWith role keygen encaps ecEk ecCt st))
    (t : ℕ) (ht : 0 < t)
    (h : sendGeneratesTarget role t st = true ∨ sendEncapsulatesTarget role t st = true) :
    t ∈ rleakEpochs role st rand := by
  obtain ⟨hkey, henc, -⟩ :=
    sendWith_operation_facts role keygen encaps ecEk ecCt st key? ρ tsnd st' rand hout
  rw [mem_rleakEpochs_iff]
  refine ⟨ht, ?_⟩
  rcases h with h | h
  · simp only [sendGeneratesTarget, Bool.and_eq_true, decide_eq_true_eq] at h
    exact Or.inl ⟨hkey.trans h.1, h.2.symm⟩
  · simp only [sendEncapsulatesTarget, Bool.and_eq_true, decide_eq_true_eq] at h
    refine Or.inr ⟨henc.trans h.1, ?_⟩
    rw [hkey]
    exact h.2.symm

/-! ## One `recvWith` step -/

/-- What a successful `recvWith` output `some (key?, trcv, st')` guarantees about the state
change: the responder epoch is kept, own material is kept or cleared, decoded peer keys are
kept and at most one is added, secret keys only disappear, ciphertext acknowledgements grow by
the message's flag and by the decapsulated epoch, and an emitted key comes from the recovery
function at the decapsulated epoch. -/
structure RecvWithFacts (role : Role) (recover : ℤ → SK → C → Option K)
    (st : State PK SK C Sym) (ρ : Message Sym) (key? : Option (ℕ × K))
    (st' : State PK SK C Sym) : Prop where
  /-- The responder epoch is unchanged. -/
  resEpoch : st'.res.resEpoch = st.res.resEpoch
  /-- The own public key is kept or cleared. -/
  ek : st'.req.ek = st.req.ek ∨ st'.req.ek = none
  /-- The retained ciphertext is kept, or cleared once the responder epoch is acknowledged. -/
  ct : st'.res.ct = st.res.ct ∨ (st'.res.ct = none ∧ st.res.resEpoch ∈ st'.ack.ctRec)
  /-- Ciphertext acknowledgements grow. -/
  ctRec_mono : st.ack.ctRec ⊆ st'.ack.ctRec
  /-- Decoded peer keys are kept. -/
  ekPeer_stable : ∀ e, (st.res.ekPeer e).isSome = true → st'.res.ekPeer e = st.res.ekPeer e
  /-- A decoded peer key was present before, or was decoded now from a public-key message at
  the new requester epoch's peer key epoch. -/
  ekPeer_new : ∀ e pk, st'.res.ekPeer e = some pk → st.res.ekPeer e = some pk ∨
    (st.res.ekPeer e = none ∧ ¬ ρ.tRes < st.req.reqEpoch ∧ ρ.bit = some 0 ∧
      e = recvReq st ρ - role.offset)
  /-- Secret keys only disappear. -/
  dk_subset : ∀ p, p ∈ st'.req.dk → p ∈ st.req.dk
  /-- A ciphertext acknowledgement was present, comes from the message's flag, or is the
  decapsulated epoch. -/
  ctRec : ∀ e, e ∈ st'.ack.ctRec → e ∈ st.ack.ctRec ∨ (ρ.ack.ctRec = true ∧ e = ρ.tReq) ∨
    (e = recvReq st ρ ∧ key?.isSome = true)
  /-- An emitted key is recovered at the new requester epoch from a non-stale ciphertext message
  carrying a chunk. -/
  key : ∀ tI k, key? = some (tI, k) → ¬ ρ.tRes < st.req.reqEpoch ∧ ρ.bit = some 1 ∧
    ρ.ch.isSome = true ∧ tI = (recvReq st ρ).toNat ∧
    ∃ sk c, st.req.dk.lookup (recvReq st ρ) = some sk ∧ recover (recvReq st ρ) sk c = some k

/-- Every successful `recvWith` output satisfies `RecvWithFacts`. -/
lemma recvWith_facts (role : Role) [DecidableEq Sym] (recover : ℤ → SK → C → Option K)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym)
    (key? : Option (ℕ × K)) (trcv : ℕ) (st' : State PK SK C Sym)
    (hout : recvWith role recover ecEk ecCt st ρ = some (key?, trcv, st')) :
    RecvWithFacts role recover st ρ key? st' := by
  have hack : ∀ e, e ∈ (recvAck role st.ack ρ).ctRec →
      e ∈ st.ack.ctRec ∨ (ρ.ack.ctRec = true ∧ e = ρ.tReq) := by
    intro e he
    simp only [recvAck] at he
    split_ifs at he with h
    · rcases Finset.mem_insert.1 he with rfl | he
      · exact Or.inr ⟨h, rfl⟩
      · exact Or.inl he
    · exact Or.inl he
  dsimp only [recvWith] at hout
  split_ifs at hout with hst hpk hct
  · simp only [Option.some.injEq, Prod.mk.injEq] at hout
    obtain ⟨rfl, -, rfl⟩ := hout
    exact ⟨rfl, Or.inl rfl, Or.inl rfl, recvAck_ctRec_subset role st.ack ρ, fun _ _ => rfl,
      fun e pk h => Or.inl h, fun _ h => h, fun e he => (hack e he).imp_right Or.inl,
      fun _ _ h => by cases h⟩
  · split at hout <;> simp only [Option.some.injEq, Prod.mk.injEq] at hout <;>
      obtain ⟨rfl, -, rfl⟩ := hout
    · refine ⟨rfl, ?_, ?_, recvAck_ctRec_subset role st.ack ρ, fun _ _ => rfl,
        fun e pk h => Or.inl h, fun _ h => h, fun e he => (hack e he).imp_right Or.inl,
        fun _ _ h => by cases h⟩
      · simp only [recvFinish]; split_ifs <;> simp
      · simp only [recvFinish]; split_ifs with h <;> simp [h]
    · rename_i pk hdec
      refine ⟨rfl, ?_, ?_, recvAck_ctRec_subset role st.ack ρ, ?_, ?_, fun _ h => h, ?_,
        fun _ _ h => by cases h⟩
      · simp only [recvFinish]; split_ifs <;> simp
      · simp only [recvFinish]; split_ifs with h <;> simp [h]
      · intro e he
        simp only [recvFinish, Function.update_apply]
        split_ifs with h
        · exfalso
          subst h
          obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp he
          rw [hv] at hpk
          simp at hpk
        · rfl
      · intro e pk' h
        simp only [recvFinish, Function.update_apply] at h
        split_ifs at h with h'
        · subst h'
          exact Or.inr ⟨by simpa using hpk.1, hst, hpk.2, rfl⟩
        · exact Or.inl h
      · intro e he
        exact (hack e he).imp_right Or.inl
  · split at hout <;> (try simp only [Option.some.injEq, Prod.mk.injEq] at hout)
    · obtain ⟨rfl, -, rfl⟩ := hout
      refine ⟨rfl, ?_, ?_, recvAck_ctRec_subset role st.ack ρ, fun _ _ => rfl,
        fun e pk h => Or.inl h, fun _ h => h, fun e he => (hack e he).imp_right Or.inl,
        fun _ _ h => by cases h⟩
      · simp only [recvFinish]; split_ifs <;> simp
      · simp only [recvFinish]; split_ifs with h <;> simp [h]
    · rename_i c hdec
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
        Prod.mk.injEq] at hout
      obtain ⟨sk, hsk, k, hk, rfl, -, rfl⟩ := hout
      refine ⟨rfl, ?_, ?_, (recvAck_ctRec_subset role st.ack ρ).trans (Finset.subset_insert _ _),
        fun _ _ => rfl, fun e pk h => Or.inl h, ?_, ?_, ?_⟩
      · simp only [recvFinish]; split_ifs <;> simp
      · simp only [recvFinish]; split_ifs with h <;> simp [h]
      · intro p hp
        simp only [recvFinish, List.mem_filter] at hp
        exact hp.1
      · intro e he
        simp only [recvFinish] at he
        rcases Finset.mem_insert.1 he with rfl | he
        · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
        · exact (hack e he).imp_right Or.inl
      · intro tI k' h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨hst, hct.2, ?_, rfl, sk, c, hsk, hk⟩
        cases hch : ρ.ch with
        | none => simp [insertChunkAndDecode, hch] at hdec
        | some ch => rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at hout
    obtain ⟨rfl, -, rfl⟩ := hout
    refine ⟨rfl, ?_, ?_, recvAck_ctRec_subset role st.ack ρ, fun _ _ => rfl, fun e pk h => Or.inl h,
      fun _ h => h, fun e he => (hack e he).imp_right Or.inl, fun _ _ h => by cases h⟩
    · simp only [recvFinish]; split_ifs <;> simp
    · simp only [recvFinish]; split_ifs with h <;> simp [h]

/-! ## The target epoch's owner and the pinning invariant -/

/-- The owner of key epoch `t`: `A` for even `t`, `B` for odd `t`. -/
def targetOwner (t : ℕ) : Role := if t % 2 = 0 then .A else .B

/-- The target epoch has its owner's requester parity. -/
lemma targetOwner_parity (t : ℕ) : (t : ℤ) % 2 = (targetOwner t).reqParity := by
  unfold targetOwner
  split_ifs with h <;> simp only [Role.reqParity] <;> omega

/-- A positive integer with a positive `toNat` is that natural number. -/
lemma eq_of_toNat_eq_of_pos {m : ℤ} {n : ℕ} (hn : 0 < n) (h : m.toNat = n) : m = n := by
  rcases le_or_gt 0 m with hm | hm
  · rw [← h, Int.toNat_of_nonneg hm]
  · rw [Int.toNat_of_nonpos hm.le] at h
    omega

/-- The pinning invariant for target epoch `t` owned by `role`, on the owner's state `own`, the
peer's state `peer`, the peer's outgoing messages, and the owner's and peer's key tables.
Every clause is a fact about the current state; the three `_decoded` clauses record that the
peer decoded the target's public key before any ciphertext for `t` could exist, which is what
pins the key the peer decodes to the injected one. -/
structure TargetInv (role : Role) (t : ℕ) (inj : TargetInjection PK SK C K)
    (own peer : State PK SK C Sym) (peerMsgs : ℕ → Option (Message Sym × ℕ))
    (ownKey peerKey : ℕ → Option K) : Prop where
  /-- While the owner's key epoch is `t`, its retained public key is the injected one. -/
  ek_pinned : own.res.resEpoch + role.offset = t → ∀ pk, own.req.ek = some pk → pk = inj.pk
  /-- The peer's decoded key for `t` is the injected one. -/
  ekPeer_pinned : ∀ pk, peer.res.ekPeer t = some pk → pk = inj.pk
  /-- The owner's retained secret for `t` is the injected one. -/
  secret_pinned : ∀ sk, ((t : ℤ), sk) ∈ own.req.dk → sk = inj.sk
  /-- The owner's table at `t` is empty or the injected key. -/
  table_own : ownKey t = none ∨ ownKey t = some inj.key
  /-- The peer's table at `t` is empty or the injected key. -/
  table_peer : peerKey t = none ∨ peerKey t = some inj.key
  /-- Once the owner acknowledges `t`'s ciphertext, the peer has decoded `t`'s public key. -/
  ctRec_decoded : (t : ℤ) ∈ own.ack.ctRec → (peer.res.ekPeer t).isSome = true
  /-- Once the peer recorded a ciphertext chunk for `t`, it has decoded `t`'s public key. -/
  ctMsg_decoded : ∀ n ρ tsnd, peerMsgs n = some (ρ, tsnd) → ρ.tRes = t → ρ.bit = some 1 →
    ρ.ch.isSome = true → (peer.res.ekPeer t).isSome = true
  /-- Once the peer retains a ciphertext at responder epoch `t`, it has decoded `t`'s public
  key. -/
  ct_decoded : peer.res.resEpoch = t → peer.res.ct.isSome = true →
    (peer.res.ekPeer t).isSome = true

/-- The injected-state invariant for target `t`: `GameInv` and the pinning invariant for the
target's owner. -/
def InjInv (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (t : ℕ) (inj : TargetInjection PK SK C K)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) : Prop :=
  GameInv kem ecEk ecCt s ∧
    match targetOwner t with
    | .A => TargetInv .A t inj s.stA s.stB s.msgB s.keyA s.keyB
    | .B => TargetInv .B t inj s.stB s.stA s.msgA s.keyB s.keyA

/-- `InjInv` when `A` owns the target. -/
lemma injInv_A {kem : KEMScheme ProbComp K PK SK C}
    {ecEk : ErasureCodePayload PK Sym} {ecCt : ErasureCodePayload C Sym}
    {t : ℕ} {inj : TargetInjection PK SK C K}
    {s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)}
    (ho : targetOwner t = .A) :
    InjInv kem ecEk ecCt t inj s ↔
      GameInv kem ecEk ecCt s ∧ TargetInv .A t inj s.stA s.stB s.msgB s.keyA s.keyB := by
  simp only [InjInv, ho]

/-- `InjInv` when `B` owns the target. -/
lemma injInv_B {kem : KEMScheme ProbComp K PK SK C}
    {ecEk : ErasureCodePayload PK Sym} {ecCt : ErasureCodePayload C Sym}
    {t : ℕ} {inj : TargetInjection PK SK C K}
    {s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)}
    (ho : targetOwner t = .B) :
    InjInv kem ecEk ecCt t inj s ↔
      GameInv kem ecEk ecCt s ∧ TargetInv .B t inj s.stB s.stA s.msgA s.keyB s.keyA := by
  simp only [InjInv, ho]

/-- `InjInv` holds at the initial game state, for every positive target and every injection:
no material, message, key or positive acknowledgement is present. -/
lemma injInv_init (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (t : ℕ) (ht : 0 < t) (inj : TargetInjection PK SK C K) :
    InjInv kem ecEk ecCt t inj
      (initState (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym)) := by
  refine ⟨gameInv_init kem ecEk ecCt _ _ (by simp [initA, init, initialState])
    (by simp [initB, init, initialState]), ?_⟩
  have hinit : ∀ role role', TargetInv role t inj (initialState (Sym := Sym) role')
      (initialState (Sym := Sym) role'.peer) (fun _ => none) (fun _ => none) (fun _ => none) := by
    intro role role'
    refine ⟨fun _ pk h => by simp [initialState] at h, fun pk h => by simp [initialState] at h,
      fun sk h => by simp [initialState] at h, Or.inl rfl, Or.inl rfl, fun h => ?_,
      fun n ρ tsnd h => by simp at h, fun h => ?_⟩
    · simp only [initialState, Finset.mem_insert, Finset.mem_singleton] at h
      omega
    · cases role' <;> simp [initialState] at h <;> omega
  rcases targetOwner t with _ | _
  · exact hinit .A .A
  · exact hinit .B .B

/-! ## Parity: the wrong party never touches the target -/

/-- A party whose requester parity is `t`'s never encapsulates for `t`. -/
lemma sendEncapsulatesTarget_eq_false_of_parity (role : Role) (t : ℕ)
    (st : State PK SK C Sym) (htpar : (t : ℤ) % 2 = role.reqParity)
    (hpar : st.res.resEpoch % 2 = role.resParity) :
    sendEncapsulatesTarget role t st = false := by
  rw [Bool.eq_false_iff]
  intro h
  simp only [sendEncapsulatesTarget, Bool.and_eq_true, decide_eq_true_eq] at h
  have := Role.reqParity_ne_resParity role
  split_ifs at h <;> omega

/-- A party whose responder parity is `t`'s never generates the key pair of `t`. -/
lemma sendGeneratesTarget_eq_false_of_parity (role : Role) (t : ℕ)
    (st : State PK SK C Sym) (htpar : (t : ℤ) % 2 = role.resParity)
    (hpar : st.res.resEpoch % 2 = role.resParity) :
    sendGeneratesTarget role t st = false := by
  rw [Bool.eq_false_iff]
  intro h
  simp only [sendGeneratesTarget, Bool.and_eq_true, decide_eq_true_eq] at h
  have := Role.offset_parity role (st.res.resEpoch + 2)
  have := Role.reqParity_ne_resParity role
  omega

/-! ## Preservation of the pinning invariant, per state transition -/

namespace TargetInv

variable {role : Role} {t : ℕ} {inj : TargetInjection PK SK C K}
  {own peer : State PK SK C Sym} {peerMsgs : ℕ → Option (Message Sym × ℕ)}
  {ownKey peerKey : ℕ → Option K}

/-- The owner's send keeps the pinning invariant, provided a generation of `t`'s key pair
generates the injected pair. -/
lemma ownSend {RK RE : Type} (h : TargetInv role t inj own peer peerMsgs ownKey peerKey)
    (ht : 0 < t) (htpar : (t : ℤ) % 2 = role.reqParity)
    (hpar : own.res.resEpoch % 2 = role.resParity)
    {keygen : ProbComp ((PK × SK) × RK)} {encaps : PK → ProbComp ((C × K) × RE)}
    {ecEk : ErasureCodePayload PK Sym} {ecCt : ErasureCodePayload C Sym}
    {key? : Option (ℕ × K)} {ρ : Message Sym} {tsnd : ℕ} {own' : State PK SK C Sym}
    {rand : SendRand RK RE}
    (hout : some (key?, ρ, tsnd, own', rand) ∈ support (sendWith role keygen encaps ecEk ecCt own))
    (hgen : sendGeneratesTarget role t own = true → ∀ pk sk rk,
      ((pk, sk), rk) ∈ support keygen → pk = inj.pk ∧ sk = inj.sk) :
    TargetInv role t inj own' peer peerMsgs (recordKey ownKey key?) peerKey := by
  have f := sendWith_facts role keygen encaps ecEk ecCt own key? ρ tsnd own' rand hout
  obtain ⟨hkflag, -, hres, -, -, -⟩ :=
    sendWith_operation_facts role keygen encaps ecEk ecCt own key? ρ tsnd own' rand hout
  have hsite : ∀ rk, rand.keygenRand = some rk → own'.res.resEpoch + role.offset = t →
      ∀ pk sk, ((pk, sk), rk) ∈ support keygen → pk = inj.pk ∧ sk = inj.sk := by
    intro rk hrk hk pk sk hmem
    refine hgen ?_ pk sk rk hmem
    have hg : sendKeygenGuard role own = true := by rw [← hkflag, hrk]; rfl
    rw [hres, hrk] at hk
    simp only [sendGeneratesTarget, hg, Bool.true_and, decide_eq_true_eq]
    simpa using hk
  refine ⟨?_, h.ekPeer_pinned, ?_, ?_, h.table_peer, ?_, h.ctMsg_decoded, h.ct_decoded⟩
  · intro hk pk hek
    cases hrk : rand.keygenRand with
    | none =>
      obtain ⟨hek', -⟩ := f.no_keygen hrk
      rw [hres, hrk] at hk
      simp only [Option.isSome_none, Bool.false_eq_true, if_false, add_zero] at hk
      rw [hek'] at hek
      exact h.ek_pinned hk pk hek
    | some rk =>
      obtain ⟨pk₀, sk₀, hmem, hek', -⟩ := f.keygen rk hrk
      rw [hek'] at hek
      obtain rfl := Option.some.inj hek
      exact (hsite rk hrk hk pk₀ sk₀ hmem).1
  · intro sk hmem
    cases hrk : rand.keygenRand with
    | none =>
      obtain ⟨-, hdk⟩ := f.no_keygen hrk
      rw [hdk] at hmem
      exact h.secret_pinned sk hmem
    | some rk =>
      obtain ⟨pk₀, sk₀, hmem₀, -, hdk⟩ := f.keygen rk hrk
      rw [hdk] at hmem
      rcases List.mem_cons.1 hmem with heq | hmem'
      · simp only [Prod.mk.injEq] at heq
        obtain ⟨hk, hsk⟩ := heq
        rw [hsk]
        exact (hsite rk hrk hk.symm pk₀ sk₀ hmem₀).2
      · exact h.secret_pinned sk (List.mem_filter.1 hmem').1
  · cases hre : rand.encapsRand with
    | none =>
      rw [(f.no_encaps hre).1]
      exact h.table_own
    | some re =>
      obtain ⟨-, -, k, -, -, hkey, -⟩ := f.encaps re hre
      rw [hkey, recordKey_some]
      by_cases htI : own'.res.resEpoch.toNat = t
      · exfalso
        have hres' : own'.res.resEpoch % 2 = role.resParity := by
          rw [hres]; split_ifs <;> omega
        rw [eq_of_toNat_eq_of_pos ht htI] at hres'
        have := Role.reqParity_ne_resParity role
        omega
      · rw [Function.update_of_ne (Ne.symm htI)]
        exact h.table_own
  · intro hmem
    rw [f.acknowledgements] at hmem
    exact h.ctRec_decoded hmem

/-- The peer's send keeps the pinning invariant, provided an encapsulation for `t` emits the
injected key. -/
lemma peerSend {RK RE : Type} (h : TargetInv role t inj own peer peerMsgs ownKey peerKey)
    (ht : 0 < t) (hct_acked : peer.res.resEpoch ∈ peer.ack.ctRec → peer.res.ct = none)
    {keygen : ProbComp ((PK × SK) × RK)} {encaps : PK → ProbComp ((C × K) × RE)}
    {ecEk : ErasureCodePayload PK Sym} {ecCt : ErasureCodePayload C Sym}
    {key? : Option (ℕ × K)} {ρ : Message Sym} {tsnd : ℕ} {peer' : State PK SK C Sym}
    {rand : SendRand RK RE} (n : ℕ)
    (hout : some (key?, ρ, tsnd, peer', rand) ∈
      support (sendWith role.peer keygen encaps ecEk ecCt peer))
    (henc : sendEncapsulatesTarget role.peer t peer = true → ∀ pk c k re,
      ((c, k), re) ∈ support (encaps pk) → k = inj.key) :
    TargetInv role t inj own peer' (Function.update peerMsgs n (some (ρ, tsnd))) ownKey
      (recordKey peerKey key?) := by
  have f := sendWith_facts role.peer keygen encaps ecEk ecCt peer key? ρ tsnd peer' rand hout
  obtain ⟨hkflag, heflag, hres, -, -, -⟩ :=
    sendWith_operation_facts role.peer keygen encaps ecEk ecCt peer key? ρ tsnd peer' rand hout
  have hdecoded : peer'.res.resEpoch = t → peer'.res.ct.isSome = true →
      (peer.res.ekPeer t).isSome = true := by
    intro hr hct
    cases hre : rand.encapsRand with
    | some re =>
      obtain ⟨pk, -, -, hpk, -, -, -⟩ := f.encaps re hre
      rw [hr] at hpk
      rw [hpk]
      rfl
    | none =>
      obtain ⟨-, hct'⟩ := f.no_encaps hre
      rw [hct'] at hct
      cases hrk : rand.keygenRand with
      | none =>
        rw [hres, hrk] at hr
        simp only [Option.isSome_none, Bool.false_eq_true, if_false, add_zero] at hr
        exact h.ct_decoded hr hct
      | some rk =>
        exfalso
        have hg : sendKeygenGuard role.peer peer = true := by rw [← hkflag, hrk]; rfl
        simp only [sendKeygenGuard, Bool.and_eq_true, decide_eq_true_eq] at hg
        rw [hct_acked hg.2.1] at hct
        cases hct
  refine ⟨h.ek_pinned, ?_, h.secret_pinned, h.table_own, ?_, ?_, ?_, ?_⟩
  · intro pk hpk
    rw [f.peer_keys] at hpk
    exact h.ekPeer_pinned pk hpk
  · cases hre : rand.encapsRand with
    | none =>
      rw [(f.no_encaps hre).1]
      exact h.table_peer
    | some re =>
      obtain ⟨pk, c, k, -, hmem, hkey, -⟩ := f.encaps re hre
      rw [hkey, recordKey_some]
      by_cases htI : peer'.res.resEpoch.toNat = t
      · rw [htI, Function.update_self]
        right
        refine congrArg some (henc ?_ pk c k re hmem)
        have hg : sendEncapsGuard role.peer peer = true := by rw [← heflag, hre]; rfl
        simp only [sendEncapsulatesTarget, hg, Bool.true_and, decide_eq_true_eq]
        rw [← eq_of_toNat_eq_of_pos ht htI, hres, hkflag]
      · rw [Function.update_of_ne (Ne.symm htI)]
        exact h.table_peer
  · intro hmem
    rw [f.peer_keys]
    exact h.ctRec_decoded hmem
  · intro n' ρ' tsnd' hmsg htres hbit hch
    rw [f.peer_keys]
    rcases eq_or_ne n' n with rfl | hne
    · rw [Function.update_self] at hmsg
      simp only [Option.some.injEq, Prod.mk.injEq] at hmsg
      obtain ⟨rfl, -⟩ := hmsg
      rw [f.message_resEpoch] at htres
      refine hdecoded htres ?_
      rw [f.ciphertext_chunk hbit] at hch
      cases hc : peer'.res.ct with
      | none => rw [hc] at hch; simp at hch
      | some => rfl
    · rw [Function.update_of_ne hne] at hmsg
      exact h.ctMsg_decoded n' ρ' tsnd' hmsg htres hbit hch
  · intro hr hct
    rw [f.peer_keys]
    exact hdecoded hr hct

/-- The owner's ideal receive of the peer's message keeps the pinning invariant. -/
lemma ownRecv [DecidableEq Sym] (h : TargetInv role t inj own peer peerMsgs ownKey peerKey)
    (htpar : (t : ℤ) % 2 = role.reqParity)
    {ecEk : ErasureCodePayload PK Sym} {ecCt : ErasureCodePayload C Sym}
    {n : ℕ} {ρ : Message Sym} {tsnd : ℕ} (hmsg : peerMsgs n = some (ρ, tsnd))
    (hreq : ρ.tReq % 2 = role.resParity)
    (hq : ¬ ρ.tRes < own.req.reqEpoch → recvReq own ρ = ρ.tRes)
    {key? : Option (ℕ × K)} {trcv : ℕ} {own' : State PK SK C Sym}
    (hout : recvWith role (idealRecover peerKey) ecEk ecCt own ρ = some (key?, trcv, own')) :
    TargetInv role t inj own' peer peerMsgs (recordKey ownKey key?) peerKey := by
  have f := recvWith_facts role (idealRecover peerKey) ecEk ecCt own ρ key? trcv own' hout
  refine ⟨?_, h.ekPeer_pinned, ?_, ?_, h.table_peer, ?_, h.ctMsg_decoded, h.ct_decoded⟩
  · intro hk pk hek
    rw [f.resEpoch] at hk
    rcases f.ek with hek' | hek'
    · rw [hek'] at hek
      exact h.ek_pinned hk pk hek
    · rw [hek'] at hek
      cases hek
  · intro sk hmem
    exact h.secret_pinned sk (f.dk_subset _ hmem)
  · rcases key? with _ | ⟨tI, k⟩
    · exact h.table_own
    · obtain ⟨-, -, -, rfl, sk, c, -, hk⟩ := f.key tI k rfl
      rw [recordKey_some]
      by_cases htI : (recvReq own ρ).toNat = t
      · rw [htI, Function.update_self]
        right
        simp only [idealRecover, htI] at hk
        rcases h.table_peer with h' | h'
        · rw [h'] at hk
          cases hk
        · rw [h'] at hk
          exact hk.symm
      · rw [Function.update_of_ne (Ne.symm htI)]
        exact h.table_own
  · intro hmem
    rcases f.ctRec _ hmem with hmem | ⟨-, heq⟩ | ⟨heq, hsome⟩
    · exact h.ctRec_decoded hmem
    · exfalso
      have := Role.reqParity_ne_resParity role
      omega
    · obtain ⟨⟨tI, k⟩, hk⟩ := Option.isSome_iff_exists.mp hsome
      obtain ⟨hns, hbit, hch, -⟩ := f.key tI k hk
      rw [hq hns] at heq
      exact h.ctMsg_decoded n ρ tsnd hmsg heq.symm hbit hch

/-- The peer's ideal receive of the owner's message keeps the pinning invariant, on a state
satisfying `GameInv`. A key the peer decodes for `t` now is the transcript's, which the owner's
retained public key pins while the owner's key epoch is `t`; the owner cannot have moved past
`t` without acknowledging its ciphertext, which presupposes the decoding. -/
lemma peerRecv [DecidableEq Sym] {kem : KEMScheme ProbComp K PK SK C}
    {ecEk : ErasureCodePayload PK Sym} {ecCt : ErasureCodePayload C Sym}
    (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct)
    {T : Transcript kem} {ownMsgs : ℕ → Option (Message Sym × ℕ)} {tcurO tcurP : ℕ}
    (hO : PartyInv role ecEk ecCt T own peer ownMsgs ownKey peerKey tcurO)
    (hP : PartyInv role.peer ecEk ecCt T peer own peerMsgs peerKey ownKey tcurP)
    (h : TargetInv role t inj own peer peerMsgs ownKey peerKey)
    (ht : 0 < t) (htpar : (t : ℤ) % 2 = role.reqParity)
    {n : ℕ} {ρ : Message Sym} {tsnd : ℕ} (hmsg : ownMsgs n = some (ρ, tsnd))
    {key? : Option (ℕ × K)} {trcv : ℕ} {peer' : State PK SK C Sym}
    (hout : recvWith role.peer (idealRecover ownKey) ecEk ecCt peer ρ =
      some (key?, trcv, peer')) :
    TargetInv role t inj own peer' peerMsgs ownKey (recordKey peerKey key?) := by
  have f := recvWith_facts role.peer (idealRecover ownKey) ecEk ecCt peer ρ key? trcv peer' hout
  have hO' : PartyInv role.peer.peer ecEk ecCt T own peer ownMsgs ownKey peerKey tcurO := by
    rw [Role.peer_peer]; exact hO
  have hpar : ρ.tRes % 2 = role.peer.reqParity := recv_tRes_parity (roleR := role.peer) hO' hmsg
  have hparO : ρ.tRes % 2 = role.resParity := by simpa using hpar
  have hrec : ρ.tRes ∉ peer.ack.ctRec → ∀ pk sk c k, (T ρ.tRes).keypair = some (pk, sk) →
      (T ρ.tRes).enc = some (c, k) → idealRecover ownKey ρ.tRes sk c = some k := by
    intro _ pk sk c k hkp henc
    have hpos : 0 < ρ.tRes := hP.keypair_pos _ hpar (by rw [hkp]; rfl)
    change ownKey ρ.tRes.toNat = some k
    rw [hO.key_res _ hpos hparO, EpochTranscript.key, henc]
    rfl
  obtain ⟨-, hall⟩ := partyInv_recvWith_step hP hO' hmsg hEk hCt (idealRecover ownKey) hrec
  obtain ⟨-, -, -, hP', -⟩ := hall key? trcv peer' hout
  have hstable : ∀ e, (peer.res.ekPeer e).isSome = true → (peer'.res.ekPeer e).isSome = true :=
    fun e he => by rw [f.ekPeer_stable e he]; exact he
  refine ⟨h.ek_pinned, ?_, h.secret_pinned, h.table_own, ?_,
    fun hm => hstable t (h.ctRec_decoded hm),
    fun n' ρ' tsnd' hm htres hbit hch =>
      hstable t (h.ctMsg_decoded n' ρ' tsnd' hm htres hbit hch), ?_⟩
  · intro pk hpk
    rcases f.ekPeer_new t pk hpk with hold | ⟨hnone, hns, -, hpe⟩
    · exact h.ekPeer_pinned pk hold
    obtain ⟨sk, hkp⟩ := hP'.ekPeer_T t pk hpk
    have hq := recvReq_eq_tRes hP hO' hmsg hns
    have hres_le : ρ.tRes ≤ own.res.resEpoch := (hO.msgs n ρ tsnd hmsg).res_le
    have hpe' : (t : ℤ) = ρ.tRes + role.offset := by
      rw [hpe, hq, Role.peer_offset]; ring
    rcases lt_or_eq_of_le (show (t : ℤ) ≤ own.res.resEpoch + role.offset by omega) with
      hlt | heq
    · exfalso
      have hmem : (t : ℤ) ∈ own.ack.ctRec := by
        by_contra hnot
        have hdk := hO.T_dk t pk sk hkp htpar hnot
        rcases hO.dk_shape with hnil | ⟨sk', hone⟩
        · rw [hnil] at hdk
          cases hdk
        · rw [hone] at hdk
          simp only [List.mem_singleton, Prod.mk.injEq] at hdk
          omega
      have := h.ctRec_decoded hmem
      rw [hnone] at this
      cases this
    · cases hek : own.req.ek with
      | some pk' =>
        obtain ⟨sk', hkp'⟩ := hO.ek_T pk' hek
        rw [← heq, hkp] at hkp'
        simp only [Option.some.injEq, Prod.mk.injEq] at hkp'
        exact hkp'.1.trans (h.ek_pinned heq.symm pk' hek)
      | none =>
        exfalso
        rcases hO.ek_acked hek with hnone' | hack
        · rw [← heq, hkp] at hnone'
          cases hnone'
        · rw [← heq] at hack
          have := hO.ekRec_req t hack htpar
          rw [hnone] at this
          cases this
  · rcases key? with _ | ⟨tI, k⟩
    · exact h.table_peer
    · obtain ⟨hns, -, -, rfl, -⟩ := f.key tI k rfl
      rw [recordKey_some]
      have hq := recvReq_eq_tRes hP hO' hmsg hns
      have hne : (recvReq peer ρ).toNat ≠ t := by
        intro heq
        have := eq_of_toNat_eq_of_pos ht heq
        have := Role.reqParity_ne_resParity role
        omega
      rw [Function.update_of_ne (Ne.symm hne)]
      exact h.table_peer
  · intro hr hct
    rw [f.resEpoch] at hr
    refine hstable t (h.ct_decoded hr ?_)
    rcases f.ct with hc | ⟨hc, -⟩
    · rwa [hc] at hct
    · rw [hc] at hct
      cases hct

end TargetInv

/-! ## Preservation of `InjInv` on continuing successors -/

section Preservation

variable [DecidableEq K] [DecidableEq Sym]
  (kem : KEMScheme ProbComp K PK SK C) (hDet : kem.DeterministicDecaps)
  (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
  (hEk : ecEk.ec.Correct) (hCt : ecCt.ec.Correct) (leak : kem.RandLeak)
  (t : ℕ) (inj : TargetInjection PK SK C K)

omit [DecidableEq K] [DecidableEq Sym] in
/-- A successful injected send is a successful `sendWith` with the injected samplers. -/
lemma exists_rand_of_mem_injectedSend (role : Role) (st : State PK SK C Sym)
    (key? : Option (ℕ × K)) (ρ : Message Sym) (tsnd : ℕ) (st' : State PK SK C Sym)
    (hout : some (key?, ρ, tsnd, st') ∈ support (injectedSend kem role ecEk ecCt t inj st)) :
    ∃ rand : SendRand Unit Unit, some (key?, ρ, tsnd, st', rand) ∈
      support (sendWith role (injectedKeygen kem role t inj st) (injectedEncaps kem role t inj st)
        ecEk ecCt st) := by
  rw [injectedSend, mem_support_bind_iff] at hout
  obtain ⟨out, hmem, hpure⟩ := hout
  cases out with
  | none => simp at hpure
  | some out =>
    rcases out with ⟨key, msg, epoch, state, rand⟩
    simp only [support_pure, Set.mem_singleton_iff, Option.map_some, Option.some.injEq,
      Prod.mk.injEq] at hpure
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hpure
    exact ⟨rand, hmem⟩

omit [DecidableEq K] [DecidableEq Sym] in
/-- At a generation of the target's key pair, the injected key generation returns the injected
pair. -/
lemma injectedKeygen_target (role : Role) (st : State PK SK C Sym)
    (h : sendGeneratesTarget role t st = true) (pk : PK) (sk : SK) (rk : Unit)
    (hmem : ((pk, sk), rk) ∈ support (injectedKeygen kem role t inj st)) :
    pk = inj.pk ∧ sk = inj.sk := by
  simp only [injectedKeygen, h, ↓reduceIte, support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq] at hmem
  exact ⟨hmem.1.1, hmem.1.2⟩

omit [DecidableEq K] [DecidableEq Sym] in
/-- At an encapsulation for the target, the injected encapsulation returns the injected key. -/
lemma injectedEncaps_target (role : Role) (st : State PK SK C Sym)
    (h : sendEncapsulatesTarget role t st = true) (pk : PK) (c : C) (k : K) (re : Unit)
    (hmem : ((c, k), re) ∈ support (injectedEncaps kem role t inj st pk)) : k = inj.key := by
  simp only [injectedEncaps, h, ↓reduceIte, support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq] at hmem
  exact hmem.1.2

omit [DecidableEq K] [DecidableEq Sym] in
/-- On an `InjInv` state where A is about to encapsulate for the target, A's decoded key for the
target is the injected public key. -/
lemma ekPeer_pinned_of_hitA (inj : TargetInjection PK SK C K)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : InjInv kem ecEk ecCt t inj s) (hq : sendEncapsulatesTarget .A t s.stA = true) :
    ∀ pk', s.stA.res.ekPeer t = some pk' → pk' = inj.pk := by
  obtain ⟨-, T, hA, -⟩ := hs.1
  have htpar := targetOwner_parity t
  cases ho : targetOwner t
  · rw [ho] at htpar
    rw [sendEncapsulatesTarget_eq_false_of_parity .A t s.stA htpar hA.res_parity] at hq
    cases hq
  · rw [injInv_B ho] at hs
    exact hs.2.ekPeer_pinned

omit [DecidableEq K] [DecidableEq Sym] in
/-- The version of `ekPeer_pinned_of_hitA` for B. -/
lemma ekPeer_pinned_of_hitB (inj : TargetInjection PK SK C K)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : InjInv kem ecEk ecCt t inj s) (hq : sendEncapsulatesTarget .B t s.stB = true) :
    ∀ pk', s.stB.res.ekPeer t = some pk' → pk' = inj.pk := by
  obtain ⟨-, T, -, hB⟩ := hs.1
  have htpar := targetOwner_parity t
  cases ho : targetOwner t
  · rw [injInv_A ho] at hs
    exact hs.2.ekPeer_pinned
  · rw [ho] at htpar
    rw [sendEncapsulatesTarget_eq_false_of_parity .B t s.stB htpar hB.res_parity] at hq
    cases hq

variable (hpk : (inj.pk, inj.sk) ∈ support kem.keygen)
  (hct : (inj.ct, inj.key) ∈ support (kem.encaps inj.pk))

omit [DecidableEq K] [DecidableEq Sym] in
include hpk hct in
/-- On an `InjInv` state, the support of A's injected send is included in that of A's honest
send. -/
lemma injectedSendA_subset
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : InjInv kem ecEk ecCt t inj s) :
    support (injectedSend kem .A ecEk ecCt t inj s.stA) ⊆
      support (send .A kem ecEk ecCt s.stA) := by
  refine injectedSend_support_subset kem .A ecEk ecCt t inj s.stA (fun _ => hpk) ?_
  intro h pk hpk'
  rw [ekPeer_pinned_of_hitA kem ecEk ecCt t inj s hs h pk hpk']
  exact hct

omit [DecidableEq K] [DecidableEq Sym] in
include hpk hct in
/-- On an `InjInv` state, the support of B's injected send is included in that of B's honest
send. -/
lemma injectedSendB_subset
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : InjInv kem ecEk ecCt t inj s) :
    support (injectedSend kem .B ecEk ecCt t inj s.stB) ⊆
      support (send .B kem ecEk ecCt s.stB) := by
  refine injectedSend_support_subset kem .B ecEk ecCt t inj s.stB (fun _ => hpk) ?_
  intro h pk hpk'
  rw [ekPeer_pinned_of_hitB kem ecEk ecCt t inj s hs h pk hpk']
  exact hct

variable (ht : 0 < t)

include hpk hct ht in
/-- A's injected send keeps `InjInv`. -/
lemma injInv_sendA_step
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : InjInv kem ecEk ecCt t inj s) :
    ∀ z ∈ support ((SCKAScheme.oracleSendA (injectedScheme kem hDet ecEk ecCt leak t inj) ()).run
      s), InjInv kem ecEk ecCt t inj z.2 := by
  intro z hz
  obtain ⟨out, hout, rfl⟩ := (SCKAScheme.mem_support_oracleSendA_run_iff _ s z).1 hz
  have hout' : out ∈ support (injectedSend kem .A ecEk ecCt t inj s.stA) := hout
  rcases out with _ | ⟨key?, ρ, tsnd, stA'⟩
  · exact hs
  have hG : GameInv kem ecEk ecCt (SCKAScheme.sendAUpdate s key? ρ tsnd stA') :=
    gameInv_sendA_step kem hDet ecEk ecCt leak s hs.1 _
      ((SCKAScheme.mem_support_oracleSendA_run_iff _ s _).2
        ⟨_, injectedSendA_subset kem ecEk ecCt t inj hpk hct s hs hout', rfl⟩)
  obtain ⟨rand, hw⟩ := exists_rand_of_mem_injectedSend kem ecEk ecCt t inj .A s.stA key? ρ tsnd
    stA' hout'
  obtain ⟨-, T, hA, -⟩ := hs.1
  have htpar := targetOwner_parity t
  cases ho : targetOwner t with
  | A =>
    rw [ho] at htpar
    rw [injInv_A ho] at hs ⊢
    refine ⟨hG, ?_⟩
    rcases key? with _ | ⟨tI, k⟩ <;>
      exact TargetInv.ownSend hs.2 ht htpar hA.res_parity hw
        (fun h pk sk rk hmem => injectedKeygen_target kem t inj .A s.stA h pk sk rk hmem)
  | B =>
    rw [injInv_B ho] at hs ⊢
    refine ⟨hG, ?_⟩
    rcases key? with _ | ⟨tI, k⟩ <;>
      exact TargetInv.peerSend hs.2 ht hA.ct_acked (s.nA + 1) hw
        (fun h pk c k re hmem => injectedEncaps_target kem t inj .A s.stA h pk c k re hmem)

include hpk hct ht in
/-- B's injected send keeps `InjInv`. -/
lemma injInv_sendB_step
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : InjInv kem ecEk ecCt t inj s) :
    ∀ z ∈ support ((SCKAScheme.oracleSendB (injectedScheme kem hDet ecEk ecCt leak t inj) ()).run
      s), InjInv kem ecEk ecCt t inj z.2 := by
  intro z hz
  obtain ⟨out, hout, rfl⟩ := (SCKAScheme.mem_support_oracleSendB_run_iff _ s z).1 hz
  have hout' : out ∈ support (injectedSend kem .B ecEk ecCt t inj s.stB) := hout
  rcases out with _ | ⟨key?, ρ, tsnd, stB'⟩
  · exact hs
  have hG : GameInv kem ecEk ecCt (SCKAScheme.sendBUpdate s key? ρ tsnd stB') :=
    gameInv_sendB_step kem hDet ecEk ecCt leak s hs.1 _
      ((SCKAScheme.mem_support_oracleSendB_run_iff _ s _).2
        ⟨_, injectedSendB_subset kem ecEk ecCt t inj hpk hct s hs hout', rfl⟩)
  obtain ⟨rand, hw⟩ := exists_rand_of_mem_injectedSend kem ecEk ecCt t inj .B s.stB key? ρ tsnd
    stB' hout'
  obtain ⟨-, T, -, hB⟩ := hs.1
  have htpar := targetOwner_parity t
  cases ho : targetOwner t with
  | B =>
    rw [ho] at htpar
    rw [injInv_B ho] at hs ⊢
    refine ⟨hG, ?_⟩
    rcases key? with _ | ⟨tI, k⟩ <;>
      exact TargetInv.ownSend hs.2 ht htpar hB.res_parity hw
        (fun h pk sk rk hmem => injectedKeygen_target kem t inj .B s.stB h pk sk rk hmem)
  | A =>
    rw [injInv_A ho] at hs ⊢
    refine ⟨hG, ?_⟩
    rcases key? with _ | ⟨tI, k⟩ <;>
      exact TargetInv.peerSend hs.2 ht hB.ct_acked (s.nB + 1) hw
        (fun h pk c k re hmem => injectedEncaps_target kem t inj .B s.stB h pk c k re hmem)

include hEk hCt ht in
/-- A's ideal receive keeps `InjInv`. -/
lemma injInv_recvA_step (n : ℕ)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : InjInv kem ecEk ecCt t inj s) :
    ∀ z ∈ support ((oracleRecvAIdeal kem hDet ecEk ecCt leak n).run s),
      InjInv kem ecEk ecCt t inj z.2 := by
  intro z hz
  have hG : GameInv kem ecEk ecCt z.2 :=
    gameInv_ideal_step kem hDet ecEk ecCt hEk hCt leak (Sum.inl (Sum.inr n)) s hs.1 z hz
  change z ∈ support ((SCKAScheme.oracleRecvA (schemeWithRecv kem hDet ecEk ecCt leak
    (recvWith .A (idealRecover s.keyB) ecEk ecCt) (recvB kem hDet ecEk ecCt)) n).run s) at hz
  obtain ⟨-, T, hA, hB⟩ := hs.1
  rcases (SCKAScheme.mem_support_oracleRecvA_run_iff _ s n z).1 hz with
    ⟨-, rfl⟩ | ⟨ρ, tsnd, -, -, rfl⟩ | ⟨ρ, tsnd, key?, trcv, stA', hmsg, hrecv, rfl⟩
  · exact hs
  · exact ⟨hG, hs.2⟩
  have hrecv' : recvWith .A (idealRecover s.keyB) ecEk ecCt s.stA ρ = some (key?, trcv, stA') :=
    hrecv
  have htpar := targetOwner_parity t
  cases ho : targetOwner t with
  | A =>
    rw [ho] at htpar
    rw [injInv_A ho] at hs ⊢
    refine ⟨hG, ?_⟩
    rcases key? with _ | ⟨tI, k⟩ <;>
      exact TargetInv.ownRecv hs.2 htpar hmsg (recv_tReq_parity (roleR := .A) hB hmsg)
        (fun hns => recvReq_eq_tRes hA hB hmsg hns) hrecv'
  | B =>
    rw [ho] at htpar
    rw [injInv_B ho] at hs ⊢
    refine ⟨hG, ?_⟩
    rcases key? with _ | ⟨tI, k⟩ <;>
      exact TargetInv.peerRecv hEk hCt hB hA hs.2 ht htpar hmsg hrecv'

include hEk hCt ht in
/-- B's ideal receive keeps `InjInv`. -/
lemma injInv_recvB_step (n : ℕ)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : InjInv kem ecEk ecCt t inj s) :
    ∀ z ∈ support ((oracleRecvBIdeal kem hDet ecEk ecCt leak n).run s),
      InjInv kem ecEk ecCt t inj z.2 := by
  intro z hz
  have hG : GameInv kem ecEk ecCt z.2 :=
    gameInv_ideal_step kem hDet ecEk ecCt hEk hCt leak (Sum.inr n) s hs.1 z hz
  change z ∈ support ((SCKAScheme.oracleRecvB (schemeWithRecv kem hDet ecEk ecCt leak
    (recvA kem hDet ecEk ecCt) (recvWith .B (idealRecover s.keyA) ecEk ecCt)) n).run s) at hz
  obtain ⟨-, T, hA, hB⟩ := hs.1
  rcases (SCKAScheme.mem_support_oracleRecvB_run_iff _ s n z).1 hz with
    ⟨-, rfl⟩ | ⟨ρ, tsnd, -, -, rfl⟩ | ⟨ρ, tsnd, key?, trcv, stB', hmsg, hrecv, rfl⟩
  · exact hs
  · exact ⟨hG, hs.2⟩
  have hrecv' : recvWith .B (idealRecover s.keyA) ecEk ecCt s.stB ρ = some (key?, trcv, stB') :=
    hrecv
  have htpar := targetOwner_parity t
  cases ho : targetOwner t with
  | B =>
    rw [ho] at htpar
    rw [injInv_B ho] at hs ⊢
    refine ⟨hG, ?_⟩
    rcases key? with _ | ⟨tI, k⟩ <;>
      exact TargetInv.ownRecv hs.2 htpar hmsg (recv_tReq_parity (roleR := .B) hA hmsg)
        (fun hns => recvReq_eq_tRes hB hA hmsg hns) hrecv'
  | A =>
    rw [ho] at htpar
    rw [injInv_A ho] at hs ⊢
    refine ⟨hG, ?_⟩
    rcases key? with _ | ⟨tI, k⟩ <;>
      exact TargetInv.peerRecv hEk hCt hA hB hs.2 ht htpar hmsg hrecv'

include ht in
/-- A's honest leaking send keeps `InjInv` on every successor that leaves `t` unexposed. -/
lemma injInv_sendArleak_step
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : InjInv kem ecEk ecCt t inj s) :
    ∀ z ∈ support ((SCKAScheme.oracleSendArleak (exposure .A leak).rleak
      (scheme kem hDet ecEk ecCt leak) ()).run s),
      t ∉ z.2.exposed → InjInv kem ecEk ecCt t inj z.2 := by
  intro z hz hexp
  have hG : GameInv kem ecEk ecCt z.2 :=
    SCKAScheme.oracleSendArleak_preservesInv_at _ _ (sendWith_rleak_forget kem .A ecEk ecCt leak)
      (GameInv kem ecEk ecCt) (fun _ _ h => h) s hs.1
      (gameInv_sendA_step kem hDet ecEk ecCt leak s hs.1) z hz
  rcases SCKAScheme.oracleSendArleak_support _ _ s z hz with
    rfl | ⟨key?, ρ, tsnd, stA', rand, hout, -, hz2⟩
  · exact hs
  rw [hz2] at hexp hG ⊢
  have hw : some (key?, ρ, tsnd, stA', rand) ∈
      support (sendWith .A leak.keygenRleak leak.encapsRleak ecEk ecCt s.stA) := hout
  have hnot : ¬ (sendGeneratesTarget .A t s.stA = true ∨
      sendEncapsulatesTarget .A t s.stA = true) := fun h =>
    hexp (Finset.mem_union_right _
      (mem_rleakEpochs_of_target .A _ _ ecEk ecCt s.stA key? ρ tsnd stA' rand hw t ht h))
  obtain ⟨-, T, hA, -⟩ := hs.1
  have htpar := targetOwner_parity t
  cases ho : targetOwner t with
  | A =>
    rw [ho] at htpar
    rw [injInv_A ho] at hs ⊢
    refine ⟨hG, ?_⟩
    rcases key? with _ | ⟨tI, k⟩ <;>
      exact TargetInv.ownSend hs.2 ht htpar hA.res_parity hw (fun h => absurd (Or.inl h) hnot)
  | B =>
    rw [injInv_B ho] at hs ⊢
    refine ⟨hG, ?_⟩
    rcases key? with _ | ⟨tI, k⟩ <;>
      exact TargetInv.peerSend hs.2 ht hA.ct_acked (s.nA + 1) hw
        (fun h => absurd (Or.inr h) hnot)

include ht in
/-- B's honest leaking send keeps `InjInv` on every successor that leaves `t` unexposed. -/
lemma injInv_sendBrleak_step
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : InjInv kem ecEk ecCt t inj s) :
    ∀ z ∈ support ((SCKAScheme.oracleSendBrleak (exposure .B leak).rleak
      (scheme kem hDet ecEk ecCt leak) ()).run s),
      t ∉ z.2.exposed → InjInv kem ecEk ecCt t inj z.2 := by
  intro z hz hexp
  have hG : GameInv kem ecEk ecCt z.2 :=
    SCKAScheme.oracleSendBrleak_preservesInv_at _ _ (sendWith_rleak_forget kem .B ecEk ecCt leak)
      (GameInv kem ecEk ecCt) (fun _ _ h => h) s hs.1
      (gameInv_sendB_step kem hDet ecEk ecCt leak s hs.1) z hz
  rcases SCKAScheme.oracleSendBrleak_support _ _ s z hz with
    rfl | ⟨key?, ρ, tsnd, stB', rand, hout, -, hz2⟩
  · exact hs
  rw [hz2] at hexp hG ⊢
  have hw : some (key?, ρ, tsnd, stB', rand) ∈
      support (sendWith .B leak.keygenRleak leak.encapsRleak ecEk ecCt s.stB) := hout
  have hnot : ¬ (sendGeneratesTarget .B t s.stB = true ∨
      sendEncapsulatesTarget .B t s.stB = true) := fun h =>
    hexp (Finset.mem_union_right _
      (mem_rleakEpochs_of_target .B _ _ ecEk ecCt s.stB key? ρ tsnd stB' rand hw t ht h))
  obtain ⟨-, T, -, hB⟩ := hs.1
  have htpar := targetOwner_parity t
  cases ho : targetOwner t with
  | B =>
    rw [ho] at htpar
    rw [injInv_B ho] at hs ⊢
    refine ⟨hG, ?_⟩
    rcases key? with _ | ⟨tI, k⟩ <;>
      exact TargetInv.ownSend hs.2 ht htpar hB.res_parity hw (fun h => absurd (Or.inl h) hnot)
  | A =>
    rw [injInv_A ho] at hs ⊢
    refine ⟨hG, ?_⟩
    rcases key? with _ | ⟨tI, k⟩ <;>
      exact TargetInv.peerSend hs.2 ht hB.ct_acked (s.nB + 1) hw
        (fun h => absurd (Or.inr h) hnot)

variable [SampleableType K]

include hEk hCt ht hpk hct in
/-- Assume:

* `ecEk` and `ecCt` are correct erasure codes;
* `0 < t`, and the injected key pair and encapsulation are supported.

Then every injected security query, for every selection, keeps `InjInv` on every successor
that leaves `t` unexposed. Successors exposing `t` carry no obligation: the stopped run
discards them. -/
theorem injectedSecurityImpl_preservesInv_continuing (random : ℕ → Bool)
    (q : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (hs : InjInv kem ecEk ecCt t inj s) :
    ∀ z ∈ support ((injectedSecurityImpl kem hDet ecEk ecCt leak t inj random q).run s),
      t ∉ z.2.exposed → InjInv kem ecEk ecCt t inj z.2 := by
  intro z hz hexp
  rcases q with (((((q | u) | u) | e) | u) | u)
  · rcases q with (((n | ⟨⟩) | ⟨⟩) | n) | n
    · exact SCKAScheme.oracleUnif_preservesInv (InjInv kem ecEk ecCt t inj) n s hs z hz
    · exact injInv_sendA_step kem hDet ecEk ecCt leak t inj hpk hct ht s hs z hz
    · exact injInv_sendB_step kem hDet ecEk ecCt leak t inj hpk hct ht s hs z hz
    · exact injInv_recvA_step kem hDet ecEk ecCt hEk hCt leak t inj ht n s hs z hz
    · exact injInv_recvB_step kem hDet ecEk ecCt hEk hCt leak t inj ht n s hs z hz
  · cases u
    exact injInv_sendArleak_step kem hDet ecEk ecCt leak t inj ht s hs z hz hexp
  · cases u
    exact injInv_sendBrleak_step kem hDet ecEk ecCt leak t inj ht s hs z hz hexp
  · rcases SCKAScheme.oracleChall_support (random e) s e z hz with ⟨rfl, -⟩ | ⟨-, -, h⟩
    · exact hs
    · rw [h]
      exact hs
  · cases u
    rcases SCKAScheme.oracleCorruptA_support _ s z hz with rfl | ⟨-, rfl⟩ <;> exact hs
  · cases u
    rcases SCKAScheme.oracleCorruptB_support _ s z hz with rfl | ⟨-, rfl⟩ <;> exact hs

omit [SampleableType K] in
/-- Every injected correctness query keeps the exposed and challenged sets. -/
lemma injectedCorrectnessImpl_bookkeeping
    (q : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (z) (hz : z ∈ support ((injectedCorrectnessImpl kem hDet ecEk ecCt leak t inj q).run s)) :
    z.2.exposed = s.exposed ∧ z.2.challenged = s.challenged := by
  rcases q with (((n | ⟨⟩) | ⟨⟩) | n) | n
  · exact SCKAScheme.oracleUnif_preservesInv
      (fun u => u.exposed = s.exposed ∧ u.challenged = s.challenged) n s ⟨rfl, rfl⟩ z hz
  · obtain ⟨out, -, rfl⟩ := (SCKAScheme.mem_support_oracleSendA_run_iff _ s z).1 hz
    rcases out with _ | ⟨_ | ⟨tI, k⟩, ρ, tsnd, stA'⟩ <;> simp [SCKAScheme.sendAUpdate]
  · obtain ⟨out, -, rfl⟩ := (SCKAScheme.mem_support_oracleSendB_run_iff _ s z).1 hz
    rcases out with _ | ⟨_ | ⟨tI, k⟩, ρ, tsnd, stB'⟩ <;> simp [SCKAScheme.sendBUpdate]
  · change z ∈ support ((SCKAScheme.oracleRecvA (schemeWithRecv kem hDet ecEk ecCt leak
      (recvWith .A (idealRecover s.keyB) ecEk ecCt) (recvB kem hDet ecEk ecCt)) n).run s) at hz
    rcases (SCKAScheme.mem_support_oracleRecvA_run_iff _ s n z).1 hz with
      ⟨-, rfl⟩ | ⟨ρ, tsnd, -, -, rfl⟩ | ⟨ρ, tsnd, keyOpt, trcv, stA', -, -, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · rcases keyOpt with _ | ⟨tI, k⟩ <;> simp [SCKAScheme.recvAUpdate]
  · change z ∈ support ((SCKAScheme.oracleRecvB (schemeWithRecv kem hDet ecEk ecCt leak
      (recvA kem hDet ecEk ecCt) (recvWith .B (idealRecover s.keyA) ecEk ecCt)) n).run s) at hz
    rcases (SCKAScheme.mem_support_oracleRecvB_run_iff _ s n z).1 hz with
      ⟨-, rfl⟩ | ⟨ρ, tsnd, -, -, rfl⟩ | ⟨ρ, tsnd, keyOpt, trcv, stB', -, -, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · rcases keyOpt with _ | ⟨tI, k⟩ <;> simp [SCKAScheme.recvBUpdate]

/-- Every injected security query shrinks neither the exposed nor the challenged set, and every
epoch it newly exposes was not challenged before it. -/
lemma injectedSecurityImpl_bookkeeping (random : ℕ → Bool)
    (q : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (z) (hz : z ∈ support ((injectedSecurityImpl kem hDet ecEk ecCt leak t inj random q).run s)) :
    s.exposed ⊆ z.2.exposed ∧ s.challenged ⊆ z.2.challenged ∧
      ∀ e ∈ z.2.exposed, e ∉ s.exposed → e ∉ s.challenged := by
  refine SCKAScheme.securityImplOf_bookkeeping _ _ _ _ _ s
    (fun q z hz => injectedCorrectnessImpl_bookkeeping kem hDet ecEk ecCt leak t inj q s z hz)
    (fun e z hz => ?_) q z hz
  rcases SCKAScheme.oracleChall_support (random e) s e z hz with ⟨h, -⟩ | ⟨-, -, h⟩
  · rw [h]; exact ⟨rfl, le_rfl⟩
  · rw [h]; exact ⟨rfl, Finset.subset_insert _ _⟩

end Preservation

/-! ## First-use predicates for the target's samples -/

/-- The target's key pair has been generated: the owner's key epoch is at least `t`. -/
def targetGenerated (role : Role) (t : ℕ) (st : State PK SK C Sym) : Prop :=
  (t : ℤ) ≤ st.res.resEpoch + role.offset

/-- The target has been encapsulated for: the peer's responder epoch passed `t`, or is `t`
with a retained ciphertext or with `t` acknowledged. -/
def targetEncapsulated (t : ℕ) (st : State PK SK C Sym) : Prop :=
  (t : ℤ) < st.res.resEpoch ∨
    ((t : ℤ) = st.res.resEpoch ∧ (st.res.ct.isSome = true ∨ (t : ℤ) ∈ st.ack.ctRec))

/-- Once the target's key pair is generated, no send generates it. -/
lemma sendGeneratesTarget_eq_false_of_generated (role : Role) (t : ℕ) (st : State PK SK C Sym)
    (h : targetGenerated role t st) : sendGeneratesTarget role t st = false := by
  rw [Bool.eq_false_iff]
  intro hc
  simp only [sendGeneratesTarget, Bool.and_eq_true, decide_eq_true_eq] at hc
  unfold targetGenerated at h
  omega

/-- The encapsulation guard, unfolded. -/
lemma sendEncapsGuard_eq_true_iff (role : Role) (st : State PK SK C Sym) :
    sendEncapsGuard role st = true ↔
      st.res.resEpoch + (if sendKeygenGuard role st then 2 else 0) + role.offset ∈
          st.ack.ekRec ∧
        st.res.resEpoch + (if sendKeygenGuard role st then 2 else 0) ∉ st.ack.ctRec ∧
        st.res.ct = none ∧
        st.res.resEpoch + (if sendKeygenGuard role st then 2 else 0) ∈ st.ack.ekRec := by
  simp only [sendEncapsGuard, Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none]
  tauto

/-- Once the target is encapsulated for, no send encapsulates for it. -/
lemma sendEncapsulatesTarget_eq_false_of_encapsulated (role : Role) (t : ℕ)
    (st : State PK SK C Sym) (h : targetEncapsulated t st) :
    sendEncapsulatesTarget role t st = false := by
  rw [Bool.eq_false_iff]
  intro hc
  simp only [sendEncapsulatesTarget, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hg, heq⟩ := hc
  rw [sendEncapsGuard_eq_true_iff] at hg
  obtain ⟨-, hnot, hctn, -⟩ := hg
  unfold targetEncapsulated at h
  split_ifs at hnot heq
  · omega
  · simp only [add_zero] at hnot heq
    rcases h with hlt | ⟨heq', hsome | hmem⟩
    · omega
    · rw [hctn] at hsome
      cases hsome
    · exact hnot (by rw [heq]; exact hmem)

/-- A send that generates the target's key pair leaves it generated. -/
lemma targetGenerated_of_sendWith {RK RE : Type} (role : Role) (t : ℕ)
    (keygen : ProbComp ((PK × SK) × RK)) (encaps : PK → ProbComp ((C × K) × RE))
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (key? : Option (ℕ × K)) (ρ : Message Sym) (tsnd : ℕ)
    (st' : State PK SK C Sym) (rand : SendRand RK RE)
    (hout : some (key?, ρ, tsnd, st', rand) ∈ support (sendWith role keygen encaps ecEk ecCt st))
    (h : sendGeneratesTarget role t st = true) : targetGenerated role t st' := by
  obtain ⟨hkflag, -, hres, -⟩ :=
    sendWith_operation_facts role keygen encaps ecEk ecCt st key? ρ tsnd st' rand hout
  simp only [sendGeneratesTarget, Bool.and_eq_true, decide_eq_true_eq] at h
  unfold targetGenerated
  rw [hres, hkflag, h.1]
  simp only [↓reduceIte]
  omega

/-- A send keeps the target generated. -/
lemma targetGenerated_sendWith {RK RE : Type} (role : Role) (t : ℕ)
    (keygen : ProbComp ((PK × SK) × RK)) (encaps : PK → ProbComp ((C × K) × RE))
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (key? : Option (ℕ × K)) (ρ : Message Sym) (tsnd : ℕ)
    (st' : State PK SK C Sym) (rand : SendRand RK RE)
    (hout : some (key?, ρ, tsnd, st', rand) ∈ support (sendWith role keygen encaps ecEk ecCt st))
    (h : targetGenerated role t st) : targetGenerated role t st' := by
  obtain ⟨-, -, hres, -⟩ :=
    sendWith_operation_facts role keygen encaps ecEk ecCt st key? ρ tsnd st' rand hout
  unfold targetGenerated at h ⊢
  rw [hres]
  split_ifs <;> omega

/-- A receive keeps the target generated. -/
lemma targetGenerated_recvWith [DecidableEq Sym] (role : Role) (t : ℕ)
    (recover : ℤ → SK → C → Option K)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym)
    (key? : Option (ℕ × K)) (trcv : ℕ) (st' : State PK SK C Sym)
    (hout : recvWith role recover ecEk ecCt st ρ = some (key?, trcv, st'))
    (h : targetGenerated role t st) : targetGenerated role t st' := by
  unfold targetGenerated at h ⊢
  rw [recvWith_resEpoch role recover ecEk ecCt st ρ key? trcv st' hout]
  exact h

/-- A send that encapsulates for the target leaves it encapsulated for. -/
lemma targetEncapsulated_of_sendWith {RK RE : Type} (role : Role) (t : ℕ)
    (keygen : ProbComp ((PK × SK) × RK)) (encaps : PK → ProbComp ((C × K) × RE))
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (key? : Option (ℕ × K)) (ρ : Message Sym) (tsnd : ℕ)
    (st' : State PK SK C Sym) (rand : SendRand RK RE)
    (hout : some (key?, ρ, tsnd, st', rand) ∈ support (sendWith role keygen encaps ecEk ecCt st))
    (h : sendEncapsulatesTarget role t st = true) : targetEncapsulated t st' := by
  have f := sendWith_facts role keygen encaps ecEk ecCt st key? ρ tsnd st' rand hout
  obtain ⟨hkflag, heflag, hres, -⟩ :=
    sendWith_operation_facts role keygen encaps ecEk ecCt st key? ρ tsnd st' rand hout
  simp only [sendEncapsulatesTarget, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨re, hre⟩ := Option.isSome_iff_exists.mp (heflag.trans h.1)
  obtain ⟨_, c, _, -, -, -, hct⟩ := f.encaps re hre
  refine Or.inr ⟨?_, Or.inl (by rw [hct]; rfl)⟩
  rw [hres, hkflag]
  exact h.2.symm

/-- A send keeps the target encapsulated for. -/
lemma targetEncapsulated_sendWith {RK RE : Type} (role : Role) (t : ℕ)
    (keygen : ProbComp ((PK × SK) × RK)) (encaps : PK → ProbComp ((C × K) × RE))
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (key? : Option (ℕ × K)) (ρ : Message Sym) (tsnd : ℕ)
    (st' : State PK SK C Sym) (rand : SendRand RK RE)
    (hout : some (key?, ρ, tsnd, st', rand) ∈ support (sendWith role keygen encaps ecEk ecCt st))
    (h : targetEncapsulated t st) : targetEncapsulated t st' := by
  have f := sendWith_facts role keygen encaps ecEk ecCt st key? ρ tsnd st' rand hout
  obtain ⟨-, -, hres, -⟩ :=
    sendWith_operation_facts role keygen encaps ecEk ecCt st key? ρ tsnd st' rand hout
  unfold targetEncapsulated at h ⊢
  rw [hres, f.acknowledgements]
  rcases h with hlt | ⟨heq, hrest⟩
  · left
    split_ifs <;> omega
  · split_ifs with hk
    · left
      omega
    · right
      refine ⟨by omega, ?_⟩
      rcases hrest with hsome | hmem
      · left
        cases hre : rand.encapsRand with
        | none => rw [(f.no_encaps hre).2]; exact hsome
        | some re =>
          obtain ⟨_, c, _, -, -, -, hct⟩ := f.encaps re hre
          rw [hct]
          rfl
      · exact Or.inr hmem

/-- A receive keeps the target encapsulated for. -/
lemma targetEncapsulated_recvWith [DecidableEq Sym] (role : Role) (t : ℕ)
    (recover : ℤ → SK → C → Option K)
    (ecEk : ErasureCodePayload PK Sym) (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (ρ : Message Sym)
    (key? : Option (ℕ × K)) (trcv : ℕ) (st' : State PK SK C Sym)
    (hout : recvWith role recover ecEk ecCt st ρ = some (key?, trcv, st'))
    (h : targetEncapsulated t st) : targetEncapsulated t st' := by
  have f := recvWith_facts role recover ecEk ecCt st ρ key? trcv st' hout
  unfold targetEncapsulated at h ⊢
  rw [f.resEpoch]
  rcases h with hlt | ⟨heq, hsome | hmem⟩
  · exact Or.inl hlt
  · refine Or.inr ⟨heq, ?_⟩
    rcases f.ct with hc | ⟨-, hack⟩
    · rw [hc]; exact Or.inl hsome
    · rw [← heq] at hack; exact Or.inr hack
  · exact Or.inr ⟨heq, Or.inr (f.ctRec_mono hmem)⟩

end oppBiKemCKA
