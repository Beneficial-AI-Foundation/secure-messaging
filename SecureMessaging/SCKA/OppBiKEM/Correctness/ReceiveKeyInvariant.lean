/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Gavran, Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppBiKEM.Correctness.ReceiveState

/-!
# Opp-BiKEM received-key epoch freshness

Retained decapsulation keys mark positive epochs with empty local game-key entries.
This structural invariant yields freshness of emitted receive epochs throughout the
correctness game. Receive success and full protocol correctness require further results.
-/

open OracleSpec OracleComp KEMScheme

namespace oppBiKemCKA

variable {K PK SK C Sym : Type}

structure ReceiveKeyInvariant
    (role : Role) (st : State PK SK C Sym) (keys : ℕ → Option K) : Prop where
  resEpoch_lower :
    (if role = .A then (-1 : ℤ) else 0) ≤ st.res.resEpoch
  futureKeys : ∀ t : ℕ,
    max st.res.resEpoch (st.res.resEpoch + role.offset) < (t : ℤ) →
      keys t = none
  storedKeys : ∀ (epoch : ℤ) (secretKey : SK),
    (epoch, secretKey) ∈ st.req.dk →
      0 < epoch ∧
      epoch ≤ st.res.resEpoch + role.offset ∧
      epoch % 2 ≠ st.res.resEpoch % 2 ∧
      keys epoch.toNat = none

def GameReceiveKeyInvariant
    (s : SCKAScheme.GameState
      (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym)) : Prop :=
  ReceiveKeyInvariant .A s.stA s.keyA ∧
    ReceiveKeyInvariant .B s.stB s.keyB

theorem initGameState_receiveKeyInvariant
    (stA : StA PK SK C Sym) (stB : StB PK SK C Sym)
    (hA : stA ∈ support (initA () : ProbComp (StA PK SK C Sym)))
    (hB : stB ∈ support (initB () : ProbComp (StB PK SK C Sym))) :
    GameReceiveKeyInvariant (K := K) (SCKAScheme.initGameState stA stB) := by
  simp only [initA, init, support_pure, Set.mem_singleton_iff] at hA
  simp only [initB, init, support_pure, Set.mem_singleton_iff] at hB
  subst stA
  subst stB
  constructor <;> constructor <;> simp [SCKAScheme.initGameState, Role.offset]

private theorem send_dk_transition
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (key? : Option (ℕ × K))
    (ρ : Message Sym) (tsnd : ℕ) (st' : State PK SK C Sym)
    (hout : some (key?, ρ, tsnd, st') ∈
      support (send role kem ecEk ecCt st)) :
    st'.req.dk = st.req.dk ∨
      ∃ secretKey : SK,
        st'.res.resEpoch = st.res.resEpoch + 2 ∧
        st'.req.dk =
          (st'.res.resEpoch + role.offset, secretKey) ::
            st.req.dk.filter
              (fun p => p.1 != (st'.res.resEpoch + role.offset)) := by
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
    all_goals first
      | exact Or.inl rfl
      | exact Or.inr ⟨_, rfl, rfl⟩

theorem send_preserves_receiveKeyInvariant
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (keys : ℕ → Option K)
    (hs : ReceiveKeyInvariant role st keys)
    (key? : Option (ℕ × K)) (ρ : Message Sym)
    (tsnd : ℕ) (st' : State PK SK C Sym)
    (hout : some (key?, ρ, tsnd, st') ∈
      support (send role kem ecEk ecCt st)) :
    ReceiveKeyInvariant role st'
      (match key? with
      | none => keys
      | some (tI, key) => Function.update keys tI (some key)) := by
  have hfacts := send_support_facts role kem ecEk ecCt st key? ρ tsnd st' hout
  rcases hfacts with ⟨_, _, hepoch, _, hkey⟩
  have hdk := send_dk_transition role kem ecEk ecCt st key? ρ tsnd st' hout
  have hlower := hs.resEpoch_lower
  have hlower' : (if role = .A then (-1 : ℤ) else 0) ≤ st'.res.resEpoch := by
    rcases hepoch with hepoch | hepoch <;> omega
  have hbound :
      max st.res.resEpoch (st.res.resEpoch + role.offset) ≤
        max st'.res.resEpoch (st'.res.resEpoch + role.offset) := by
    rcases hepoch with hepoch | hepoch <;> omega
  have hretained : ∀ (epoch : ℤ) (secretKey : SK),
      (epoch, secretKey) ∈ st.req.dk →
        0 < epoch ∧ epoch ≤ st'.res.resEpoch + role.offset ∧
          epoch % 2 ≠ st'.res.resEpoch % 2 ∧ keys epoch.toNat = none := by
    intro epoch secretKey hmem
    obtain ⟨hpos, hle, hparity, hnone⟩ := hs.storedKeys epoch secretKey hmem
    refine ⟨hpos, ?_, ?_, hnone⟩
    · rcases hepoch with hepoch | hepoch <;> omega
    · rcases hepoch with hepoch | hepoch <;> omega
  have hbase : ReceiveKeyInvariant role st' keys := by
    refine ⟨hlower', fun t ht => hs.futureKeys t (lt_of_le_of_lt hbound ht), ?_⟩
    intro epoch secretKey hmem
    rcases hdk with hdk | ⟨newKey, hadvance, hdk⟩
    · rw [hdk] at hmem
      exact hretained epoch secretKey hmem
    · rw [hdk] at hmem
      simp only [List.mem_cons, List.mem_filter, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨hmem, _⟩
      · have hpos : 0 < st'.res.resEpoch + role.offset := by
          cases role <;> simp only [Role.offset, reduceCtorEq, reduceIte] at hlower ⊢ <;>
            omega
        have hfuture :
            max st.res.resEpoch (st.res.resEpoch + role.offset) <
              st'.res.resEpoch + role.offset := by
          cases role <;> simp only [Role.offset] <;> omega
        refine ⟨hpos, le_refl _, ?_, ?_⟩
        · cases role <;> simp only [Role.offset] <;> omega
        · apply hs.futureKeys
          rw [Int.toNat_of_nonneg (le_of_lt hpos)]
          exact hfuture
      · exact hretained epoch secretKey hmem
  cases key? with
  | none => exact hbase
  | some keyOut =>
    rcases keyOut with ⟨tI, key⟩
    obtain ⟨htI, _, _, _⟩ := hkey tI key rfl
    have hindexBound :
        (st'.res.resEpoch.toNat : ℤ) ≤
          max st'.res.resEpoch (st'.res.resEpoch + role.offset) := by
      by_cases hnonneg : 0 ≤ st'.res.resEpoch
      · rw [Int.toNat_of_nonneg hnonneg]
        exact le_max_left _ _
      · have hzero : st'.res.resEpoch.toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
        rw [hzero]
        cases role <;> simp only [Role.offset, reduceCtorEq, reduceIte] at hlower' ⊢ <;>
          omega
    change ReceiveKeyInvariant role st' (Function.update keys tI (some key))
    refine ⟨hbase.resEpoch_lower, ?_, ?_⟩
    · intro t ht
      have hne : t ≠ tI := by
        rw [htI]
        omega
      rw [Function.update_of_ne hne]
      exact hbase.futureKeys t ht
    · intro epoch secretKey hmem
      obtain ⟨hpos, hle, hparity, hnone⟩ := hbase.storedKeys epoch secretKey hmem
      have hne : epoch.toNat ≠ tI := by
        rw [htI]
        intro heq
        have hcast : (epoch.toNat : ℤ) = epoch := Int.toNat_of_nonneg (le_of_lt hpos)
        have hres : 0 ≤ st'.res.resEpoch := by omega
        have hcast' : (st'.res.resEpoch.toNat : ℤ) = st'.res.resEpoch :=
          Int.toNat_of_nonneg hres
        have : epoch = st'.res.resEpoch := by omega
        exact hparity (congrArg (fun x : ℤ => x % 2) this)
      exact ⟨hpos, hle, hparity, by simpa only [Function.update_of_ne hne] using hnone⟩

theorem recv_preserves_receiveKeyInvariant
    [DecidableEq Sym]
    (role : Role) (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (st : State PK SK C Sym) (keys : ℕ → Option K)
    (hs : ReceiveKeyInvariant role st keys)
    (ρ : Message Sym) (key? : Option (ℕ × K))
    (trcv : ℕ) (st' : State PK SK C Sym)
    (hout : recv role kem hDet ecEk ecCt st ρ =
      some (key?, trcv, st')) :
    ReceiveKeyInvariant role st'
      (match key? with
      | none => keys
      | some (tI, key) => Function.update keys tI (some key)) := by
  have hfacts := recv_success_state_facts role kem hDet ecEk ecCt st ρ key? trcv st' hout
  rcases hfacts with ⟨_, hepoch, _, _, _, _, _, _, hnone⟩
  cases key? with
  | none =>
    have hdk := hnone rfl
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hepoch] using hs.resEpoch_lower
    · intro t ht
      exact hs.futureKeys t (by simpa only [hepoch] using ht)
    · intro epoch secretKey hmem
      rw [hdk] at hmem
      simpa only [hepoch] using hs.storedKeys epoch secretKey hmem
  | some keyOut =>
    rcases keyOut with ⟨tI, key⟩
    have hemitted := recv_emitted_key_facts role kem hDet ecEk ecCt st ρ tI key trcv st' hout
    rcases hemitted with
      ⟨_, _, htI, _, _, hfilter, _, _, secretKey, ciphertext, hlookup, _, _⟩
    have hmem : (st'.req.reqEpoch, secretKey) ∈ st.req.dk := by
      obtain ⟨before, after, hlist, _⟩ := List.lookup_eq_some_iff.mp hlookup
      simp only [hlist, List.mem_append, List.mem_cons, true_or, or_true]
    obtain ⟨hpos, hle, _, _⟩ := hs.storedKeys st'.req.reqEpoch secretKey hmem
    have hcast : (st'.req.reqEpoch.toNat : ℤ) = st'.req.reqEpoch :=
      Int.toNat_of_nonneg (le_of_lt hpos)
    change ReceiveKeyInvariant role st' (Function.update keys tI (some key))
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hepoch] using hs.resEpoch_lower
    · intro t ht
      have hne : t ≠ tI := by
        rw [htI]
        rw [hepoch] at ht
        omega
      rw [Function.update_of_ne hne]
      exact hs.futureKeys t (by simpa only [hepoch] using ht)
    · intro epoch storedKey hstored
      rw [hfilter] at hstored
      simp only [List.mem_filter, bne_iff_ne] at hstored
      obtain ⟨hpositive, hupper, hparity, hfree⟩ :=
        hs.storedKeys epoch storedKey hstored.1
      have hne : epoch.toNat ≠ tI := by
        rw [htI]
        have hepochCast : (epoch.toNat : ℤ) = epoch :=
          Int.toNat_of_nonneg (le_of_lt hpositive)
        intro heq
        have : epoch = st'.req.reqEpoch := by omega
        exact hstored.2 this
      refine ⟨hpositive, ?_, ?_, ?_⟩
      · simpa only [hepoch] using hupper
      · simpa only [hepoch] using hparity
      · simpa only [Function.update_of_ne hne] using hfree

theorem sckaCorrectnessImpl_preserves_receiveKeyInvariant
    [DecidableEq K] [DecidableEq Sym]
    (kem : KEMScheme ProbComp K PK SK C)
    (hDet : kem.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt : ErasureCodePayload C Sym)
    (leak : kem.RandLeak) :
    QueryImpl.PreservesInv
      (SCKAScheme.sckaCorrectnessImpl (scheme kem hDet ecEk ecCt leak))
      (GameReceiveKeyInvariant
        (K := K) (PK := PK) (SK := SK) (C := C) (Sym := Sym)) := by
  intro t s hs z hz
  rcases t with (((n | ⟨⟩) | ⟨⟩) | n) | n
  · exact oracleUnif_preservesInv _ n s hs z hz
  · change z ∈ support ((SCKAScheme.oracleSendA (scheme kem hDet ecEk ecCt leak) ()).run s)
      at hz
    simp only [SCKAScheme.oracleSendA, StateT.run_bind, StateT.run_get, pure_bind,
      StateT.run_liftM, bind_assoc] at hz
    obtain ⟨out, hout, hz⟩ := mem_support_bind_peel _ _ hz
    cases out with
    | none =>
      simp at hz
      subst z
      exact hs
    | some out =>
      rcases out with ⟨key?, ρ, tsnd, st'⟩
      have hlocal := send_preserves_receiveKeyInvariant .A kem ecEk ecCt
        s.stA s.keyA hs.1 key? ρ tsnd st' hout
      cases key? <;> simp at hz <;> subst z <;> exact ⟨hlocal, hs.2⟩
  · change z ∈ support ((SCKAScheme.oracleSendB (scheme kem hDet ecEk ecCt leak) ()).run s)
      at hz
    simp only [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get, pure_bind,
      StateT.run_liftM, bind_assoc] at hz
    obtain ⟨out, hout, hz⟩ := mem_support_bind_peel _ _ hz
    cases out with
    | none =>
      simp at hz
      subst z
      exact hs
    | some out =>
      rcases out with ⟨key?, ρ, tsnd, st'⟩
      have hlocal := send_preserves_receiveKeyInvariant .B kem ecEk ecCt
        s.stB s.keyB hs.2 key? ρ tsnd st' hout
      cases key? <;> simp at hz <;> subst z <;> exact ⟨hs.1, hlocal⟩
  · change z ∈ support ((SCKAScheme.oracleRecvA (scheme kem hDet ecEk ecCt leak) n).run s)
      at hz
    cases hmsg : s.msgB n with
    | none =>
      simp only [SCKAScheme.oracleRecvA, StateT.run_bind, StateT.run_get,
        pure_bind, hmsg, StateT.run_pure, support_pure] at hz
      subst z
      exact hs
    | some entry =>
      rcases entry with ⟨ρ, tsnd⟩
      cases hrecv : (scheme kem hDet ecEk ecCt leak).recvA s.stA ρ with
      | none =>
        simp only [SCKAScheme.oracleRecvA, bind_pure_comp, StateT.run_bind, StateT.run_get,
          pure_bind, hmsg, hrecv, StateT.run_map, StateT.run_set, map_pure, support_pure] at hz
        subst z
        exact hs
      | some out =>
        rcases out with ⟨key?, trcv, st'⟩
        have hlocal := recv_preserves_receiveKeyInvariant .A kem hDet ecEk ecCt
          s.stA s.keyA hs.1 ρ key? trcv st' hrecv
        cases key? <;>
          simp only [SCKAScheme.oracleRecvA, bind_pure_comp, StateT.run_bind, StateT.run_get,
            pure_bind, hmsg, hrecv, StateT.run_map, StateT.run_set, map_pure,
            support_pure] at hz <;>
          subst z <;>
          exact ⟨hlocal, hs.2⟩
  · change z ∈ support ((SCKAScheme.oracleRecvB (scheme kem hDet ecEk ecCt leak) n).run s)
      at hz
    cases hmsg : s.msgA n with
    | none =>
      simp only [SCKAScheme.oracleRecvB, StateT.run_bind, StateT.run_get,
        pure_bind, hmsg, StateT.run_pure, support_pure] at hz
      subst z
      exact hs
    | some entry =>
      rcases entry with ⟨ρ, tsnd⟩
      cases hrecv : (scheme kem hDet ecEk ecCt leak).recvB s.stB ρ with
      | none =>
        simp only [SCKAScheme.oracleRecvB, bind_pure_comp, StateT.run_bind, StateT.run_get,
          pure_bind, hmsg, hrecv, StateT.run_map, StateT.run_set, map_pure, support_pure] at hz
        subst z
        exact hs
      | some out =>
        rcases out with ⟨key?, trcv, st'⟩
        have hlocal := recv_preserves_receiveKeyInvariant .B kem hDet ecEk ecCt
          s.stB s.keyB hs.2 ρ key? trcv st' hrecv
        cases key? <;>
          simp only [SCKAScheme.oracleRecvB, bind_pure_comp, StateT.run_bind, StateT.run_get,
            pure_bind, hmsg, hrecv, StateT.run_map, StateT.run_set, map_pure,
            support_pure] at hz <;>
          subst z <;>
          exact ⟨hs.1, hlocal⟩

theorem simulateQ_receiveKeyInvariant
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
    GameReceiveKeyInvariant z.2 := by
  exact simulateQ_run_preservesInv _ GameReceiveKeyInvariant
    (sckaCorrectnessImpl_preserves_receiveKeyInvariant kem hDet ecEk ecCt leak)
    adv _ (initGameState_receiveKeyInvariant stA stB hA hB) z hz

theorem oracleRecvB_emitted_epoch_fresh_of_reachable
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
      (SCKAScheme.initGameState stA stB)))
    (s' : SCKAScheme.GameState
      (StA PK SK C Sym) (StB PK SK C Sym) K (Message Sym))
    (n trcv t : ℕ)
    (hout : (some (trcv, some t), s') ∈ support
      ((SCKAScheme.oracleRecvB (scheme kem hDet ecEk ecCt leak) n).run z.2)) :
    0 < t ∧ z.2.keyB t = none := by
  have hinv := simulateQ_receiveKeyInvariant kem hDet ecEk ecCt leak adv stA stB hA hB z hz
  have hmessages := simulateQ_messageEpochsConsistent kem hDet ecEk ecCt leak adv stA stB z hz
  obtain ⟨ρ, _, _, _, _, _, _, _, _, _, _, _, hkey⟩ :=
    oracleRecvB_recorded_state_facts kem hDet ecEk ecCt leak z.2 s' hmessages
      n trcv (some t) hout
  obtain ⟨ht, _, _, key, secretKey, ciphertext, _, hlookup, _, _⟩ := hkey t rfl
  have hmem : (s'.stB.req.reqEpoch, secretKey) ∈ z.2.stB.req.dk := by
    obtain ⟨before, after, hlist, _⟩ := List.lookup_eq_some_iff.mp hlookup
    simp only [hlist, List.mem_append, List.mem_cons, true_or, or_true]
  obtain ⟨hpos, _, _, hfree⟩ := hinv.2.storedKeys s'.stB.req.reqEpoch secretKey hmem
  refine ⟨?_, ?_⟩
  · rw [ht]
    omega
  · simpa only [ht] using hfree

end oppBiKemCKA
