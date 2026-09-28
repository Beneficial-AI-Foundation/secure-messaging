/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Sources
import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction.Receive
import SecureMessaging.SCKA.Security.Bookkeeping
import SecureMessaging.SCKA.Security.Leakage

/-!
# Preservation of selected-epoch source material

**Statement.** Every supported ordinary send and every successful receive
in the honest intermediate game preserves `pinnedSources m e` when applied
to the corresponding local state.

**Proof.** Selected key generation and offline encapsulation install the
stored material. Other send branches retain the relevant fields. Receive
shape lemmas from correctness show that each receive either retains these
fields and its epoch or advances the epoch and erases the private field.
Erasure satisfies the source invariant at the new epoch.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- For every material value, selected epoch, and state satisfying the
source invariant, every supported pinned A-send preserves that invariant
when its successor replaces A's local state. -/
theorem sendA_preserves_pinnedSources
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff}
    (ecEk : ErasureCodePayload PK Sym) (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : pinnedSources m e s) (key : Option (ℕ × K)) (msg : Message Sym)
    (t : ℕ) (next : StA onoff Sym)
    (hout : some (key, msg, t, next) ∈ support
      (sendA (Pinned.kem m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (s.keyB s.stA.t))
        (Pinned.onOff m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (s.keyB s.stA.t))
        ecEk s.stA)) :
    pinnedSources m e { s with stA := next } := by
  by_cases he : s.stA.t = e <;> cases hd : s.stA.dkA <;>
    cases hp : s.stA.ekA <;> cases ha : s.stA.ack.ekRec
  all_goals
    simp only [sendA, hd, hp, ha, Bool.false_eq_true, ↓reduceIte, pure_bind] at hout
    try dsimp only [Pinned.kem, Pinned.onOff] at hout
    simp only [Pinned.keygen, he, decide_true, decide_false, ↓reduceIte, pure_bind,
      mem_support_bind_iff, mem_support_pure_iff, Prod.exists,
      Option.some.injEq, Prod.mk.injEq] at hout
    simp_all [pinnedSources] <;> aesop

set_option maxHeartbeats 800000 in
-- The phase split tracks the offline fields through both online-sampling branches.
/-- For every material value, selected epoch, and state satisfying the
source invariant, every supported pinned B-send preserves that invariant
when its successor replaces B's local state. -/
theorem sendB_preserves_pinnedSources
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff}
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : pinnedSources m e s) (key : Option (ℕ × K)) (msg : Message Sym)
    (t : ℕ) (next : StB onoff Sym)
    (hout : some (key, msg, t, next) ∈ support
      (sendB (Pinned.kem m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (s.keyB s.stA.t))
        (Pinned.onOff m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (s.keyB s.stA.t))
        ecCt0 ecCt1 s.stB)) :
    pinnedSources m e { s with stB := next } := by
  by_cases he : s.stB.t = e <;> cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;>
    cases hc1 : s.stB.ct1 <;> cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
  all_goals
    simp only [sendB, hc0, hp, hc1, hst, ha, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, pure_bind] at hout
    try dsimp only [Pinned.kem, Pinned.onOff] at hout
    simp only [Pinned.encapsOff, Pinned.encapsOn, he, decide_true, decide_false,
      ↓reduceIte, pure_bind, mem_support_bind_iff, mem_support_pure_iff,
      Prod.exists, Option.some.injEq, Prod.mk.injEq] at hout
    simp_all [pinnedSources] <;> aesop

/-- For every deterministic-decapsulation receive by A, replacing its local
state by a successful successor preserves selected source material. This
uses the receive shape lemma independently of erasure-code correctness. -/
theorem recvA_preserves_pinnedSources [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : pinnedSources m e s) (msg : Message Sym) (key : Option (ℕ × K))
    (t : ℕ) (next : StA onoff Sym)
    (hout : recvA base onoff hDet ecCt0 ecCt1 s.stA msg = some (key, t, next)) :
    pinnedSources m e { s with stA := next } := by
  obtain h | h := oppUniKemCKA.Reduction.Internal.recvA_kem_source_shape
    base onoff hDet ecCt0 ecCt1 s.stA msg key t next hout
  · exact ⟨by simpa only [h.1, h.2.1, h.2.2] using hs.1, hs.2⟩
  · exact ⟨by simp [h.2.2.1], hs.2⟩

/-- For every receive by B, replacing its local state by a successful
successor preserves selected offline material: it is retained in the same
epoch or erased on advancement. -/
theorem recvB_preserves_pinnedSources [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : pinnedSources m e s) (msg : Message Sym) (key : Option (ℕ × K))
    (t : ℕ) (next : StB onoff Sym)
    (hout : recvB base onoff ecEk s.stB msg = some (key, t, next)) :
    pinnedSources m e { s with stB := next } := by
  obtain h | h := oppUniKemCKA.Reduction.Internal.recvB_kem_source_shape
    base onoff ecEk s.stB msg key t next hout
  · exact ⟨hs.1, by simpa only [h.1, h.2.1, h.2.2.1] using hs.2⟩
  · exact ⟨hs.1, by simp [h.2.1]⟩

/-- For every state satisfying `pinnedSources m e` and every query in the
correctness interface, every supported honest pinned successor also
satisfies that invariant. Message delivery is indexed by the existing
tables and may repeat any available index. -/
theorem honestCorrectness_preserves_pinnedSources [DecidableEq K] [DecidableEq Sym]
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff}
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (m : Material leak) (e : ℕ)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : pinnedSources m e s)
    (z : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Range t ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.sckaCorrectnessImpl (honestScheme ecEk ecCt0 ecCt1 m e s) t).run s)) :
    pinnedSources m e z.2 := by
  rcases t with ((((n | u) | u) | n) | n)
  · have hz' : ∃ r, (r, s) = z := by
      simpa [SCKAScheme.sckaCorrectnessImpl, SCKAScheme.oracleUnif] using hz
    obtain ⟨_, rfl⟩ := hz'
    exact hs
  · cases u
    simp only [SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl,
      QueryImpl.add_apply_inr, SCKAScheme.oracleSendA,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      bind_assoc, pure_bind, mem_support_bind_iff] at hz
    obtain ⟨out, hout, hz⟩ := hz
    cases out with
    | none => simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
    | some out =>
      rcases out with ⟨key, msg, t, next⟩
      have hnext := sendA_preserves_pinnedSources ecEk m e s hs key msg t next hout
      cases key <;>
        simp only [StateT.run_bind, StateT.run_set, pure_bind,
          StateT.run_pure, mem_support_pure_iff] at hz
      all_goals obtain rfl := hz; exact hnext
  · cases u
    simp only [SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl,
      QueryImpl.add_apply_inr, SCKAScheme.oracleSendB,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      bind_assoc, pure_bind, mem_support_bind_iff] at hz
    obtain ⟨out, hout, hz⟩ := hz
    cases out with
    | none => simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
    | some out =>
      rcases out with ⟨key, msg, t, next⟩
      have hnext := sendB_preserves_pinnedSources ecCt0 ecCt1 m e s hs key msg t next hout
      cases key <;>
        simp only [StateT.run_bind, StateT.run_set, pure_bind,
          StateT.run_pure, mem_support_pure_iff] at hz
      all_goals obtain rfl := hz; exact hnext
  · simp only [SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl,
      QueryImpl.add_apply_inr, SCKAScheme.oracleRecvA,
      StateT.run_bind, StateT.run_get, pure_bind] at hz
    cases hm : s.msgB n with
    | none =>
      simp only [hm, StateT.run_pure, mem_support_pure_iff] at hz
      obtain rfl := hz
      exact hs
    | some entry =>
      rcases entry with ⟨msg, tsnd⟩
      simp only [hm] at hz
      cases hr : (honestScheme ecEk ecCt0 ecCt1 m e s).recvA s.stA msg with
      | none =>
        simp only [hr, StateT.run_bind, StateT.run_set, pure_bind,
          StateT.run_pure, mem_support_pure_iff] at hz
        obtain rfl := hz
        exact hs
      | some out =>
        rcases out with ⟨key, t, next⟩
        have hshape := oppUniKemCKA.Reduction.Internal.recvA_kem_source_shape
          (Pinned.kem m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (s.keyB s.stA.t))
          (Pinned.onOff m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (s.keyB s.stA.t))
          (Pinned.deterministic m (decide (s.stA.t = e)) (decide (s.stB.t = e))
            (s.keyB s.stA.t)) ecCt0 ecCt1 s.stA msg key t next hr
        have hnext : pinnedSources m e { s with stA := next } := by
          rcases hshape with h | h
          · exact ⟨by simpa only [h.1, h.2.1, h.2.2] using hs.1, hs.2⟩
          · exact ⟨by simp [h.2.2.1], hs.2⟩
        cases key <;>
          simp only [hr, StateT.run_bind, StateT.run_set, pure_bind,
            StateT.run_pure, mem_support_pure_iff] at hz
        all_goals obtain rfl := hz; exact hnext
  · simp only [SCKAScheme.sckaCorrectnessImpl,
      QueryImpl.add_apply_inr, SCKAScheme.oracleRecvB,
      StateT.run_bind, StateT.run_get, pure_bind] at hz
    cases hm : s.msgA n with
    | none =>
      simp only [hm, StateT.run_pure, mem_support_pure_iff] at hz
      obtain rfl := hz
      exact hs
    | some entry =>
      rcases entry with ⟨msg, tsnd⟩
      simp only [hm] at hz
      cases hr : (honestScheme ecEk ecCt0 ecCt1 m e s).recvB s.stB msg with
      | none =>
        simp only [hr, StateT.run_bind, StateT.run_set, pure_bind,
          StateT.run_pure, mem_support_pure_iff] at hz
        obtain rfl := hz
        exact hs
      | some out =>
        rcases out with ⟨key, t, next⟩
        have hnext := recvB_preserves_pinnedSources base onoff ecEk leak
          m e s hs msg key t next hr
        cases key <;>
          simp only [hr, StateT.run_bind, StateT.run_set, pure_bind,
            StateT.run_pure, mem_support_pure_iff] at hz
        all_goals obtain rfl := hz; exact hnext

/-- For every material value, selected epoch, and supplied challenge key,
the full honest intermediate oracle preserves `pinnedSources`. Leaking
sends inherit ordinary-send preservation through their marginal laws;
exposure and challenge bookkeeping retains the local source fields. -/
theorem honestOracle_preserves_pinnedSources
    [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (kStar : K) :
    QueryImpl.PreservesInv (honestOracle base onoff ecEk ecCt0 ecCt1 leak m e kStar)
      (pinnedSources m e) := by
  intro t s hs z hz
  simp only [honestOracle, StateT.run_bind, StateT.run_get, pure_bind] at hz
  rcases t with (((((t | u) | u) | t) | u) | u)
  · exact honestCorrectness_preserves_pinnedSources ecEk ecCt0 ecCt1 m e t s hs z hz
  · cases u
    apply SCKAScheme.oracleSendArleak_preservesInv_at
      (honestScheme ecEk ecCt0 ecCt1 m e s) sendExposureA _
      (pinnedSources (base := base) (onoff := onoff) (leak := leak) m e)
      (fun _ _ h => h) s hs _ z hz
    · exact sendArleak_forget _ _ _ _
    · exact honestCorrectness_preserves_pinnedSources ecEk ecCt0 ecCt1 m e
        SCKAScheme.sckaCorrectnessSpec.OSendA s hs
  · cases u
    apply SCKAScheme.oracleSendBrleak_preservesInv_at
      (honestScheme ecEk ecCt0 ecCt1 m e s) sendExposureB _
      (pinnedSources (base := base) (onoff := onoff) (leak := leak) m e)
      (fun _ _ h => h) s hs _ z hz
    · exact sendBrleak_forget _ _ _ _ _
    · exact honestCorrectness_preserves_pinnedSources ecEk ecCt0 ecCt1 m e
        SCKAScheme.sckaCorrectnessSpec.OSendB s hs
  · simp only [pinnedChallenge, StateT.run_bind, StateT.run_get, pure_bind] at hz
    repeat' split at hz
    all_goals
      simp only [StateT.run_pure, StateT.run_bind, StateT.run_map, StateT.run_set,
        StateT.run_monadLift, monadLift_self, bind_pure_comp, map_pure, Functor.map_map,
        mem_support_pure_iff, support_map, support_uniformSample,
        Set.image_univ, Set.mem_range] at hz
    all_goals
      first
      | obtain rfl := hz
      | obtain ⟨_, rfl⟩ := hz
    all_goals exact hs
  · exact SCKAScheme.oracleCorruptA_preservesInv (vulnA base onoff)
      (pinnedSources m e) (fun _ _ h => h) u s hs z hz
  · exact SCKAScheme.oracleCorruptB_preservesInv (vulnB base onoff)
      (pinnedSources m e) (fun _ _ h => h) u s hs z hz

/-- For every material value and selected epoch, the honest initial game
state satisfies `pinnedSources`, since both private source fields are absent. -/
theorem pinnedSources_initial
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (leak : base.OnOffRandLeak onoff) (m : Material leak) (e : ℕ) :
    pinnedSources (Sym := Sym) m e
      (oppUniKemCKA.Reduction.Internal.initialGame base onoff) := by
  simp [pinnedSources, oppUniKemCKA.Reduction.Internal.initialGame,
    oppUniKemCKA.Reduction.Internal.initialA, oppUniKemCKA.Reduction.Internal.initialB,
    SCKAScheme.initGameState]

end oppUniKemCKA.Security.Embedding
