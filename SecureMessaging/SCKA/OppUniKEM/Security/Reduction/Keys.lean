/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.SourcePreservation
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Receive
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.SendShape

/-!
# Honest keys at the selected epoch

**Predicate.** `pinnedKey m e s` states that every key recorded by B at
epoch `e` equals the selected online sample's key `m.on.1.2`.

**Statement.** The honest intermediate game preserves this predicate for
every supplied challenge key. Transcript consistency then gives the same
property for A's key table.

**Proof.** B records a key only when online encapsulation first completes.
At the selected epoch that sampler returns `m.on`. Other queries retain
B's table, and challenges change only the challenged set. This identifies
the real selected challenge with its honest recorded key while retaining
a separate, possibly random, supplied challenge response.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- Every key recorded in B's table at selected epoch `e` equals the key
in material value `m`. An absent table entry satisfies the predicate. -/
def pinnedKey {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) : Prop :=
  ∀ k, s.keyB e = some k → k = m.on.1.2

set_option maxHeartbeats 800000 in
-- Each send phase is inspected, including combined offline/online sampling.
/-- For every fixed material value and state, a pinned B-send deriving a
key at the selected epoch returns exactly `m.on.1.2`. -/
theorem sendB_selected_key
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff}
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (k : K) (msg : Message Sym) (t : ℕ) (next : StB onoff Sym)
    (hout : some (some (e, k), msg, t, next) ∈ support
      (sendB (Pinned.kem m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (s.keyB s.stA.t))
        (Pinned.onOff m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (s.keyB s.stA.t))
        ecCt0 ecCt1 s.stB)) : k = m.on.1.2 := by
  have he : s.stB.t = e := (sendB_key_fresh
    (Pinned.kem m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (s.keyB s.stA.t))
    (Pinned.onOff m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (s.keyB s.stA.t))
    ecCt0 ecCt1 s.stB e k msg t next hout).1.symm
  cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;>
    cases hc1 : s.stB.ct1 <;> cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
  all_goals
    simp only [sendB, hc0, hp, hc1, hst, ha, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, pure_bind, Pinned.onOff, Pinned.encapsOff,
      Pinned.encapsOn, he, decide_true, mem_support_pure_iff,
      Option.some.injEq, Prod.mk.injEq] at hout
    simp_all

/-- For every fixed material value, state satisfying `pinnedKey`, and
correctness-interface query, each supported honest pinned successor
satisfies `pinnedKey`. -/
theorem honestCorrectness_preserves_pinnedKey [DecidableEq K] [DecidableEq Sym]
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff}
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (m : Material leak) (e : ℕ)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : pinnedKey m e s)
    (z : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Range t ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.sckaCorrectnessImpl (honestScheme ecEk ecCt0 ecCt1 m e s) t).run s)) :
    pinnedKey m e z.2 := by
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
    obtain ⟨out, _, hz⟩ := hz
    cases out with
    | none => simpa using (mem_support_pure_iff _ _).mp hz ▸ hs
    | some out =>
      rcases out with ⟨key, msg, t, next⟩
      cases key <;>
        simp only [StateT.run_bind, StateT.run_set, pure_bind,
          StateT.run_pure, mem_support_pure_iff] at hz
      all_goals obtain rfl := hz; exact hs
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
      cases key with
      | none =>
        simp only [StateT.run_bind, StateT.run_set, pure_bind,
          StateT.run_pure, mem_support_pure_iff] at hz
        obtain rfl := hz
        exact hs
      | some key =>
        rcases key with ⟨epoch, k⟩
        simp only [StateT.run_bind, StateT.run_set, pure_bind,
          StateT.run_pure, mem_support_pure_iff] at hz
        obtain rfl := hz
        intro k' hk'
        by_cases he : epoch = e
        · subst epoch
          have hk := sendB_selected_key ecCt0 ecCt1 m e s k msg t next hout
          simp only [Function.update_self, Option.some.injEq] at hk'
          exact hk' ▸ hk
        · exact hs k' (by simpa [Function.update, Ne.symm he] using hk')
  · simp only [SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl,
      QueryImpl.add_apply_inr, SCKAScheme.oracleRecvA,
      StateT.run_bind, StateT.run_get, pure_bind] at hz
    repeat' split at hz
    all_goals
      simp only [StateT.run_bind, StateT.run_set, pure_bind,
        StateT.run_pure, mem_support_pure_iff] at hz
      obtain rfl := hz
      exact hs
  · simp only [SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inr,
      SCKAScheme.oracleRecvB, StateT.run_bind, StateT.run_get, pure_bind] at hz
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
        have hk := recvB_key_none base onoff ecEk s.stB msg key t next hr
        subst key
        simp only [hr, StateT.run_bind, StateT.run_set, pure_bind,
          StateT.run_pure, mem_support_pure_iff] at hz
        obtain rfl := hz
        exact hs

/-- For every material value, selected epoch, and supplied challenge key,
the full honest intermediate oracle preserves the selected recorded key. Leaking
sends inherit ordinary-send preservation through their marginal laws;
exposure and challenge bookkeeping retains the recorded key tables. -/
theorem honestOracle_preserves_pinnedKey
    [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (kStar : K) :
    QueryImpl.PreservesInv (honestOracle base onoff ecEk ecCt0 ecCt1 leak m e kStar)
      (pinnedKey m e) := by
  intro t s hs z hz
  simp only [honestOracle, StateT.run_bind, StateT.run_get, pure_bind] at hz
  rcases t with (((((t | u) | u) | t) | u) | u)
  · exact honestCorrectness_preserves_pinnedKey ecEk ecCt0 ecCt1 m e t s hs z hz
  · cases u
    apply SCKAScheme.oracleSendArleak_preservesInv_at
      (honestScheme ecEk ecCt0 ecCt1 m e s) sendExposureA _
      (pinnedKey (base := base) (onoff := onoff) (leak := leak) m e)
      (fun _ _ h => h) s hs _ z hz
    · exact sendArleak_forget _ _ _ _
    · exact honestCorrectness_preserves_pinnedKey ecEk ecCt0 ecCt1 m e
        SCKAScheme.sckaCorrectnessSpec.OSendA s hs
  · cases u
    apply SCKAScheme.oracleSendBrleak_preservesInv_at
      (honestScheme ecEk ecCt0 ecCt1 m e s) sendExposureB _
      (pinnedKey (base := base) (onoff := onoff) (leak := leak) m e)
      (fun _ _ h => h) s hs _ z hz
    · exact sendBrleak_forget _ _ _ _ _
    · exact honestCorrectness_preserves_pinnedKey ecEk ecCt0 ecCt1 m e
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
      (pinnedKey m e) (fun _ _ h => h) u s hs z hz
  · exact SCKAScheme.oracleCorruptB_preservesInv (vulnB base onoff)
      (pinnedKey m e) (fun _ _ h => h) u s hs z hz

/-- For every material value and selected epoch, the honest initial game
state satisfies `pinnedKey`, since B's key table is empty. -/
theorem pinnedKey_initial
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (leak : base.OnOffRandLeak onoff) (m : Material leak) (e : ℕ) :
    pinnedKey (Sym := Sym) m e
      (oppUniKemCKA.Reduction.Internal.initialGame base onoff) := by
  simp [pinnedKey, oppUniKemCKA.Reduction.Internal.initialGame,
    oppUniKemCKA.Reduction.Internal.initialA, oppUniKemCKA.Reduction.Internal.initialB,
    SCKAScheme.initGameState]


/-- For every transcript-consistent state and epoch, a key recorded by A
is recorded with the same value by B. -/
theorem recordedA_eq_recordedB
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s)
    (e : ℕ) (k : K) (hk : s.keyA e = some k) : s.keyB e = some k := by
  obtain ⟨T, hT⟩ := hs
  rw [hT.keyA] at hk
  split_ifs at hk with hzero hpast
  simpa only [hT.keyB] using hk

/-- In every transcript-consistent state satisfying `pinnedKey m e`, each
key recorded by either party at epoch `e` equals `m.on.1.2`. -/
theorem pinnedKey_both
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hm : pinnedKey m e s)
    (k : K) (hk : s.keyA e = some k ∨ s.keyB e = some k) : k = m.on.1.2 := by
  apply hm k
  exact hk.elim (recordedA_eq_recordedB base onoff ecEk ecCt0 ecCt1 s hs e k) id

/-- If each selected-epoch table entry equals `kStar`, then for every query
index the pinned challenge with response `kStar` equals the ordinary challenge
randomizing precisely the positive epochs strictly below `e`. -/
theorem pinnedChallenge_eq_recorded [SampleableType K]
    {base : KEMScheme ProbComp K PK SK C} (onoff : base.OnOffStructure)
    (e : ℕ) (kStar : K) (t : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hkey : ∀ k, s.keyA e = some k ∨ s.keyB e = some k → k = kStar) :
    (pinnedChallenge onoff e kStar t).run s =
      (SCKAScheme.oracleChall (decide (0 < t ∧ t < e))
        (StA onoff Sym) (StB onoff Sym) K (Message Sym) t).run s := by
  by_cases hg : t ∈ s.exposed ∨ t ∈ s.challenged
  · simp [pinnedChallenge, SCKAScheme.oracleChall, hg]
  · by_cases ht : t = e
    · subst t
      cases hA : s.keyA e with
      | none =>
        cases hB : s.keyB e with
        | none => simp [pinnedChallenge, SCKAScheme.oracleChall, hg, hA, hB]
        | some k =>
          have hk := hkey k (.inr hB)
          subst k
          simp [pinnedChallenge, SCKAScheme.oracleChall, hg, hA, hB]
      | some k =>
        have hk := hkey k (.inl hA)
        subst k
        simp [pinnedChallenge, SCKAScheme.oracleChall, hg, hA]
    · cases hA : s.keyA t <;> cases hB : s.keyB t <;> by_cases hr : 0 < t ∧ t < e <;>
        simp [pinnedChallenge, SCKAScheme.oracleChall, hg, hA, hB, ht, hr]

end oppUniKemCKA.Security.Embedding
