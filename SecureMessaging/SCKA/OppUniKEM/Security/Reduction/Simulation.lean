/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Sources
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Relation
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Oracle
import ToVCVio.OracleComp.SimSemantics.StateT.Stop

/-!
# The simulation theorem

**Setting.** Assume deterministic decapsulation and correct erasure codes. Fix supported material
`m`, a selected epoch `e`, and a challenge key `kStar`.

**Definitions.** `pinnedKey m e s`: every key that B records at epoch `e` is `m.on.1.2`.

**Results.**

- `honestScheme_preserves_simulationInv`, `honestScheme_preserves_pinnedKey`: for every challenge
  oracle that records challenges, the games on `honestScheme m e` preserve
  `reachableInv ∧ pinnedSources m e` and `pinnedKey m e`.
- `run_eq_honestStopped`: `run adv e m.pk m.ciphertext kStar` and the honest intermediate game
  stopped after the first query exposing `e` return `true` with equal probability.
- `fixedBranch_eq_honestStopped`: `fixedBranch adv e b` is the stopped honest game averaged over
  complete material, with challenge key `m.on.1.2` if `b = true` and an independent uniform key
  otherwise.
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
      (sendB (Pinned.kem m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (decide (s.stB.t = e))
              (s.keyB s.stA.t))
        (Pinned.onOff m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (decide (s.stB.t = e))
         (s.keyB s.stA.t))
        ecCt0 ecCt1 s.stB)) : k = m.on.1.2 := by
  have he : s.stB.t = e := (sendB_key_fresh
    (Pinned.kem m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (decide (s.stB.t = e))
     (s.keyB s.stA.t))
    (Pinned.onOff m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (decide (s.stB.t = e))
     (s.keyB s.stA.t))
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
  apply SCKAScheme.correctnessImpl_preserves_keyBInv_at _
    (fun keyB => ∀ k, keyB e = some k → k = m.on.1.2) s hs ?_ ?_ t z hz
  · intro tI k msg t next hout k' hk'
    by_cases he : tI = e
    · subst tI
      simp only [Function.update_self, Option.some.injEq] at hk'
      exact hk' ▸ sendB_selected_key ecCt0 ecCt1 m e s k msg t next hout
    · exact hs k' (by simpa [Function.update, Ne.symm he] using hk')
  · intro msg tI k t next hr
    exact absurd (recvB_key_none base onoff ecEk s.stB msg _ t next hr) (Option.some_ne_none _)

/-- For every material value, selected epoch, and challenge oracle `chall` that records
challenges, the pinned protocol game preserves the selected recorded key. -/
theorem honestScheme_preserves_pinnedKey
    [DecidableEq K] [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (chall : QueryImpl (ℕ →ₒ Option K)
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp))
    (hchall : SCKAScheme.RecordsChallenges chall) :
    QueryImpl.PreservesInv
      (securityImplAt base onoff leak (honestScheme ecEk ecCt0 ecCt1 m e) chall)
      (pinnedKey m e) :=
  securityImplAt_preservesInv base onoff leak _ chall (pinnedKey m e) (fun _ _ _ h => h)
    (fun _ => sendArleak_forget (onoff := Pinned.onOff m _ _ _ _) _ _ _)
    (fun _ => sendBrleak_forget (onoff := Pinned.onOff m _ _ _ _) _ _ _ _) hchall
    (fun s hs t => honestCorrectness_preserves_pinnedKey ecEk ecCt0 ecCt1 m e t s hs)

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

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type} [DecidableEq K] [DecidableEq Sym]

/-- Assume supported material and correct erasure codes. For every state
satisfying transcript consistency and the fixed-source invariant, every
supported correctness-interface query in the pinned game preserves the
original transcript invariant. -/
theorem honestCorrectness_preserves_reachableInv
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (hm : m ∈ support (sampleMaterial leak)) (e : ℕ)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hsrc : pinnedSources m e s)
    (z : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Range t ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.sckaCorrectnessImpl (honestScheme ecEk ecCt0 ecCt1 m e s) t).run s)) :
    reachableInv base onoff ecEk ecCt0 ecCt1 z.2 := by
  rcases t with ((((n | u) | u) | n) | n)
  · exact SCKAScheme.oracleUnif_preservesInv _ n s hs z hz
  · cases u
    exact oracleSendA_preserves_reachableInv base onoff hDet ecEk ecCt0 ecCt1 leak
      ecEk.ec.nchunk_pos () s hs z
      (oracleSendA_pinned_support base onoff hDet ecEk ecCt0 ecCt1 leak m hm e s z hz)
  · cases u
    exact oracleSendB_preserves_reachableInv base onoff hDet ecEk ecCt0 ecCt0.ec.nchunk_pos
      ecCt1 ecCt1.ec.nchunk_pos leak () s hs z
      (oracleSendB_pinned_support base onoff hDet ecEk ecCt0 ecCt1 leak
        m hm e s hs hsrc z hz)
  · apply oracleRecvAIdeal_preserves_reachableInv base onoff hDet ecEk ecCt0 hCt0
      ecCt1 hCt1 leak n s hs z
    have heq :
        (SCKAScheme.oracleRecvA (honestScheme ecEk ecCt0 ecCt1 m e s) n).run s =
        (oracleRecvAIdeal base onoff hDet ecEk ecCt0 ecCt1 leak n).run s := by
      change (SCKAScheme.oracleRecvA _ n).run s =
        (SCKAScheme.oracleRecvA (schemeWithDecaps base onoff hDet ecEk ecCt0 ecCt1 leak
          (fun _ _ => s.keyB s.stA.t)) n).run s
      simp only [SCKAScheme.oracleRecvA, StateT.run_bind, StateT.run_get, pure_bind]
      simp_rw [honest_recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak m e s]
      rfl
    exact heq ▸ hz
  · exact oracleRecvB_preserves_reachableInv base onoff hDet ecEk hEk ecEk.ec.nchunk_pos
      ecCt0 ecCt1 leak n s hs z hz

/-- Assume supported material and correct erasure codes. For every challenge oracle `chall`
that records challenges, the pinned protocol game preserves transcript consistency together
with `pinnedSources m e`. -/
theorem honestScheme_preserves_simulationInv
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (hm : m ∈ support (sampleMaterial leak)) (e : ℕ)
    (chall : QueryImpl (ℕ →ₒ Option K)
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp))
    (hchall : SCKAScheme.RecordsChallenges chall) :
    QueryImpl.PreservesInv
      (securityImplAt base onoff leak (honestScheme ecEk ecCt0 ecCt1 m e) chall)
      (fun s => reachableInv base onoff ecEk ecCt0 ecCt1 s ∧ pinnedSources m e s) :=
  securityImplAt_preservesInv base onoff leak _ chall _
    (fun _ E C h => ⟨reachableInv_with_security_bookkeeping h.1 E C, h.2⟩)
    (fun _ => sendArleak_forget (onoff := Pinned.onOff m _ _ _ _) _ _ _)
    (fun _ => sendBrleak_forget (onoff := Pinned.onOff m _ _ _ _) _ _ _ _) hchall
    (fun s hs t z hz => ⟨honestCorrectness_preserves_reachableInv base onoff hDet ecEk hEk
      ecCt0 hCt0 ecCt1 hCt1 leak m hm e t s hs.1 hs.2 z hz,
      honestCorrectness_preserves_pinnedSources ecEk ecCt0 ecCt1 m e t s hs.2 z hz⟩)


end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- For every supported material value, supplied key, and adversary, the
symbolic and stopped honest runs have equal acceptance probabilities from
related states satisfying transcript consistency, `pinnedSources`, and
non-exposure of the selected epoch. -/
theorem optionRun_mark_eq
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (hm : m ∈ support (sampleMaterial leak)) (e : ℕ) (kStar : K)
    (adv : SecurityAdversary leak Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s)
    (hsrc : pinnedSources m e s) (he : e ∉ s.exposed) :
    Pr[= true | optionRun
      (oracle base onoff ecEk ecCt0 ecCt1 leak e m.keygen.1.1 m.ciphertext kStar)
      adv (markState e s)] =
    Pr[= true | optionRun (honestStopped base onoff ecEk ecCt0 ecCt1 leak m e kStar)
      adv s] := by
  apply probOutput_optionRun_eq_of_state_map _ _ (markState e)
    (fun s => (reachableInv base onoff ecEk ecCt0 ecCt1 s ∧ pinnedSources m e s) ∧
      e ∉ s.exposed)
  · intro t s hs z hz hcont
    change z ∈ support (do
      let out ← (honestOracle base onoff ecEk ecCt0 ecCt1 leak m e kStar t).run s
      pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2)) at hz
    obtain ⟨out, hout, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    obtain rfl := (mem_support_pure_iff _ _).mp hz
    have hex : e ∉ out.2.exposed := by
      by_contra h
      simp only [h, decide_true, ↓reduceIte, Option.isSome_none, Bool.false_eq_true] at hcont
    exact ⟨honestScheme_preserves_simulationInv base onoff hDet ecEk hEk ecCt0 hCt0
      ecCt1 hCt1 leak m hm e _ (pinnedChallenge_recordsChallenges onoff e kStar)
      t s hs.1 out hout, hex⟩
  · intro t s hs
    exact oracle_mark base onoff ecEk ecCt0 ecCt1 leak m e kStar t s hs.1.1 hs.2
  · exact ⟨⟨hs, hsrc⟩, he⟩

omit [DecidableEq K] [DecidableEq Sym] [SampleableType K] in
/-- For every selected epoch, marking the honest initial state yields
exactly the simulator's initial state. All private fields and key tables
are absent, so every marker is absent as well. -/
theorem markState_initial
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure) (e : ℕ) :
    markState e (oppUniKemCKA.Reduction.Internal.initialGame (Sym := Sym) base onoff) =
      initial onoff := by
  simp [markState, markA, markB, initial, oppUniKemCKA.Reduction.Internal.initialGame,
    oppUniKemCKA.Reduction.Internal.initialA, oppUniKemCKA.Reduction.Internal.initialB,
    SCKAScheme.initGameState]

/-- Assume deterministic decapsulation and correct erasure codes. For every
supported material value, selected epoch, supplied key, and adversary, the
explicit simulator's acceptance probability equals that of the stopped
honest intermediate game from its initial state. -/
theorem run_eq_honestStopped
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (hm : m ∈ support (sampleMaterial leak)) (e : ℕ) (kStar : K)
    (adv : SecurityAdversary leak Sym) :
    Pr[= true | run base onoff ecEk ecCt0 ecCt1 leak adv e m.keygen.1.1 m.ciphertext kStar] =
    Pr[= true | optionRun (honestStopped base onoff ecEk ecCt0 ecCt1 leak m e kStar)
      adv (oppUniKemCKA.Reduction.Internal.initialGame base onoff)] := by
  have hrun : run base onoff ecEk ecCt0 ecCt1 leak adv e m.keygen.1.1 m.ciphertext kStar =
      optionRun (oracle base onoff ecEk ecCt0 ecCt1 leak e
        m.keygen.1.1 m.ciphertext kStar) adv (initial onoff) := by
    simp [run, optionRun, StateT.run'_eq, bind_pure_comp, Functor.map_map]
  rw [hrun, ← markState_initial base onoff e]
  exact optionRun_mark_eq base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
    leak m hm e kStar adv _
    (reachableInv_init base onoff ecEk ecCt0 ecCt1 ecEk.ec.nchunk_pos ecCt0.ec.nchunk_pos)
    (pinnedSources_initial base onoff leak m e)
    (by simp [oppUniKemCKA.Reduction.Internal.initialGame, SCKAScheme.initGameState])


/-- For every adversary, selected epoch, and KEM bit `b`, the reduction's
fixed branch has the same acceptance probability as: sample complete
material and a uniform key, then run the stopped honest game with the
material key for `b = true` and the uniform key for `b = false`. -/
theorem fixedBranch_eq_honestStopped
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff)
    (adv : SecurityAdversary leak Sym) (e : ℕ) (b : Bool) :
    Pr[= true | fixedBranch base onoff ecEk ecCt0 ecCt1 leak adv e b] =
    Pr[= true | do
      let m ← sampleMaterial leak
      let k ← ($ᵗ K : ProbComp K)
      optionRun (honestStopped base onoff ecEk ecCt0 ecCt1 leak m e
        (if b then m.on.1.2 else k)) adv
        (oppUniKemCKA.Reduction.Internal.initialGame base onoff)] := by
  rw [fixedBranch_eq_material]
  apply probOutput_bind_congr
  intro m hm
  apply probOutput_bind_congr
  intro k _
  exact run_eq_honestStopped base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
    leak m hm e _ adv

end oppUniKemCKA.Security.Embedding
