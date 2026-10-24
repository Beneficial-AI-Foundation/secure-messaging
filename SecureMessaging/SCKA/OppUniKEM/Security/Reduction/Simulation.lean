/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Game
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Relation
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Oracle
import ToVCVio.OracleComp.SimSemantics.StateT.Stop

/-!
# The simulation theorem

**Setting.** Throughout this module, we consider:

- an SCKA adversary `adv`, a challenge epoch `e`, a candidate key `kStar : K`, and the initial
  game state `s₀`;
- a KEM material `kemMat` (`Simulator`), that is, pre-sampled outputs and coins of the three
  sampling phases of one epoch, with public key `kemMat.pk`, ciphertext `kemMat.ciphertext`, and
  encapsulated key `kemMat.key`, drawn by `sampleMaterial leak` as the protocol samples them;
- the simulator run `run adv e pk ct kStar` (`Simulator`), which runs `adv` against the simulator
  with the IND-CPA challenge `(pk, ct, kStar)` embedded at epoch `e`, and outputs `false` if the
  simulator halts;
- the fixed branch `fixedBranch adv e b` (`Simulator`), that is, the reduction `𝓑` with challenge
  epoch `e` and IND-CPA bit `b`, which runs `run` on a fresh challenge whose key is the
  encapsulated key if `b` and a uniform key otherwise;
- the stopped honest game `honestStopped kemMat e kStar` (`Game`), which runs the security game with
  the samples of epoch `e` taken from `kemMat` and challenges at `e` answered with `kStar`, and
  stops at the first exposure of `e`.

**Main results.**

- For a fixed KEM material `kemMat`, the simulator has the acceptance probability of the stopped
  honest game: for `kemMat ∈ support (sampleMaterial leak)`,
  `Pr[run adv e kemMat.pk kemMat.ciphertext kStar = true] =
  Pr[optionRun (honestStopped kemMat e kStar) adv s₀ = true]` (`run_eq_honestStopped`).

- Averaged over the KEM material, each fixed branch has the acceptance probability of the stopped
  honest game:
  `Pr[fixedBranch adv e b = true]` equals
  `Pr[kemMat ← sampleMaterial leak; k ←$ K; optionRun (honestStopped kemMat e k_b) adv s₀ = true]`,
  where `k_b := if b then kemMat.key else k` (`fixedBranch_eq_honestStopped`).
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- If B's send in `honestScheme kemMat e s` can output a key `k` at epoch `e`, then
`k = kemMat.key`. -/
private theorem sendB_selected_key
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff}
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (k : K) (msg : Message Sym) (t : ℕ) (next : StB onoff Sym)
    (hout : some (some (e, k), msg, t, next) ∈ support
      (sendB (honestKem kemMat e s) (honestOnOff kemMat e s)
        ecCt0 ecCt1 s.stB)) : k = kemMat.key := by
  have he : s.stB.t = e := (sendB_key_fresh
    (honestKem kemMat e s) (honestOnOff kemMat e s)
    ecCt0 ecCt1 s.stB e k msg t next hout).1.symm
  cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;>
    cases hc1 : s.stB.ct1 <;> cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
  all_goals
    simp only [sendB, hc0, hp, hc1, hst, ha, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, pure_bind, Pinned.encapsOff,
      Pinned.encapsOn, he, decide_true, mem_support_pure_iff,
      Option.some.injEq, Prod.mk.injEq] at hout
    simp_all

/-- The correctness oracles of `honestScheme kemMat e` preserve the property that every key B
records at `e` is `kemMat.key`. -/
private theorem honestCorrectness_preserves_keyB_eq [DecidableEq K] [DecidableEq Sym]
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff}
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (kemMat : KEMMaterial leak) (e : ℕ)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : ∀ k, s.keyB e = some k → k = kemMat.key)
    (z : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Range t ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.sckaCorrectnessImpl (honestScheme ecEk ecCt0 ecCt1 kemMat e s) t).run s)) :
    ∀ k, z.2.keyB e = some k → k = kemMat.key := by
  apply SCKAScheme.correctnessImpl_preserves_keyBInv_at _
    (fun keyB => ∀ k, keyB e = some k → k = kemMat.key) s hs ?_ ?_ t z hz
  · intro tI k msg t next hout k' hk'
    by_cases he : tI = e
    · subst tI
      simp only [Function.update_self, Option.some.injEq] at hk'
      exact hk' ▸ sendB_selected_key ecCt0 ecCt1 kemMat e s k msg t next hout
    · exact hs k' (by simpa [Function.update, Ne.symm he] using hk')
  · intro msg tI k t next hr
    exact absurd (recvB_key_none base onoff ecEk s.stB msg _ t next hr) (Option.some_ne_none _)

/-- If `RecordsChallenges chall`, `securityImplAt (honestScheme kemMat e) chall` preserves the
property that every key B records at `e` is `kemMat.key`. -/
theorem honestScheme_preserves_keyB_eq
    [DecidableEq K] [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ)
    (chall : QueryImpl (ℕ →ₒ Option K)
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp))
    (hchall : SCKAScheme.RecordsChallenges chall) :
    QueryImpl.PreservesInv
      (securityImplAt base onoff leak (honestScheme ecEk ecCt0 ecCt1 kemMat e) chall)
      (fun s => ∀ k, s.keyB e = some k → k = kemMat.key) :=
  securityImplAt_preservesInv base onoff leak _ chall _ (fun _ _ _ h => h)
    (fun _ => sendArleak_forget (onoff := Pinned.onOff kemMat _ _ _ _) _ _ _)
    (fun _ => sendBrleak_forget (onoff := Pinned.onOff kemMat _ _ _ _) _ _ _ _) hchall
    (fun s hs t => honestCorrectness_preserves_keyB_eq ecEk ecCt0 ecCt1 kemMat e t s hs)

/-- In the initial game state, every key B records at `e` is `kemMat.key`, since B records none. -/
theorem keyB_eq_initial
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (leak : base.OnOffRandLeak onoff) (kemMat : KEMMaterial leak) (e : ℕ) :
    ∀ k, (oppUniKemCKA.Reduction.Internal.initialGame (Sym := Sym) base onoff).keyB e = some k →
      k = kemMat.key := by
  simp [oppUniKemCKA.Reduction.Internal.initialGame,
    oppUniKemCKA.Reduction.Internal.initialA, oppUniKemCKA.Reduction.Internal.initialB,
    SCKAScheme.initGameState]

/-- Under `reachableInv`, a key A records at epoch `e` is also recorded by B. -/
private theorem recordedA_eq_recordedB
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

/-- Under `reachableInv`, if every key B records at `e` is `kemMat.key`, then so is every key
recorded at `e` by either party. -/
theorem recorded_eq_key
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hm : ∀ k, s.keyB e = some k → k = kemMat.key)
    (k : K) (hk : s.keyA e = some k ∨ s.keyB e = some k) : k = kemMat.key := by
  apply hm k
  exact hk.elim (recordedA_eq_recordedB base onoff ecEk ecCt0 ecCt1 s hs e k) id

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type} [DecidableEq K] [DecidableEq Sym]

/-- For possible `kemMat`, the correctness oracles of `honestScheme kemMat e`
preserve `reachableInv` on states satisfying `pinnedSources kemMat e`. -/
private theorem honestCorrectness_preserves_reachableInv
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (hm : kemMat ∈ support (sampleMaterial leak)) (e : ℕ)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hsrc : pinnedSources kemMat e s)
    (z : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Range t ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.sckaCorrectnessImpl (honestScheme ecEk ecCt0 ecCt1 kemMat e s) t).run s)) :
    reachableInv base onoff ecEk ecCt0 ecCt1 z.2 := by
  rcases t with ((((n | u) | u) | n) | n)
  · exact SCKAScheme.oracleUnif_preservesInv _ n s hs z hz
  · cases u
    exact oracleSendA_preserves_reachableInv base onoff hDet ecEk ecCt0 ecCt1 leak
      ecEk.ec.nchunk_pos () s hs z
      (oracleSendA_pinned_support base onoff hDet ecEk ecCt0 ecCt1 leak kemMat hm e s z hz)
  · cases u
    exact oracleSendB_preserves_reachableInv base onoff hDet ecEk ecCt0 ecCt0.ec.nchunk_pos
      ecCt1 ecCt1.ec.nchunk_pos leak () s hs z
      (oracleSendB_pinned_support base onoff hDet ecEk ecCt0 ecCt1 leak
        kemMat hm e s hs hsrc z hz)
  · apply oracleRecvAIdeal_preserves_reachableInv base onoff hDet ecEk ecCt0 hCt0
      ecCt1 hCt1 leak n s hs z
    have heq :
        (SCKAScheme.oracleRecvA (honestScheme ecEk ecCt0 ecCt1 kemMat e s) n).run s =
        (oracleRecvAIdeal base onoff hDet ecEk ecCt0 ecCt1 leak n).run s := by
      change (SCKAScheme.oracleRecvA _ n).run s =
        (SCKAScheme.oracleRecvA (schemeWithDecaps base onoff hDet ecEk ecCt0 ecCt1 leak
          (fun _ _ => s.keyB s.stA.t)) n).run s
      simp only [SCKAScheme.oracleRecvA, StateT.run_bind, StateT.run_get, pure_bind]
      simp_rw [honest_recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak kemMat e s]
      rfl
    exact heq ▸ hz
  · exact oracleRecvB_preserves_reachableInv base onoff hDet ecEk hEk ecEk.ec.nchunk_pos
      ecCt0 ecCt1 leak n s hs z hz

/-- For possible `kemMat` and `RecordsChallenges chall`,
`securityImplAt (honestScheme kemMat e) chall` preserves `reachableInv ∧ pinnedSources kemMat e`. -/
theorem honestScheme_preserves_simulationInv
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (hm : kemMat ∈ support (sampleMaterial leak)) (e : ℕ)
    (chall : QueryImpl (ℕ →ₒ Option K)
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp))
    (hchall : SCKAScheme.RecordsChallenges chall) :
    QueryImpl.PreservesInv
      (securityImplAt base onoff leak (honestScheme ecEk ecCt0 ecCt1 kemMat e) chall)
      (fun s => reachableInv base onoff ecEk ecCt0 ecCt1 s ∧ pinnedSources kemMat e s) :=
  securityImplAt_preservesInv base onoff leak _ chall _
    (fun _ E C h => ⟨reachableInv_with_security_bookkeeping h.1 E C, h.2⟩)
    (fun _ => sendArleak_forget (onoff := Pinned.onOff kemMat _ _ _ _) _ _ _)
    (fun _ => sendBrleak_forget (onoff := Pinned.onOff kemMat _ _ _ _) _ _ _ _) hchall
    (fun s hs t z hz => ⟨honestCorrectness_preserves_reachableInv base onoff hDet ecEk hEk
      ecCt0 hCt0 ecCt1 hCt1 leak kemMat hm e t s hs.1 hs.2 z hz,
      honestCorrectness_preserves_pinnedSources ecEk ecCt0 ecCt1 kemMat e t s hs.2 z hz⟩)

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- For `kemMat ∈ support (sampleMaterial leak)` and any state `s` satisfying `reachableInv s`,
`pinnedSources kemMat e s`, and `e ∉ s.exposed`, `adv` accepts with the same probability against
`simOracle … e kemMat.pk kemMat.ciphertext kStar` from `hideState e s` and against
`honestStopped … kemMat e kStar` from `s`. -/
private theorem optionRun_hide_eq
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (hm : kemMat ∈ support (sampleMaterial leak)) (e : ℕ) (kStar : K)
    (adv : SecurityAdversary leak Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s)
    (hsrc : pinnedSources kemMat e s) (he : e ∉ s.exposed) :
    Pr[= true | optionRun
      (simOracle base onoff ecEk ecCt0 ecCt1 leak e kemMat.pk kemMat.ciphertext kStar)
      adv (hideState e s)] =
    Pr[= true | optionRun (honestStopped base onoff ecEk ecCt0 ecCt1 leak kemMat e kStar)
      adv s] := by
  apply probOutput_optionRun_eq_of_state_map _ _ (hideState e)
    (fun s => (reachableInv base onoff ecEk ecCt0 ecCt1 s ∧ pinnedSources kemMat e s) ∧
      e ∉ s.exposed)
  · intro t s hs z hz hcont
    change z ∈ support (do
      let out ← (honestOracle base onoff ecEk ecCt0 ecCt1 leak kemMat e kStar t).run s
      pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2)) at hz
    obtain ⟨out, hout, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    obtain rfl := (mem_support_pure_iff _ _).mp hz
    have hex : e ∉ out.2.exposed := by
      by_contra h
      simp only [h, decide_true, ↓reduceIte, Option.isSome_none, Bool.false_eq_true] at hcont
    exact ⟨honestScheme_preserves_simulationInv base onoff hDet ecEk hEk ecCt0 hCt0
      ecCt1 hCt1 leak kemMat hm e _ (pinnedChallenge_recordsChallenges onoff e kStar)
      t s hs.1 out hout, hex⟩
  · intro t s hs
    exact simOracle_hide base onoff ecEk ecCt0 ecCt1 leak kemMat e kStar t s hs.1.1 hs.2
  · exact ⟨⟨hs, hsrc⟩, he⟩

omit [DecidableEq K] [DecidableEq Sym] [SampleableType K] in
/-- `hideState e` maps the initial game state to the simulator's initial state. -/
private theorem hideState_initial
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure) (e : ℕ) :
    hideState e (oppUniKemCKA.Reduction.Internal.initialGame (Sym := Sym) base onoff) =
      initial onoff := by
  simp [hideState, hideA, hideB, initial, oppUniKemCKA.Reduction.Internal.initialGame,
    oppUniKemCKA.Reduction.Internal.initialA, oppUniKemCKA.Reduction.Internal.initialB,
    SCKAScheme.initGameState]

/-- For `kemMat ∈ support (sampleMaterial leak)`,
`Pr[run adv e kemMat.pk kemMat.ciphertext kStar = true] =
Pr[optionRun (honestStopped kemMat e kStar) adv s₀ = true]`. -/
theorem run_eq_honestStopped
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (hm : kemMat ∈ support (sampleMaterial leak)) (e : ℕ) (kStar : K)
    (adv : SecurityAdversary leak Sym) :
    Pr[= true | run base onoff ecEk ecCt0 ecCt1 leak adv e kemMat.pk kemMat.ciphertext kStar] =
    Pr[= true | optionRun (honestStopped base onoff ecEk ecCt0 ecCt1 leak kemMat e kStar)
      adv (oppUniKemCKA.Reduction.Internal.initialGame base onoff)] := by
  have hrun : run base onoff ecEk ecCt0 ecCt1 leak adv e kemMat.pk kemMat.ciphertext kStar =
      optionRun (simOracle base onoff ecEk ecCt0 ecCt1 leak e
        kemMat.pk kemMat.ciphertext kStar) adv (initial onoff) := by
    simp [run, optionRun, StateT.run'_eq, bind_pure_comp, Functor.map_map]
  rw [hrun, ← hideState_initial base onoff e]
  exact optionRun_hide_eq base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
    leak kemMat hm e kStar adv _
    (reachableInv_init base onoff ecEk ecCt0 ecCt1 ecEk.ec.nchunk_pos ecCt0.ec.nchunk_pos)
    (pinnedSources_initial base onoff leak kemMat e)
    (by simp [oppUniKemCKA.Reduction.Internal.initialGame, SCKAScheme.initGameState])

/-- `Pr[fixedBranch adv e b = true] =
Pr[kemMat ← sampleMaterial leak; k ←$ K; optionRun (honestStopped kemMat e k_b) adv s₀ = true]` with
`k_b := if b then kemMat.key else k`. -/
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
      let kemMat ← sampleMaterial leak
      let k ← ($ᵗ K : ProbComp K)
      optionRun (honestStopped base onoff ecEk ecCt0 ecCt1 leak kemMat e
        (if b then kemMat.key else k)) adv
        (oppUniKemCKA.Reduction.Internal.initialGame base onoff)] := by
  rw [fixedBranch_eq_material]
  apply probOutput_bind_congr
  intro kemMat hm
  apply probOutput_bind_congr
  intro k _
  exact run_eq_honestStopped base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
    leak kemMat hm e _ adv

end oppUniKemCKA.Security.Embedding
