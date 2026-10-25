/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Endpoints
import SecureMessaging.SCKA.OppUniKEM.Security.IdealHybrids
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Game
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Simulation
import SecureMessaging.SCKA.Security
import ToVCVio.OracleComp.QueryTracking.OneUseSampling

/-!
# The pinned hybrids and their sampling stages

**Setting.** Throughout this module, we consider a KEM material `kemMat` (`Simulator`), a challenge
epoch `e > 0`, a mode bit `b`, an SCKA adversary `adv`, the initial game state `s₀`, and the
instances `stageScheme stage kemMat e s` (`Game`): Opp-UniKEM with the sampling phases of epoch `e`
selected by the stage `stage` *pinned* to `kemMat` and the others *fresh*, where A outputs B's
recorded key instead of decapsulating; `honestScheme kemMat e s` is the fully pinned instance.

**Definitions.** The *pinned hybrid* `stageStopped .pinned kemMat e b` is the ideal hybrid `H_{e-1}`
if `b = false`, or `H_e` if `b = true` (`H_i := idealEpochHybridExp adv i`, `IdealHybrids`), with
the samples of epoch `e` *pinned*: drawn in advance as `kemMat` and read from there by the sampling
phases of epoch `e` instead of drawn at their protocol calls; the run stops at the first exposure
of `e`. Formally, it is the security game over `honestScheme kemMat e` whose challenges follow the
mode `adjacentMode e b` (`IdealHybrids`; `U`: uniform challenge key, `R`: recorded key):

```text
epoch                  1   …   e-1   e   e+1  …
adjacentMode e false   U   …   U     R   R    …      (H_{e-1})
adjacentMode e true    U   …   U     U   R    …      (H_e)
```

More generally, `stageStopped stage kemMat e b` is the same game over `stageScheme stage kemMat e`,
so the stages interpolate between the pinned hybrid and the ideal game:

| game                        | key generation | offline encapsulation | online encapsulation |
| --------------------------- | -------------- | --------------------- | -------------------- |
| `stageStopped .pinned`      | pinned         | pinned                | pinned               |
| `stageStopped .onlineFresh` | pinned         | pinned                | fresh                |
| `stageStopped .encapsFresh` | pinned         | fresh                 | fresh                |
| `stageStopped .fresh`       | fresh          | fresh                 | fresh                |

**Main results.** The games in the following chain, the stopped ones run by `adv` from `s₀`, all
accept with the same probability; `fixedBranch adv e b` is the reduction `𝓑` with challenge epoch
`e` and IND-CPA bit `b` (`Simulator`), and the mode bit is `!b` because the IND-CPA bit `true`
selects the real key while the mode bit `true` selects a uniform key. This module proves the first
and the last link, the deferral modules the middle ones.

```text
fixedBranch adv e b
   ‖ fixedBranch_eq_pinnedHybrid
kemMat ← sampleMaterial leak;  stageStopped .pinned kemMat e (!b)
   ‖ stageStopped_online_deferred                                        (OnlineDeferral)
kemMat ← sampleMaterial leak;  stageStopped .onlineFresh kemMat e (!b)
   ‖ stageStopped_offline_deferred                                       (SourceDeferral)
kemMat ← sampleMaterial leak;  stageStopped .encapsFresh kemMat e (!b)
   ‖ stageStopped_keygen_deferred                                        (SourceDeferral)
stageStopped .fresh kemMat₀ e (!b)                                       kemMat₀ arbitrary (unused)
   ‖ stageOracle_fresh_eq_ideal                                          (an equality of oracles)
idealSecurityImpl (adjacentMode e (!b)), stopped at the first exposure of e
```
-/

open OracleSpec OracleComp KEMScheme
open SCKAScheme.sckaSecuritySpec

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
  (hDet : base.DeterministicDecaps)
variable (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
variable (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
variable (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
variable (leak : base.OnOffRandLeak onoff)

/-- Whether `query` is an eligible challenge at epoch `e` from `s`, that is, a query whose answer
reads the key at `e`. -/
def usesChallengeKey {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (e : ℕ) (query : (SCKAScheme.sckaSecuritySpec Unit Unit Unit Unit Unit).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) : Bool :=
  match query with
  | .inl (.inl (.inr t)) => decide (t = e ∧ e ∉ s.exposed ∧ e ∉ s.challenged ∧
      ((s.keyA e).isSome ∨ (s.keyB e).isSome))
  | _ => false

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Stage oracles: the security oracles over `stageScheme stage kemMat e s` at state `s`, with
challenges `challOf (adjacentMode e b)`; `stageOracle .pinned kemMat e b` is the pinned hybrid
before stopping. -/
def stageOracle (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool) :
    QueryImpl (securitySpec leak Sym)
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp) :=
  securityImplAt base onoff leak (stageScheme ecEk ecCt0 ecCt1 stage kemMat e)
    (SCKAScheme.challOf (adjacentMode e b))

/-- `stageOracle stage kemMat e b`, answering `⊥` at the first query whose successor exposes `e`;
`stageStopped .pinned kemMat e b` is the pinned hybrid. -/
def stageStopped (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool) :
    QueryImpl (securitySpec leak Sym)
      (OptionT (StateT
        (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp)) :=
  stopOnState (stageOracle base onoff ecEk ecCt0 ecCt1 leak stage kemMat e b)
    (fun s => decide (e ∈ s.exposed))

/-- No query of `honestOracle kemMat e kStar` removes an epoch from `challenged`. -/
private theorem honestOracle_preserves_challenged (kemMat : KEMMaterial leak) (e : ℕ) (kStar : K)
    (u : ℕ) :
    QueryImpl.PreservesInv (honestOracle base onoff ecEk ecCt0 ecCt1 leak kemMat e kStar)
      (fun s => u ∈ s.challenged) := by
  intro t s hs z hz
  rw [honestOracle, securityImplAt_run] at hz
  exact SCKAScheme.securityImplOf_challenged_subset _ _ _ _ _
    (fun t s z hz => (SCKAScheme.correctnessImpl_securitySets_eq _ t s z hz).2)
    (pinnedChallenge_recordsChallenges onoff e kStar) t s z hz hs

/-- If `usesChallengeKey e t s = false`, the key does not affect how `honestOracle kemMat e k`
answers `t` from `s`. -/
private theorem honestOracle_eq_of_unused (kemMat : KEMMaterial leak) (e : ℕ) (k k' : K)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (h : usesChallengeKey e t s = false) :
    (honestOracle base onoff ecEk ecCt0 ecCt1 leak kemMat e k t).run s =
      (honestOracle base onoff ecEk ecCt0 ecCt1 leak kemMat e k' t).run s := by
  rcases t with (((((t | a) | a) | t) | a) | a)
  all_goals try rfl
  simp only [securityImplAt, honestOracle, StateT.run_bind, StateT.run_get, pure_bind]
  exact pinnedChallenge_eq_of_unused onoff e t k k' s (of_decide_eq_false h)

/-- If `usesChallengeKey e t s = true`, every possible successor of
`honestOracle kemMat e k` on `t` from `s` has `e ∈ challenged`. -/
private theorem honestOracle_use_records_challenge (kemMat : KEMMaterial leak) (e : ℕ) (k : K)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (h : usesChallengeKey e t s = true)
    (z : (securitySpec leak Sym).Range t ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support ((honestOracle base onoff ecEk ecCt0 ecCt1 leak kemMat e k t).run s)) :
    e ∈ z.2.challenged := by
  rcases t with (((((t | a) | a) | t) | a) | a)
  all_goals try simp only [usesChallengeKey, Bool.false_eq_true, decide_eq_true_eq] at h
  obtain ⟨ht, he, hc, hk⟩ := h
  subst t
  simp only [securityImplAt, honestOracle, StateT.run_bind, StateT.run_get, pure_bind] at hz
  rw [pinnedChallenge_selected onoff e k s (by simp [he, hc]) hk] at hz
  obtain rfl := (mem_support_pure_iff _ _).mp hz
  exact Finset.mem_insert_self _ _

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]
variable (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
  (hDet : base.DeterministicDecaps)
variable (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
variable (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
variable (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
variable (leak : base.OnOffRandLeak onoff)

/-- Under `reachableInv`, if every key B records at `e` is `kemMat.key`, then
`honestOracle kemMat e kemMat.key` and `stageOracle .pinned kemMat e false` answer every query with
the same computation. -/
private theorem honestOracle_eq_hybrid_real
    (kemMat : KEMMaterial leak) (e : ℕ) (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s)
    (hm : ∀ k, s.keyB e = some k → k = kemMat.key) :
    (honestOracle base onoff ecEk ecCt0 ecCt1 leak kemMat e kemMat.key t).run s =
      (stageOracle base onoff ecEk ecCt0 ecCt1 leak .pinned kemMat e false t).run s := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  all_goals try rfl
  simp only [securityImplAt, honestOracle, stageOracle, StateT.run_bind, StateT.run_get,
    pure_bind, SCKAScheme.challOf, adjacentMode_apply, Bool.false_eq_true, false_and, or_false]
  exact pinnedChallenge_eq_recorded onoff e kemMat.key t s
    (recorded_eq_key base onoff ecEk ecCt0 ecCt1 leak kemMat e s hs hm)

include hDet hEk hCt0 hCt1 in
/-- With the key of `kemMat` at `e`, the stopped honest game has the acceptance probability of the
stopped pinned hybrid with mode bit `false`: for `kemMat ∈ support (sampleMaterial leak)`,
`Pr[optionRun (honestStopped kemMat e kemMat.key) adv s₀ = true] =
Pr[optionRun (stageStopped .pinned kemMat e false) adv s₀ = true]`. -/
theorem honestStopped_real_eq_hybrid
    (kemMat : KEMMaterial leak) (hm : kemMat ∈ support (sampleMaterial leak)) (e : ℕ)
    (adv : SecurityAdversary leak Sym) :
    Pr{let x ← (optionRun (honestStopped base onoff ecEk ecCt0 ecCt1 leak kemMat e kemMat.key)
      adv (oppUniKemCKA.Reduction.Internal.initialGame base onoff))}[x = true] =
    Pr{let x ← (optionRun (stageStopped base onoff ecEk ecCt0 ecCt1 leak .pinned kemMat e false)
      adv (oppUniKemCKA.Reduction.Internal.initialGame base onoff))}[x = true] := by
  symm
  apply prEvent_optionRun_eq_of_state_map _ _ id
    (fun s => (reachableInv base onoff ecEk ecCt0 ecCt1 s ∧ consistentMat kemMat e s) ∧
      ∀ k, s.keyB e = some k → k = kemMat.key)
  · intro t s hs z hz _
    change z ∈ support (do
      let out ← (honestOracle base onoff ecEk ecCt0 ecCt1 leak kemMat e kemMat.key t).run s
      pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2)) at hz
    obtain ⟨out, hout, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    obtain rfl := (mem_support_pure_iff _ _).mp hz
    exact ⟨honestScheme_preserves_simulationInv base onoff hDet ecEk hEk ecCt0 hCt0
      ecCt1 hCt1 leak kemMat hm e _ (pinnedChallenge_recordsChallenges onoff e kemMat.key)
      t s hs.1 out hout,
      honestScheme_preserves_keyB_eq base onoff ecEk ecCt0 ecCt1 leak kemMat e _
        (pinnedChallenge_recordsChallenges onoff e kemMat.key) t s hs.2 out hout⟩
  · intro t s hs
    simp only [id_eq, Prod.map_id, id_map]
    change (do
      let out ← (stageOracle base onoff ecEk ecCt0 ecCt1 leak .pinned kemMat e false t).run s
      pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2)) =ᵈ _
    rw [← honestOracle_eq_hybrid_real base onoff ecEk ecCt0 ecCt1 leak kemMat e t s hs.1.1 hs.2]
    rfl
  · exact ⟨⟨reachableInv_init base onoff ecEk ecCt0 ecCt1
      ecEk.ec.nchunk_pos ecCt0.ec.nchunk_pos, consistentMat_initial base onoff leak kemMat e⟩,
      keyB_eq_initial base onoff leak kemMat e⟩

omit [DecidableEq K] [DecidableEq Sym] in
/-- Drawing the key at `e` uniformly turns the pinned challenge into the challenge of mode
`adjacentMode e true`: for `e > 0`, from every state,
`k ←$ K; pinnedChallenge e k t =ᵈ oracleChall (adjacentMode e true t) t`. -/
private theorem pinnedChallenge_sample_uniform
    {base : KEMScheme ProbComp K PK SK C} (onoff : base.OnOffStructure)
    (e : ℕ) (he : 0 < e) (t : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    (do
      let k ← ($ᵗ K : ProbComp K)
      (pinnedChallenge onoff e k t).run s) =ᵈ
    (SCKAScheme.oracleChall (adjacentMode e true t)
      (StA onoff Sym) (StB onoff Sym) K (Message Sym) t).run s := by
  by_cases hg : t ∈ s.exposed ∨ t ∈ s.challenged
  · simp [OracleComp.EvalDistEq.map_const, pinnedChallenge, challengeWith,
      SCKAScheme.oracleChall, hg]
  · by_cases ht : t = e
    · subst t
      cases hA : s.keyA e <;> cases hB : s.keyB e <;>
        simp [OracleComp.EvalDistEq.map_const, pinnedChallenge, challengeWith,
          SCKAScheme.oracleChall, adjacentMode_apply, hg, hA, hB, he]
    · cases hA : s.keyA t <;> cases hB : s.keyB t <;> by_cases hr : 0 < t ∧ t < e <;>
        simp [OracleComp.EvalDistEq.bind_const, OracleComp.EvalDistEq.map_const, pinnedChallenge,
          challengeWith, SCKAScheme.oracleChall, adjacentMode_apply, hg, hA, hB, ht, hr]

/-- The query-level version of `honestStopped_random_eq_hybrid`: for `e > 0`, from every state,
`k ←$ K; honestOracle kemMat e k t =ᵈ stageOracle .pinned kemMat e true t`. -/
private theorem honestOracle_sample_uniform
    (kemMat : KEMMaterial leak) (e : ℕ) (he : 0 < e) (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    (do
      let k ← ($ᵗ K : ProbComp K)
      (honestOracle base onoff ecEk ecCt0 ecCt1 leak kemMat e k t).run s) =ᵈ
    (stageOracle base onoff ecEk ecCt0 ecCt1 leak .pinned kemMat e true t).run s := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  all_goals
    first
    | simpa only [securityImplAt, honestOracle, stageOracle, StateT.run_bind, StateT.run_get,
        pure_bind, SCKAScheme.challOf] using pinnedChallenge_sample_uniform onoff e he t s
    | simp only [securityImplAt, honestOracle, stageOracle, StateT.run_bind, StateT.run_get,
        pure_bind]
      exact OracleComp.EvalDistEq.bind_const _ _

/-- With a uniform key at `e`, the stopped honest game has the acceptance probability of the stopped
pinned hybrid with mode bit `true`: for `e > 0` and every state `s`,
`Pr[k ←$ K; optionRun (honestStopped kemMat e k) adv s = true] =
Pr[optionRun (stageStopped .pinned kemMat e true) adv s = true]`. -/
theorem honestStopped_random_eq_hybrid
    (kemMat : KEMMaterial leak) (e : ℕ) (he : 0 < e)
    (adv : SecurityAdversary leak Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    Pr{let x ← (do
      let k ← ($ᵗ K : ProbComp K)
      optionRun (honestStopped base onoff ecEk ecCt0 ecCt1 leak kemMat e k) adv s)}[x = true] =
    Pr{let x ← (optionRun
        (stageStopped base onoff ecEk ecCt0 ecCt1 leak .pinned kemMat e true) adv s)}[x = true] :=
  stoppedRun_sample_once_eq ($ᵗ K) (honestOracle base onoff ecEk ecCt0 ecCt1 leak kemMat e)
    (stageOracle base onoff ecEk ecCt0 ecCt1 leak .pinned kemMat e true) (fun s => decide (e ∈
      s.exposed))
    (fun _ => True) (fun s => e ∈ s.challenged) (usesChallengeKey e)
    (fun _ _ _ _ _ _ _ _ => trivial)
    (fun k _ t s _ hs z hz _ => honestOracle_preserves_challenged base onoff ecEk ecCt0 ecCt1
      leak kemMat e k e t s hs z hz)
    (fun t s _ h k _ k' _ => ToVCVio.evalDistEq_of_eq
      (honestOracle_eq_of_unused base onoff ecEk ecCt0 ecCt1 leak kemMat e k k' t s h))
    (fun t s _ hs => by
      rcases t with (((((t | a) | a) | t) | a) | a) <;> simp [usesChallengeKey, hs])
    (fun k _ t s _ h z hz _ => honestOracle_use_records_challenge base onoff ecEk ecCt0 ecCt1
      leak kemMat e k t s h z hz)
    (fun t s _ => honestOracle_sample_uniform base onoff ecEk ecCt0 ecCt1 leak kemMat e he t s)
    adv s trivial

include hDet hEk hCt0 hCt1 in
/-- For `e > 0`, `Pr[fixedBranch adv e b = true] =
Pr[kemMat ← sampleMaterial leak; optionRun (stageStopped .pinned kemMat e (!b)) adv s₀ = true]`;
the negation maps the IND-CPA bit (`true`: real key) to the mode bit (`true`: uniform key). -/
theorem fixedBranch_eq_pinnedHybrid
    (adv : SecurityAdversary leak Sym) (e : ℕ) (he : 0 < e) (b : Bool) :
    Pr{let x ← fixedBranch base onoff ecEk ecCt0 ecCt1 leak adv e b}[x = true] =
    Pr{let x ← (do
      let kemMat ← sampleMaterial leak
      optionRun (stageStopped base onoff ecEk ecCt0 ecCt1 leak .pinned kemMat e (!b))
        adv (oppUniKemCKA.Reduction.Internal.initialGame base onoff))}[x = true] := by
  rw [fixedBranch_eq_honestStopped base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1]
  simp only [map_bind]
  refine OracleComp.prEvent_bind_congr_of_support _ _ _ fun kemMat hm => ?_
  cases b
  · simpa only [map_bind, Bool.false_eq_true, ↓reduceIte, Bool.not_false] using
      honestStopped_random_eq_hybrid base onoff ecEk ecCt0 ecCt1 leak kemMat e he adv _
  · simp only [Bool.not_true, ↓reduceIte, OracleComp.prEvent_bind_const]
    exact honestStopped_real_eq_hybrid base onoff hDet ecEk hEk ecCt0 hCt0
      ecCt1 hCt1 leak kemMat hm e adv

end oppUniKemCKA.Security.Embedding

/-! ## The fresh stage -/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
  (hDet : base.DeterministicDecaps)
variable (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
variable (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
variable (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
variable (leak : base.OnOffRandLeak onoff)

/-- B's leaking send in `stageScheme .fresh kemMat e s` is that of Opp-UniKEM over `base`. -/
theorem sendBrleak_fresh_eq [DecidableEq Sym]
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (stB : StB onoff Sym) :
    (stageScheme ecEk ecCt0 ecCt1 .fresh kemMat e s).sendBrleak stB =
    (scheme base onoff hDet ecEk ecCt0 ecCt1 leak).sendBrleak stB := by
  dsimp only [stageScheme, Stage.keygenFlag, Stage.offlineFlag, Stage.onlineFlag]
  simp only [scheme]
  cases hct0 : stB.ct0 <;> cases hek : stB.ekA <;> cases hct1 : stB.ct1 <;>
    cases hst : stB.stCt <;> cases hack : stB.ack.ctRec
  all_goals
    simp only [sendBrleak, hct0, hek, hct1]
    try dsimp only [Pinned.leakage]
    simp [hct0, hek, hct1, hst, hack, monad_norm]

/-- Ordinary-send version of `sendBrleak_fresh_eq`. -/
theorem sendB_fresh_eq [DecidableEq Sym]
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (stB : StB onoff Sym) :
    (stageScheme ecEk ecCt0 ecCt1 .fresh kemMat e s).sendB stB =
    (scheme base onoff hDet ecEk ecCt0 ecCt1 leak).sendB stB := by
  rw [scheme_sendB_eq_map_sendBrleak, scheme_sendB_eq_map_sendBrleak,
    sendBrleak_fresh_eq base onoff hDet ecEk ecCt0 ecCt1 leak kemMat e s stB]

/-- The fully fresh stage is the ideal game of mode `adjacentMode e b`:
`stageOracle .fresh kemMat e b = idealSecurityImpl (adjacentMode e b)`. -/
theorem stageOracle_fresh_eq_ideal [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool) :
    stageOracle base onoff ecEk ecCt0 ecCt1 leak .fresh kemMat e b =
      idealSecurityImpl base onoff hDet ecEk ecCt0 ecCt1 leak (adjacentMode e b) := by
  funext t
  apply StateT.ext
  intro s
  simp only [securityImplAt, stageOracle, StateT.run_bind, StateT.run_get, pure_bind]
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n)
    · simp only [idealSecurityImpl, SCKAScheme.securityImplOf, idealCorrectnessImpl,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl]
    · simp only [idealSecurityImpl, SCKAScheme.securityImplOf, idealCorrectnessImpl,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        SCKAScheme.oracleSendA, stageScheme, Stage.keygenFlag, Stage.offlineFlag,
        Stage.onlineFlag, scheme, sendA, Pinned.kem, Pinned.onOff, Pinned.keygen,
        Bool.false_eq_true, ite_false]
    · simp only [idealSecurityImpl, SCKAScheme.securityImplOf, idealCorrectnessImpl,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get, pure_bind]
      rw [sendB_fresh_eq base onoff hDet ecEk ecCt0 ecCt1 leak kemMat e s _]
    · simp only [idealSecurityImpl, SCKAScheme.securityImplOf, idealCorrectnessImpl,
        SCKAScheme.sckaCorrectnessImpl,
        QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        SCKAScheme.oracleRecvA, StateT.run_bind, StateT.run_get, pure_bind]
      cases hm : s.msgB n with
      | none =>
        simp only [oracleRecvAIdeal, schemeWithDecaps, SCKAScheme.oracleRecvA,
          StateT.run_bind, StateT.run_get, pure_bind, hm]
      | some entry =>
        rcases entry with ⟨msg, tsnd⟩
        simp only []
        rw [stageScheme_recvA_eq_ideal]
        simp only [oracleRecvAIdeal, schemeWithDecaps, SCKAScheme.oracleRecvA,
          StateT.run_bind, StateT.run_get, pure_bind, hm]
    · simp only [idealSecurityImpl, SCKAScheme.securityImplOf, idealCorrectnessImpl,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        SCKAScheme.oracleRecvB, stageScheme, scheme, recvB]
  · simp only [idealSecurityImpl, SCKAScheme.securityImplOf,
      QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      SCKAScheme.oracleSendArleak, stageScheme, Stage.keygenFlag, Stage.offlineFlag,
      Stage.onlineFlag, scheme, sendArleak, Pinned.kem, Pinned.onOff, Pinned.leakage,
      Bool.false_eq_true, ite_false]
  · simp only [idealSecurityImpl, SCKAScheme.securityImplOf,
      QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      SCKAScheme.oracleSendBrleak, StateT.run_bind, StateT.run_get, pure_bind]
    rw [sendBrleak_fresh_eq base onoff hDet ecEk ecCt0 ecCt1 leak kemMat e s _]
  · rfl
  · rfl
  · rfl

end oppUniKemCKA.Security.Embedding
