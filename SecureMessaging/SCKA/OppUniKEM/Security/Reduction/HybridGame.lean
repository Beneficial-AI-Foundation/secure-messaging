/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Endpoints
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Game
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Simulation
import SecureMessaging.SCKA.Security
import ToVCVio.OracleComp.QueryTracking.OneUseSampling

/-!
# The pinned hybrids and their sampling stages

Fix complete material `m`, an epoch `e > 0`, a mode bit `b`, an adversary `adv`, and the initial
game state `s₀`. `securityImplAt`, `honestScheme`, `honestOracle`, and `honestStopped` are
defined in `Game`; `challOf μ` (`SCKA.Security`) randomizes the eligible challenges at `t` with
`μ t = true`.

**Definitions.**

- `adjacentMode e b t := decide (0 < t ∧ (t < e ∨ (b ∧ t = e)))`: randomize `1, …, e - 1`, and
  `e` if `b`.
- `hybridOracle m e b := securityImplAt (honestScheme m e) (challOf (adjacentMode e b))`, the
  *pinned hybrid*; `hybridStopped m e b` answers `⊥` at the first query exposing `e`.
- `oracle stage m e b`: as `hybridOracle`, with instance `schemeAt stage m e`, which pins only
  the phases of `stage`; `stopped stage m e b` answers `⊥` at the first query exposing `e`.

| `Stage` | key generation | offline encapsulation | online encapsulation |
| --- | --- | --- | --- |
| `onlineFresh` | pinned | pinned | fresh |
| `encapsFresh` | pinned | fresh | fresh |
| `fresh` | fresh | fresh | fresh |

A *pinned* phase returns its output in `m`; a *fresh* one samples at its call. `OnlineDeferral`
and `SourceDeferral` pass from the pinned hybrid to these stages in order.

**Results.** With `P(O, s) := Pr[optionRun O adv s = true]`:

- `honestStopped_real_eq_hybrid`: for `m ∈ support (sampleMaterial leak)`,
  `P(honestStopped m e m.on.1.2, s₀) = P(hybridStopped m e false, s₀)`;
- `honestStopped_random_eq_hybrid`: for every `s`,
  `Pr[k ←$ K; optionRun (honestStopped m e k) adv s = true] = P(hybridStopped m e true, s)`;
- `fixedBranch_eq_pinnedHybrid`: `Pr[fixedBranch adv e b = true] =
  Pr[m ← sampleMaterial leak; optionRun (hybridStopped m e (!b)) adv s₀ = true]`;
- `oracle_fresh_eq_ideal`: `oracle .fresh m e b = idealSecurityImpl (adjacentMode e b)`.
-/

open OracleSpec OracleComp KEMScheme
open SCKAScheme.sckaSecuritySpec

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- Whether `query` is an eligible challenge of `e` from `s`. -/
def usesChallengeKey {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (e : ℕ) (query : (SCKAScheme.sckaSecuritySpec Unit Unit Unit Unit Unit).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) : Bool :=
  match query with
  | .inl (.inl (.inr t)) => decide (t = e ∧ e ∉ s.exposed ∧ e ∉ s.challenged ∧
      ((s.keyA e).isSome ∨ (s.keyB e).isSome))
  | _ => false

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]
variable (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
variable (ecEk : ErasureCodePayload PK Sym)
variable (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
variable (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)

/-- No query of `honestOracle m e kStar` removes an epoch from `challenged`. -/
private theorem honestOracle_preserves_challenged (m : Material leak) (e : ℕ) (kStar : K) (u : ℕ) :
    QueryImpl.PreservesInv (honestOracle base onoff ecEk ecCt0 ecCt1 leak m e kStar)
      (fun s => u ∈ s.challenged) := by
  intro t s hs z hz
  rw [honestOracle, securityImplAt_run] at hz
  exact SCKAScheme.securityImplOf_challenged_subset _ _ _ _ _
    (fun t s z hz => (SCKAScheme.correctnessImpl_securitySets_eq _ t s z hz).2)
    (pinnedChallenge_recordsChallenges onoff e kStar) t s z hz hs

/-- If `usesChallengeKey e t s = false`, the key does not affect how `honestOracle m e k`
answers `t` from `s`. -/
private theorem honestOracle_eq_of_unused (m : Material leak) (e : ℕ) (k k' : K)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (h : usesChallengeKey e t s = false) :
    (honestOracle base onoff ecEk ecCt0 ecCt1 leak m e k t).run s =
      (honestOracle base onoff ecEk ecCt0 ecCt1 leak m e k' t).run s := by
  rcases t with (((((t | a) | a) | t) | a) | a)
  all_goals try rfl
  simp only [securityImplAt, honestOracle, StateT.run_bind, StateT.run_get, pure_bind]
  exact pinnedChallenge_eq_of_unused onoff e t k k' s (of_decide_eq_false h)

/-- If `usesChallengeKey e t s = true`, every possible successor of
`honestOracle m e k` on `t` from `s` has `e ∈ challenged`. -/
private theorem honestOracle_use_records_challenge (m : Material leak) (e : ℕ) (k : K)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (h : usesChallengeKey e t s = true)
    (z : (securitySpec leak Sym).Range t ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support ((honestOracle base onoff ecEk ecCt0 ecCt1 leak m e k t).run s)) :
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

/-- Challenge mode at epoch `e`: randomize `t` iff `0 < t < e`, or `t = e` and `b = true`. -/
def adjacentMode (e : ℕ) (b : Bool) (t : ℕ) : Bool :=
  decide (0 < t ∧ (t < e ∨ (b = true ∧ t = e)))

/-- Pinned hybrid: the security oracles over `honestScheme m e s` with challenges
`challOf (adjacentMode e b)`. -/
def hybridOracle
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (b : Bool) :
    QueryImpl (securitySpec leak Sym)
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp) :=
  securityImplAt base onoff leak (honestScheme ecEk ecCt0 ecCt1 m e)
    (SCKAScheme.challOf (adjacentMode e b))

/-- `hybridOracle m e b`, answering `⊥` at the first query whose successor exposes `e`. -/
def hybridStopped
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (b : Bool) :
    QueryImpl (securitySpec leak Sym)
      (OptionT (StateT
        (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp)) :=
  stopOnState (hybridOracle base onoff ecEk ecCt0 ecCt1 leak m e b)
    (fun s => decide (e ∈ s.exposed))

/-- Under `reachableInv` and `pinnedKey m e`, `honestOracle m e m.on.1.2` and
`hybridOracle m e false` answer every query with the same computation. -/
private theorem honestOracle_eq_hybrid_real
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hm : pinnedKey m e s) :
    (honestOracle base onoff ecEk ecCt0 ecCt1 leak m e m.on.1.2 t).run s =
      (hybridOracle base onoff ecEk ecCt0 ecCt1 leak m e false t).run s := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  all_goals try rfl
  simp only [securityImplAt, honestOracle, hybridOracle, StateT.run_bind, StateT.run_get,
    pure_bind, SCKAScheme.challOf, adjacentMode, Bool.false_eq_true, false_and, or_false]
  exact pinnedChallenge_eq_recorded onoff e m.on.1.2 t s
    (pinnedKey_both base onoff ecEk ecCt0 ecCt1 leak m e s hs hm)

/-- For `m ∈ support (sampleMaterial leak)`,
`Pr[optionRun (honestStopped m e m.on.1.2) adv s₀ = true] =
Pr[optionRun (hybridStopped m e false) adv s₀ = true]`. -/
theorem honestStopped_real_eq_hybrid
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (hm : m ∈ support (sampleMaterial leak)) (e : ℕ)
    (adv : SecurityAdversary leak Sym) :
    Pr[= true | optionRun (honestStopped base onoff ecEk ecCt0 ecCt1 leak m e m.on.1.2)
      adv (oppUniKemCKA.Reduction.Internal.initialGame base onoff)] =
    Pr[= true | optionRun (hybridStopped base onoff ecEk ecCt0 ecCt1 leak m e false)
      adv (oppUniKemCKA.Reduction.Internal.initialGame base onoff)] := by
  symm
  apply probOutput_optionRun_eq_of_state_map _ _ id
    (fun s => (reachableInv base onoff ecEk ecCt0 ecCt1 s ∧ pinnedSources m e s) ∧
      pinnedKey m e s)
  · intro t s hs z hz _
    change z ∈ support (do
      let out ← (honestOracle base onoff ecEk ecCt0 ecCt1 leak m e m.on.1.2 t).run s
      pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2)) at hz
    obtain ⟨out, hout, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    obtain rfl := (mem_support_pure_iff _ _).mp hz
    exact ⟨honestScheme_preserves_simulationInv base onoff hDet ecEk hEk ecCt0 hCt0
      ecCt1 hCt1 leak m hm e _ (pinnedChallenge_recordsChallenges onoff e m.on.1.2)
      t s hs.1 out hout,
      honestScheme_preserves_pinnedKey base onoff ecEk ecCt0 ecCt1 leak m e _
        (pinnedChallenge_recordsChallenges onoff e m.on.1.2) t s hs.2 out hout⟩
  · intro t s hs
    simp only [id_eq, Prod.map_id, id_map]
    change 𝒟[(do
      let out ← (hybridOracle base onoff ecEk ecCt0 ecCt1 leak m e false t).run s
      pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2))] = _
    rw [← honestOracle_eq_hybrid_real base onoff ecEk ecCt0 ecCt1 leak m e t s hs.1.1 hs.2]
    rfl
  · exact ⟨⟨reachableInv_init base onoff ecEk ecCt0 ecCt1
      ecEk.ec.nchunk_pos ecCt0.ec.nchunk_pos, pinnedSources_initial base onoff leak m e⟩,
      pinnedKey_initial base onoff leak m e⟩

omit [DecidableEq K] [DecidableEq Sym] in
/-- For `e > 0`, from every state,
`𝒟[k ←$ K; pinnedChallenge e k t] = 𝒟[oracleChall (adjacentMode e true t) t]`. -/
private theorem pinnedChallenge_sample_uniform
    {base : KEMScheme ProbComp K PK SK C} (onoff : base.OnOffStructure)
    (e : ℕ) (he : 0 < e) (t : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    𝒟[(do
      let k ← ($ᵗ K : ProbComp K)
      (pinnedChallenge onoff e k t).run s)] =
    𝒟[(SCKAScheme.oracleChall (adjacentMode e true t)
      (StA onoff Sym) (StB onoff Sym) K (Message Sym) t).run s] := by
  apply evalDist_ext
  intro out
  by_cases hg : t ∈ s.exposed ∨ t ∈ s.challenged
  · simp [pinnedChallenge, challengeWith, SCKAScheme.oracleChall, hg]
  · by_cases ht : t = e
    · subst t
      cases hA : s.keyA e <;> cases hB : s.keyB e <;>
        simp [pinnedChallenge, challengeWith, SCKAScheme.oracleChall, adjacentMode, hg, hA, hB, he]
    · cases hA : s.keyA t <;> cases hB : s.keyB t <;> by_cases hr : 0 < t ∧ t < e <;>
        simp [probOutput_bind_const, pinnedChallenge, challengeWith, SCKAScheme.oracleChall,
          adjacentMode, hg, hA, hB, ht, hr]

/-- For `e > 0`, from every state,
`𝒟[k ←$ K; honestOracle m e k t] = 𝒟[hybridOracle m e true t]`. -/
private theorem honestOracle_sample_uniform
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (he : 0 < e) (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    𝒟[(do
      let k ← ($ᵗ K : ProbComp K)
      (honestOracle base onoff ecEk ecCt0 ecCt1 leak m e k t).run s)] =
    𝒟[(hybridOracle base onoff ecEk ecCt0 ecCt1 leak m e true t).run s] := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  all_goals
    first
    | simpa only [securityImplAt, honestOracle, hybridOracle, StateT.run_bind, StateT.run_get,
        pure_bind, SCKAScheme.challOf] using pinnedChallenge_sample_uniform onoff e he t s
    | apply evalDist_ext
      intro z
      simp only [securityImplAt, honestOracle, hybridOracle, StateT.run_bind, StateT.run_get,
        pure_bind, probOutput_bind_const, probFailure_eq_zero, tsub_zero, one_mul]

/-- For `e > 0` and every state `s`,
`Pr[k ←$ K; optionRun (honestStopped m e k) adv s = true] =
Pr[optionRun (hybridStopped m e true) adv s = true]`. -/
theorem honestStopped_random_eq_hybrid
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (he : 0 < e)
    (adv : SecurityAdversary leak Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    Pr[= true | do
      let k ← ($ᵗ K : ProbComp K)
      optionRun (honestStopped base onoff ecEk ecCt0 ecCt1 leak m e k) adv s] =
    Pr[= true | optionRun (hybridStopped base onoff ecEk ecCt0 ecCt1 leak m e true) adv s] :=
  stoppedRun_sample_once_eq ($ᵗ K) (honestOracle base onoff ecEk ecCt0 ecCt1 leak m e)
    (hybridOracle base onoff ecEk ecCt0 ecCt1 leak m e true) (fun s => decide (e ∈ s.exposed))
    (fun _ => True) (fun s => e ∈ s.challenged) (usesChallengeKey e)
    (fun _ _ _ _ _ _ _ _ => trivial)
    (fun k _ t s _ hs z hz _ => honestOracle_preserves_challenged base onoff ecEk ecCt0 ecCt1
      leak m e k e t s hs z hz)
    (fun t s _ h k _ k' _ => congrArg evalDist
      (honestOracle_eq_of_unused base onoff ecEk ecCt0 ecCt1 leak m e k k' t s h))
    (fun t s _ hs => by
      rcases t with (((((t | a) | a) | t) | a) | a) <;> simp [usesChallengeKey, hs])
    (fun k _ t s _ h z hz _ => honestOracle_use_records_challenge base onoff ecEk ecCt0 ecCt1
      leak m e k t s h z hz)
    (fun t s _ => honestOracle_sample_uniform base onoff ecEk ecCt0 ecCt1 leak m e he t s)
    adv s trivial

/-- For `e > 0`, `Pr[fixedBranch adv e b = true] =
Pr[m ← sampleMaterial leak; optionRun (hybridStopped m e (!b)) adv s₀ = true]`; the negation maps
the IND-CPA bit (`true`: real key) to the mode bit (`true`: uniform key). -/
theorem fixedBranch_eq_pinnedHybrid
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff)
    (adv : SecurityAdversary leak Sym) (e : ℕ) (he : 0 < e) (b : Bool) :
    Pr[= true | fixedBranch base onoff ecEk ecCt0 ecCt1 leak adv e b] =
    Pr[= true | do
      let m ← sampleMaterial leak
      optionRun (hybridStopped base onoff ecEk ecCt0 ecCt1 leak m e (!b))
        adv (oppUniKemCKA.Reduction.Internal.initialGame base onoff)] := by
  rw [fixedBranch_eq_honestStopped base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1]
  apply probOutput_bind_congr
  intro m hm
  cases b
  · exact honestStopped_random_eq_hybrid base onoff ecEk ecCt0 ecCt1 leak m e he adv _
  · simp only [Bool.not_true, ↓reduceIte, probOutput_bind_const,
      probFailure_eq_zero, tsub_zero, one_mul]
    exact honestStopped_real_eq_hybrid base onoff hDet ecEk hEk ecCt0 hCt0
      ecCt1 hCt1 leak m hm e adv

end oppUniKemCKA.Security.Embedding

/-! ## Sampling stages -/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding.Sampling

variable {K PK SK C Sym : Type}

/-- Which sampling phases of the selected epoch are *pinned* to stored outputs. -/
inductive Stage where
  /-- Online encapsulation is fresh; key generation and offline encapsulation are pinned. -/
  | onlineFresh
  /-- Both encapsulation phases are fresh; key generation is pinned. -/
  | encapsFresh
  /-- All three phases are fresh. -/
  | fresh
  deriving DecidableEq

/-- Whether stage `stage` pins key generation at the selected epoch. -/
def Stage.pinsKeygen (stage : Stage) : Bool := decide (stage ≠ .fresh)

/-- Whether stage `stage` pins offline encapsulation at the selected epoch. -/
def Stage.pinsOffline (stage : Stage) : Bool := decide (stage = .onlineFresh)

/-- KEM of `schemeAt stage m e s`: `Pinned.kem m` pinning the phases of `stage` at epoch `e`,
decapsulating to `s.keyB s.stA.t`. -/
abbrev stageKem {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (stage : Stage) (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    KEMScheme ProbComp K PK SK C :=
  Pinned.kem m (stage.pinsKeygen && decide (s.stA.t = e))
    (stage.pinsOffline && decide (s.stB.t = e)) false (s.keyB s.stA.t)

/-- On/off structure of `stageKem stage m e s`. -/
abbrev stageOnOff {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (stage : Stage) (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    (stageKem stage m e s).OnOffStructure :=
  Pinned.onOff m (stage.pinsKeygen && decide (s.stA.t = e))
    (stage.pinsOffline && decide (s.stB.t = e)) false (s.keyB s.stA.t)

/-- Leakage witnesses of `stageKem stage m e s`. -/
abbrev stageLeak {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (stage : Stage) (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    (stageKem stage m e s).OnOffRandLeak (stageOnOff stage m e s) :=
  Pinned.leakage leak m (stage.pinsKeygen && decide (s.stA.t = e))
    (stage.pinsOffline && decide (s.stB.t = e)) false (s.keyB s.stA.t)

/-- Opp-UniKEM over `stageKem stage m e s`, for a query from state `s`. -/
abbrev schemeAt [DecidableEq Sym]
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff}
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (stage : Stage) (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :=
  let sa := stage.pinsKeygen && decide (s.stA.t = e)
  let soff := stage.pinsOffline && decide (s.stB.t = e)
  let key := s.keyB s.stA.t
  scheme (Pinned.kem m sa soff false key) (Pinned.onOff m sa soff false key)
    (Pinned.deterministic m sa soff false key) ecEk ecCt0 ecCt1
    (Pinned.leakage leak m sa soff false key)

/-- Stage oracles: `schemeAt stage m e s` at state `s`, challenges `challOf (adjacentMode e b)`. -/
def oracle [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (stage : Stage) (m : Material leak) (e : ℕ) (b : Bool) :
    QueryImpl (securitySpec leak Sym)
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp) :=
  securityImplAt base onoff leak (schemeAt ecEk ecCt0 ecCt1 stage m e)
    (SCKAScheme.challOf (adjacentMode e b))

/-- `oracle stage m e b`, answering `none` at the first query whose successor exposes `e`. -/
def stopped [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (stage : Stage) (m : Material leak) (e : ℕ) (b : Bool) :
    QueryImpl (securitySpec leak Sym)
      (OptionT (StateT
        (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp)) :=
  stopOnState (oracle base onoff ecEk ecCt0 ecCt1 leak stage m e b)
    (fun s => decide (e ∈ s.exposed))

/-- A's receive in `schemeAt stage m e s` is `recvA` with decapsulation
`fun _ _ => s.keyB s.stA.t`. -/
theorem recvA_eq_ideal [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (stage : Stage) (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (msg : Message Sym) :
    (schemeAt ecEk ecCt0 ecCt1 stage m e s).recvA s.stA msg =
      recvA base onoff (fun _ _ => s.keyB s.stA.t) ecCt0 ecCt1 s.stA msg := by
  rcases msg with ⟨ch, ack, epoch, bit⟩
  cases bit
  all_goals try (rename_i bit; fin_cases bit)
  all_goals cases ch
  all_goals cases hd : s.stA.dkA <;> cases hc : s.stA.ct0 <;> cases hk : s.keyB s.stA.t
  all_goals
    simp only [schemeAt, scheme, recvA, hd, hc, hk,
      Option.bind_eq_bind, Option.pure_def]
    repeat' (split <;> simp_all only [Fin.zero_eta, Fin.mk_one, Fin.isValue,
      Bool.and_eq_true, beq_iff_eq, Option.bind_some, Option.bind_none])

/-- The stage `fresh` pins no key generation. -/
theorem Stage.pinsKeygen_fresh_and (t e : ℕ) :
    (Stage.pinsKeygen .fresh && decide (t = e)) = false := by
  simp [Stage.pinsKeygen]

/-- The stage `fresh` pins no offline encapsulation. -/
theorem Stage.pinsOffline_fresh_and (t e : ℕ) :
    (Stage.pinsOffline .fresh && decide (t = e)) = false := by
  simp [Stage.pinsOffline]

/-- B's leaking send in `schemeAt .fresh m e s` is that of Opp-UniKEM over `base`. -/
theorem sendBrleak_fresh_eq [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (hDet : base.DeterministicDecaps)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (stB : StB onoff Sym) :
    (schemeAt ecEk ecCt0 ecCt1 .fresh m e s).sendBrleak stB =
    (scheme base onoff hDet ecEk ecCt0 ecCt1 leak).sendBrleak stB := by
  dsimp only [schemeAt]
  rw [Stage.pinsKeygen_fresh_and, Stage.pinsOffline_fresh_and]
  simp only [scheme]
  cases hct0 : stB.ct0 <;> cases hek : stB.ekA <;> cases hct1 : stB.ct1 <;>
    cases hst : stB.stCt <;> cases hack : stB.ack.ctRec
  all_goals
    simp only [sendBrleak, hct0, hek, hct1]
    try dsimp only [Pinned.leakage]
    simp [hct0, hek, hct1, hst, hack, monad_norm]

/-- Ordinary-send version of `sendBrleak_fresh_eq`. -/
theorem sendB_fresh_eq [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (hDet : base.DeterministicDecaps)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (stB : StB onoff Sym) :
    (schemeAt ecEk ecCt0 ecCt1 .fresh m e s).sendB stB =
    (scheme base onoff hDet ecEk ecCt0 ecCt1 leak).sendB stB := by
  rw [scheme_sendB_eq_map_sendBrleak, scheme_sendB_eq_map_sendBrleak,
    sendBrleak_fresh_eq base onoff ecEk ecCt0 ecCt1 leak hDet m e s stB]

/-- `oracle .fresh m e b = idealSecurityImpl (adjacentMode e b)`. -/
theorem oracle_fresh_eq_ideal [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (b : Bool) :
    oracle base onoff ecEk ecCt0 ecCt1 leak .fresh m e b =
      idealSecurityImpl base onoff hDet ecEk ecCt0 ecCt1 leak (adjacentMode e b) := by
  have hkg : Stage.pinsKeygen .fresh = false := rfl
  funext t
  apply StateT.ext
  intro s
  simp only [securityImplAt, oracle, StateT.run_bind, StateT.run_get, pure_bind]
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n)
    · simp only [idealSecurityImpl, SCKAScheme.securityImplOf, idealCorrectnessImpl,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl]
    · simp only [idealSecurityImpl, SCKAScheme.securityImplOf, idealCorrectnessImpl,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        SCKAScheme.oracleSendA, schemeAt, scheme, sendA, Pinned.kem, Pinned.onOff,
        Pinned.keygen,
        hkg, Bool.false_and, Bool.false_eq_true, if_false]
    · simp only [idealSecurityImpl, SCKAScheme.securityImplOf, idealCorrectnessImpl,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get, pure_bind]
      rw [sendB_fresh_eq base onoff ecEk ecCt0 ecCt1 leak hDet m e s _]
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
        rw [recvA_eq_ideal]
        simp only [oracleRecvAIdeal, schemeWithDecaps, SCKAScheme.oracleRecvA,
          StateT.run_bind, StateT.run_get, pure_bind, hm]
    · simp only [idealSecurityImpl, SCKAScheme.securityImplOf, idealCorrectnessImpl,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        SCKAScheme.oracleRecvB, schemeAt, scheme, recvB]
  · simp only [idealSecurityImpl, SCKAScheme.securityImplOf,
      QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      SCKAScheme.oracleSendArleak, schemeAt, scheme, sendArleak,
      Pinned.kem, Pinned.onOff, Pinned.leakage,
      hkg, Bool.false_and, Bool.false_eq_true, if_false]
  · simp only [idealSecurityImpl, SCKAScheme.securityImplOf,
      QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      SCKAScheme.oracleSendBrleak, StateT.run_bind, StateT.run_get, pure_bind]
    rw [sendBrleak_fresh_eq base onoff ecEk ecCt0 ecCt1 leak hDet m e s _]
  · rfl
  · rfl
  · rfl

end oppUniKemCKA.Security.Embedding.Sampling
