/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Game
import SecureMessaging.SCKA.Security
import ToVCVio.OracleComp.QueryTracking.OneUseSampling
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Simulation

/-!
# From the honest game to the pinned hybrids

**Setting.** Let `m` be material, `e > 0` a selected epoch, `adv` a security adversary, and
`s₀` the initial game state. `honestStopped_real_eq_hybrid` and `fixedBranch_eq_pinnedHybrid`
assume deterministic decapsulation and correct erasure codes.

**Definitions.**

- `adjacentMode e b t := decide (0 < t ∧ (t < e ∨ (b ∧ t = e)))`: the challenge mode randomizing
  the positive epochs below `e`, and `e` itself if `b = true`.
- `hybridOracle m e b := securityImplAt (honestScheme m e) (challOf (adjacentMode e b))`: the
  pinned hybrid; `hybridStopped m e b` answers `⊥` at the first query whose successor state has
  `e` exposed.
- `usesChallengeKey e t s`: query `t` challenges `e` from a state `s` in which `e` is neither
  exposed nor challenged and A or B has a key recorded at `e`.

**Results.**

- `honestStopped_real_eq_hybrid`: for `m ∈ support (sampleMaterial leak)`,
  `optionRun (honestStopped m e m.on.1.2) adv s₀` and `optionRun (hybridStopped m e false) adv s₀`
  return `true` with equal probability.
- `honestStopped_random_eq_hybrid`: for every state `s`, drawing `k ←$ K` once and running
  `optionRun (honestStopped m e k) adv s` returns `true` with the probability of
  `optionRun (hybridStopped m e true) adv s`.
- `fixedBranch_eq_pinnedHybrid`: `fixedBranch adv e b` returns `true` with the probability that
  `m ← sampleMaterial leak` followed by `optionRun (hybridStopped m e (!b)) adv s₀` does.
-/

open OracleSpec OracleComp KEMScheme
open SCKAScheme.sckaSecuritySpec

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- Whether `query` from state `s` reads the challenge key of `pinnedChallenge e`: it
challenges `e`, `e` is neither exposed nor challenged in `s`, and A or B has a key recorded
at `e`. -/
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

/-- No query of the honest intermediate game `honestOracle m e kStar` removes an epoch `u`
from `challenged`. -/
theorem honestOracle_preserves_challenged (m : Material leak) (e : ℕ) (kStar : K) (u : ℕ) :
    QueryImpl.PreservesInv (honestOracle base onoff ecEk ecCt0 ecCt1 leak m e kStar)
      (fun s => u ∈ s.challenged) := by
  intro t s hs z hz
  rw [honestOracle, securityImplAt_run] at hz
  exact SCKAScheme.securityImplOf_challenged_subset _ _ _ _ _
    (fun t s z hz => (SCKAScheme.correctnessImpl_securitySets_eq _ t s z hz).2)
    (pinnedChallenge_recordsChallenges onoff e kStar) t s z hz hs

/-- If `usesChallengeKey e t s = false`, then for all keys `k`, `k'`, answering `t` from `s`
gives the same computation in `honestOracle m e k` and `honestOracle m e k'`. -/
theorem honestOracle_eq_of_unused (m : Material leak) (e : ℕ) (k k' : K)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (h : usesChallengeKey e t s = false) :
    (honestOracle base onoff ecEk ecCt0 ecCt1 leak m e k t).run s =
      (honestOracle base onoff ecEk ecCt0 ecCt1 leak m e k' t).run s := by
  rcases t with (((((t | a) | a) | t) | a) | a)
  all_goals try rfl
  simp only [securityImplAt, honestOracle, StateT.run_bind, StateT.run_get, pure_bind]
  exact pinnedChallenge_eq_of_unused onoff e t k k' s (of_decide_eq_false h)

/-- If `usesChallengeKey e t s = true`, then every possible successor state of
`honestOracle m e k` answering `t` from `s` has `e ∈ challenged`. -/
theorem honestOracle_use_records_challenge (m : Material leak) (e : ℕ) (k : K)
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

/-- Challenge mode of the pinned hybrids at epoch `e`: the challenge at `t` is randomized
exactly when `0 < t < e`, or when `t = e` and `b = true`. -/
def adjacentMode (e : ℕ) (b : Bool) (t : ℕ) : Bool :=
  decide (0 < t ∧ (t < e ∨ (b = true ∧ t = e)))

/-- Pinned hybrid: the security oracles over the protocol instance `honestScheme m e s` with
challenge oracle `challOf (adjacentMode e b)`. -/
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

/-- The pinned hybrid `hybridOracle m e b`, answering `⊥` (the outer `OptionT` failure) at
every query whose successor state has `e` exposed. -/
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

/-- For every query `t` and state `s` satisfying `reachableInv` and `pinnedKey m e`, answering
`t` from `s` gives the same computation in `honestOracle m e m.on.1.2` and
`hybridOracle m e false`. -/
theorem honestOracle_eq_hybrid_real
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

/-- Assume deterministic decapsulation and correct erasure codes. For every
`m ∈ support (sampleMaterial leak)` and adversary `adv`, the runs
`optionRun (honestStopped m e m.on.1.2) adv s₀` and `optionRun (hybridStopped m e false) adv s₀`
from the initial game state `s₀` return `true` with equal probability. -/
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
/-- For `e > 0`, every challenged epoch `t`, and every state `s`, drawing `k ←$ K` and running
`pinnedChallenge e k t` from `s` gives the joint response/state distribution of
`oracleChall (adjacentMode e true t) t` from `s`. -/
theorem pinnedChallenge_sample_uniform
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

/-- For `e > 0`, every query `t`, and every state `s`, drawing `k ←$ K` and answering `t` with
`honestOracle m e k` from `s` gives the joint response/state distribution of
`hybridOracle m e true` answering `t` from `s`. -/
theorem honestOracle_sample_uniform
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

/-- For every material `m`, epoch `e > 0`, adversary `adv`, and state `s`, drawing `k ←$ K`
once before the execution and running `optionRun (honestStopped m e k) adv s` returns `true`
with the probability of `optionRun (hybridStopped m e true) adv s`, which samples its key when
`e` is challenged. -/
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

/-- Assume deterministic decapsulation and correct erasure codes. For every adversary `adv`,
epoch `e > 0`, and IND-CPA bit `b`, `fixedBranch adv e b` returns `true` with the probability
that sampling `m ← sampleMaterial leak` and running
`optionRun (hybridStopped m e (!b)) adv s₀` from the initial game state `s₀` does. The
IND-CPA bit `true` selects the encapsulated key; the hybrid bit `true` randomizes the
challenge at `e`. -/
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
