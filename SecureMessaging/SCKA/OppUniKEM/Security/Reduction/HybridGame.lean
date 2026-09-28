/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Keys
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Simulation
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.ChallengeSampling

/-!
# Pinned games with ordinary hybrid challenges

**Construction.** Fix material `m`, positive epoch `e`, and Boolean `b`.
`hybridOracle` uses the pinned protocol samplers and ordinary challenge
responses: positive epochs below `e` are randomized, epoch `e` is randomized
exactly when `b = true`, and later epochs use their recorded keys.

**Role.** These games separate the protocol's online sample from the
challenge response. The selected recorded-key invariant identifies the
real branch; one-use sampling moves a uniform supplied key to its challenge
query. The next proof step defers each pinned protocol sample to its
key-generation, offline, or online phase.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Challenge mode for the two games adjacent to epoch `e`: randomize
positive epochs below `e`, together with `e` when `b = true`. -/
def adjacentMode (e : ℕ) (b : Bool) (t : ℕ) : Bool :=
  decide (0 < t ∧ (t < e ∨ (b = true ∧ t = e)))

/-- Full pinned protocol oracle with ordinary hybrid challenges. Honest
key tables supply every real response; randomized responses are sampled
at the challenge query. -/
def hybridOracle
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (b : Bool) :
    QueryImpl (securitySpec leak Sym)
      (StateT (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) ProbComp) :=
  fun t => match t with
    | .inl (.inl (.inr epoch)) =>
      SCKAScheme.oracleChall (adjacentMode e b epoch)
        (StA onoff Sym) (StB onoff Sym) K (Message Sym) epoch
    | query => honestOracle base onoff ecEk ecCt0 ecCt1 leak m e m.on.1.2 query

/-- Pinned hybrid oracle stopped after any query exposing the selected
epoch. Termination is represented by the outer `OptionT` layer. -/
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

/-- For every transcript-consistent state satisfying `pinnedKey m e` and
every query, the honest oracle supplied with `m.on.1.2` equals the pinned
hybrid oracle with a real challenge at epoch `e`. -/
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
  simp only [honestOracle, hybridOracle, StateT.run_bind, StateT.run_get, pure_bind,
    adjacentMode, Bool.false_eq_true, false_and, or_false]
  exact pinnedChallenge_eq_recorded onoff e m.on.1.2 t s
    (pinnedKey_both base onoff ecEk ecCt0 ecCt1 leak m e s hs hm)


/-- For every supported material value and adversary, supplying the honest
selected key in the stopped game has the same acceptance probability as
using ordinary hybrid challenges with a real response at epoch `e`. -/
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
    exact ⟨honestOracle_preserves_simulationInv base onoff hDet ecEk hEk ecCt0 hCt0
      ecCt1 hCt1 leak m hm e m.on.1.2 t s hs.1 out hout,
      honestOracle_preserves_pinnedKey base onoff ecEk ecCt0 ecCt1 leak
        m e m.on.1.2 t s hs.2 out hout⟩
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
/-- For every positive selected epoch, queried epoch, and game state,
supplying an independent uniform key to the pinned challenge gives the
ordinary challenge distribution randomizing epochs `1, …, e`. -/
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
  · simp [pinnedChallenge, SCKAScheme.oracleChall, hg]
  · by_cases ht : t = e
    · subst t
      cases hA : s.keyA e <;> cases hB : s.keyB e <;>
        simp [pinnedChallenge, SCKAScheme.oracleChall, adjacentMode, hg, hA, hB, he]
    · cases hA : s.keyA t <;> cases hB : s.keyB t <;> by_cases hr : 0 < t ∧ t < e <;>
        simp [probOutput_bind_const, pinnedChallenge, SCKAScheme.oracleChall,
          adjacentMode, hg, hA, hB, ht, hr]


/-- For every material value, positive selected epoch, query, and state,
averaging the supplied challenge key uniformly gives the pinned hybrid
query distribution with a random response at the selected epoch. -/
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
    | simpa only [honestOracle, hybridOracle, StateT.run_bind, StateT.run_get, pure_bind]
        using pinnedChallenge_sample_uniform onoff e he t s
    | apply evalDist_ext
      intro z
      simp only [honestOracle, hybridOracle, StateT.run_bind, StateT.run_get, pure_bind,
        probOutput_bind_const, probFailure_eq_zero, tsub_zero, one_mul]

/-- For every material value, positive selected epoch, adversary, and
initial state, the stopped honest game with an eagerly sampled uniform
challenge key has the same acceptance probability as the stopped pinned
hybrid with a random response at epoch `e`. -/
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
    Pr[= true | optionRun (hybridStopped base onoff ecEk ecCt0 ecCt1 leak m e true) adv s] := by
  rw [honestStopped_sample_key_eq]
  apply probOutput_optionRun_eq_of_state_map _ _ id (fun _ => True)
  · intros; trivial
  · intro t s _
    simp only [id_eq, Prod.map_id, id_map]
    change 𝒟[(do
      let k ← ($ᵗ K : ProbComp K)
      let out ← (honestOracle base onoff ecEk ecCt0 ecCt1 leak m e k t).run s
      pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2))] = _
    rw [← bind_assoc, evalDist_bind,
      honestOracle_sample_uniform base onoff ecEk ecCt0 ecCt1 leak m e he t s]
    change _ = 𝒟[(do
      let out ← (hybridOracle base onoff ecEk ecCt0 ecCt1 leak m e true t).run s
      pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2))]
    rw [evalDist_bind]
  · trivial

/-- Assume deterministic decapsulation and correct erasure codes. For every
adversary, positive selected epoch, and KEM branch bit `b`, the fixed
reduction branch equals, in acceptance probability, the stopped pinned
hybrid with mode `!b` averaged over complete material samples. KEM bit
`true` denotes a real key; hybrid bit `true` denotes a random response. -/
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
