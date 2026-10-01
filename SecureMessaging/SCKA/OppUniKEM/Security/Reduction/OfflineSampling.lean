/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.OfflineIndependence
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.OfflineOracle

/-!
# Deferral of the selected offline sample

**Statement.** For every material value, selected epoch, challenge mode,
adversary, and initial state, averaging the stored offline sample in
`onlineFresh` gives the acceptance probability of `encapsFresh`.

**Proof.** The one-use sampling theorem moves the sample to each query.
`SourceUse` and `SourceFirstUse` supply the used-state conditions;
`OfflineIndependence` proves equality outside first use, including leakage
rejection. `OfflineOracle` identifies the averaged query distribution with
fresh offline sampling. These arguments apply to every input state.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding.Sampling

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- For every material value, epoch, mode, adversary, and input state,
sampling the selected offline output once or independently at each query
gives equal acceptance probabilities in the stopped `onlineFresh` game. -/
theorem stopped_sample_offline_eq
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (b : Bool) (adv : SecurityAdversary leak Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    Pr[= true | do
      let offline ← leak.encapsOffRleak
      optionRun (stopped base onoff ecEk ecCt0 ecCt1 leak
        .onlineFresh { m with off := offline } e b) adv s] =
    Pr[= true | optionRun (sampleEachQuery leak.encapsOffRleak
      (fun offline => stopped base onoff ecEk ecCt0 ecCt1 leak
        .onlineFresh { m with off := offline } e b)) adv s] := by
  apply optionRun_sample_once_eq_sampleEachQuery _ _ (fun _ => True)
    (fun s => sourceUsed .offline e s.stA s.stB) (usesSource .offline e)
  · intros; trivial
  · intro offline _ t s _ hu z hz _
    change z ∈ support (do
      let out ← (oracle base onoff ecEk ecCt0 ecCt1 leak
        .onlineFresh { m with off := offline } e b t).run s
      pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2)) at hz
    obtain ⟨out, hout, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    obtain rfl := (mem_support_pure_iff _ _).mp hz
    exact oracle_preserves_sourceUsed base onoff ecEk ecCt0 ecCt1 leak
      .onlineFresh { m with off := offline } e b .offline t s hu out hout
  · intro t s _ hh offline _ offline' _
    change 𝒟[(do
      let out ← (oracle base onoff ecEk ecCt0 ecCt1 leak
        .onlineFresh { m with off := offline } e b t).run s
      pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2))] = _
    simp only [evalDist_bind,
      oracle_offline_independent base onoff ecEk ecCt0 ecCt1 leak
        m e b t s hh offline offline']
    rw [← evalDist_bind]
    rfl
  · intro t s _ hu
    exact usesSource_false_of_used .offline e t s hu
  · intro offline _ t s _ hh z hz hcont
    exact stopped_first_source_use base onoff ecEk ecCt0 ecCt1 leak
      .onlineFresh { m with off := offline } e b .offline t s hh z hz hcont
  · trivial

/-- For every query, material value, selected epoch, mode, and input state,
averaging the stopped `onlineFresh` query over offline material gives the
stopped `encapsFresh` query's joint optional-response/state distribution. -/
theorem stopped_sample_offline_query_eq_fresh
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    𝒟[(do
      let offline ← leak.encapsOffRleak
      ((stopped base onoff ecEk ecCt0 ecCt1 leak
        .onlineFresh { m with off := offline } e b t).run).run s)] =
    𝒟[((stopped base onoff ecEk ecCt0 ecCt1 leak .encapsFresh m e b t).run).run s] := by
  change 𝒟[(do
      let offline ← leak.encapsOffRleak
      let out ← (oracle base onoff ecEk ecCt0 ecCt1 leak
        .onlineFresh { m with off := offline } e b t).run s
      pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2))] = _
  rw [← bind_assoc, evalDist_bind,
    oracle_sample_offline_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e b t s,
    ← evalDist_bind]
  rfl

/-- For every material value, selected epoch, challenge mode, adversary,
and input state, sampling the selected offline output before execution in
`onlineFresh` gives the acceptance probability of the `encapsFresh` stage. -/
theorem stopped_offline_deferred
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (b : Bool) (adv : SecurityAdversary leak Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    Pr[= true | do
      let offline ← leak.encapsOffRleak
      optionRun (stopped base onoff ecEk ecCt0 ecCt1 leak
        .onlineFresh { m with off := offline } e b) adv s] =
    Pr[= true | optionRun (stopped base onoff ecEk ecCt0 ecCt1 leak .encapsFresh m e b)
      adv s] := by
  rw [stopped_sample_offline_eq base onoff ecEk ecCt0 ecCt1 leak m e b adv s]
  symm
  apply probOutput_optionRun_eq_of_state_map _ _ id (fun _ => True)
  · intros; trivial
  · intro t s _
    have hmap : Prod.map (id : Option ((securitySpec leak Sym).Range t) → _)
        (id : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) → _) =
        id := rfl
    simpa only [hmap, id_map, id_eq, sampleEachQuery_run] using
      (stopped_sample_offline_query_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e b t s).symm
  · trivial

end oppUniKemCKA.Security.Embedding.Sampling
