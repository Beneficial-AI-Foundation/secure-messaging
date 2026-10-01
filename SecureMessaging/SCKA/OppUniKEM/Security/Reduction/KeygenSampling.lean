/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.KeygenIndependence
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.KeygenOracle

/-!
# Deferral of the selected key-generation sample

**Statement.** For every material value, selected epoch, challenge mode,
adversary, and initial state, averaging the stored key-generation sample in
`encapsFresh` gives the acceptance probability of `fresh`.

**Proof.** The one-use sampling theorem moves the sample to each query.
`SourceUse` and `SourceFirstUse` supply the used-state conditions;
`KeygenIndependence` proves equality outside first use, including leakage
rejection. `KeygenOracle` identifies the averaged query distribution with
fresh key-generation sampling. These arguments apply to every input state.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding.Sampling

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- For every material value, epoch, mode, adversary, and input state,
sampling the selected key-generation output once or independently at each query
gives equal acceptance probabilities in the stopped `encapsFresh` game. -/
theorem stopped_sample_keygen_eq
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (b : Bool) (adv : SecurityAdversary leak Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    Pr[= true | do
      let keygen ← leak.keygenRleak
      optionRun (stopped base onoff ecEk ecCt0 ecCt1 leak
        .encapsFresh { m with keygen := keygen } e b) adv s] =
    Pr[= true | optionRun (sampleEachQuery leak.keygenRleak
      (fun keygen => stopped base onoff ecEk ecCt0 ecCt1 leak
        .encapsFresh { m with keygen := keygen } e b)) adv s] := by
  apply optionRun_sample_once_eq_sampleEachQuery _ _ (fun _ => True)
    (fun s => sourceUsed .keygen e s.stA s.stB) (usesSource .keygen e)
  · intros; trivial
  · intro keygen _ t s _ hu z hz _
    change z ∈ support (do
      let out ← (oracle base onoff ecEk ecCt0 ecCt1 leak
        .encapsFresh { m with keygen := keygen } e b t).run s
      pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2)) at hz
    obtain ⟨out, hout, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    obtain rfl := (mem_support_pure_iff _ _).mp hz
    exact oracle_preserves_sourceUsed base onoff ecEk ecCt0 ecCt1 leak
      .encapsFresh { m with keygen := keygen } e b .keygen t s hu out hout
  · intro t s _ hh keygen _ keygen' _
    change 𝒟[(do
      let out ← (oracle base onoff ecEk ecCt0 ecCt1 leak
        .encapsFresh { m with keygen := keygen } e b t).run s
      pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2))] = _
    simp only [evalDist_bind,
      oracle_keygen_independent base onoff ecEk ecCt0 ecCt1 leak
        m e b t s hh keygen keygen']
    rw [← evalDist_bind]
    rfl
  · intro t s _ hu
    exact usesSource_false_of_used .keygen e t s hu
  · intro keygen _ t s _ hh z hz hcont
    exact stopped_first_source_use base onoff ecEk ecCt0 ecCt1 leak
      .encapsFresh { m with keygen := keygen } e b .keygen t s hh z hz hcont
  · trivial

/-- For every query, material value, selected epoch, mode, and input state,
averaging the stopped `encapsFresh` query over key-generation material gives the
stopped `fresh` query's joint optional-response/state distribution. -/
theorem stopped_sample_keygen_query_eq_fresh
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    𝒟[(do
      let keygen ← leak.keygenRleak
      ((stopped base onoff ecEk ecCt0 ecCt1 leak
        .encapsFresh { m with keygen := keygen } e b t).run).run s)] =
    𝒟[((stopped base onoff ecEk ecCt0 ecCt1 leak .fresh m e b t).run).run s] := by
  change 𝒟[(do
      let keygen ← leak.keygenRleak
      let out ← (oracle base onoff ecEk ecCt0 ecCt1 leak
        .encapsFresh { m with keygen := keygen } e b t).run s
      pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2))] = _
  rw [← bind_assoc, evalDist_bind,
    oracle_sample_keygen_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e b t s,
    ← evalDist_bind]
  rfl

/-- For every material value, selected epoch, challenge mode, adversary,
and input state, sampling the selected key-generation output before execution in
`encapsFresh` gives the acceptance probability of the `fresh` stage. -/
theorem stopped_keygen_deferred
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (b : Bool) (adv : SecurityAdversary leak Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    Pr[= true | do
      let keygen ← leak.keygenRleak
      optionRun (stopped base onoff ecEk ecCt0 ecCt1 leak
        .encapsFresh { m with keygen := keygen } e b) adv s] =
    Pr[= true | optionRun (stopped base onoff ecEk ecCt0 ecCt1 leak .fresh m e b)
      adv s] := by
  rw [stopped_sample_keygen_eq base onoff ecEk ecCt0 ecCt1 leak m e b adv s]
  symm
  apply probOutput_optionRun_eq_of_state_map _ _ id (fun _ => True)
  · intros; trivial
  · intro t s _
    have hmap : Prod.map (id : Option ((securitySpec leak Sym).Range t) → _)
        (id : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) → _) =
        id := rfl
    simpa only [hmap, id_map, id_eq, sampleEachQuery_run] using
      (stopped_sample_keygen_query_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e b t s).symm
  · trivial

end oppUniKemCKA.Security.Embedding.Sampling
