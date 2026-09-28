/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.OnlineFresh
import SecureMessaging.SCKA.Security.Sampling

/-!
# Online sampling in the full security oracle

**Parameters.** Fix material `m`, selected epoch `e`, challenge mode `b`,
and a state satisfying `reachableInv` and `pinnedSources m e`.

**Statement.** For every security query, averaging its pinned online
material gives the response/state distribution of the `onlineFresh` stage.

**Proof.** B's sends use the local sampling comparisons from `OnlineFresh`.
The game bookkeeping is a shared continuation, including the leakage
guard. All other queries have the same computation for every online sample.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- For every query and state satisfying transcript consistency and the
selected source invariant, averaging the pinned online material gives the
joint response/state distribution of fresh online sampling at that query. -/
theorem hybridOracle_sample_online_eq_fresh
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hsrc : pinnedSources m e s) :
    𝒟[(do
      let online ← leak.encapsOnRleak m.off.1.1 m.keygen.1.1
      (hybridOracle base onoff ecEk ecCt0 ecCt1 leak { m with on := online } e b t).run s)] =
    𝒟[(Sampling.oracle base onoff ecEk ecCt0 ecCt1 leak .onlineFresh m e b t).run s] := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n)
    · apply evalDist_ext
      intro z
      apply ToVCVio.probOutput_bind_of_const'
      intro online _
      rfl
    · cases u
      simp only [hybridOracle, honestOracle, Sampling.oracle,
        StateT.run_bind, StateT.run_get, pure_bind, SCKAScheme.sckaCorrectnessImpl,
        QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
      apply SCKAScheme.oracleSendA_sample_eq
      apply evalDist_ext
      intro z
      apply ToVCVio.probOutput_bind_of_const'
      intro online _
      rfl
    · cases u
      simp only [hybridOracle, honestOracle, Sampling.oracle,
        StateT.run_bind, StateT.run_get, pure_bind, SCKAScheme.sckaCorrectnessImpl,
        QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
      exact SCKAScheme.oracleSendB_sample_eq _ _ _ s
        (sendB_sample_online_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e s hs hsrc)
    · apply evalDist_ext
      intro z
      apply ToVCVio.probOutput_bind_of_const'
      intro online _
      simp only [hybridOracle, honestOracle, Sampling.oracle,
        StateT.run_bind, StateT.run_get, pure_bind, SCKAScheme.sckaCorrectnessImpl,
        QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, SCKAScheme.oracleRecvA]
      cases hm : s.msgB n with
      | none => rfl
      | some out =>
        rcases out with ⟨msg, epoch⟩
        simp only
        rw [honest_recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak
          { m with on := online } e s msg,
          Sampling.recvA_eq_auxiliary base onoff ecEk ecCt0 ecCt1 leak .onlineFresh m e s msg]
    · apply evalDist_ext
      intro z
      apply ToVCVio.probOutput_bind_of_const'
      intro online _
      rfl
  · cases u
    simp only [hybridOracle, honestOracle, Sampling.oracle,
      StateT.run_bind, StateT.run_get, pure_bind, Sampling.sendExposureA_eq]
    apply SCKAScheme.oracleSendArleak_sample_eq
    apply evalDist_ext
    intro z
    apply ToVCVio.probOutput_bind_of_const'
    intro online _
    rfl
  · cases u
    simp only [hybridOracle, honestOracle, Sampling.oracle,
      StateT.run_bind, StateT.run_get, pure_bind, Sampling.sendExposureB_eq]
    exact SCKAScheme.oracleSendBrleak_sample_eq _ _ _ _ s
      (sendBrleak_sample_online_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e s hs hsrc)
  all_goals
    apply evalDist_ext
    intro z
    apply ToVCVio.probOutput_bind_of_const'
    intro online _
    rfl

/-- Under transcript consistency and the selected source invariant,
averaging the stopped pinned query gives the stopped fresh-online query.
Both kernels apply the same exposure test to the successor state. -/
theorem hybridStopped_sample_online_query_eq_fresh
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hsrc : pinnedSources m e s) :
    𝒟[(do
      let online ← leak.encapsOnRleak m.off.1.1 m.keygen.1.1
      ((hybridStopped base onoff ecEk ecCt0 ecCt1 leak
        { m with on := online } e b t).run).run s)] =
    𝒟[((Sampling.stopped base onoff ecEk ecCt0 ecCt1 leak
      .onlineFresh m e b t).run).run s] := by
  change 𝒟[(do
      let online ← leak.encapsOnRleak m.off.1.1 m.keygen.1.1
      let out ← (hybridOracle base onoff ecEk ecCt0 ecCt1 leak
        { m with on := online } e b t).run s
      pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2))] = _
  rw [← bind_assoc, evalDist_bind,
    hybridOracle_sample_online_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e b t s hs hsrc,
    ← evalDist_bind]
  rfl

/-- Assume supported material, deterministic decapsulation, and correct
erasure codes. For every adversary, mode, and state satisfying transcript
consistency and `pinnedSources`, sampling the selected online output before
execution gives the acceptance probability of the `onlineFresh` stage. -/
theorem hybridStopped_online_deferred
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (hm : m ∈ support (sampleMaterial leak)) (e : ℕ) (b : Bool)
    (adv : SecurityAdversary leak Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hsrc : pinnedSources m e s) :
    Pr[= true | do
      let online ← leak.encapsOnRleak m.off.1.1 m.keygen.1.1
      optionRun (hybridStopped base onoff ecEk ecCt0 ecCt1 leak { m with on := online } e b)
        adv s] =
    Pr[= true | optionRun
      (Sampling.stopped base onoff ecEk ecCt0 ecCt1 leak .onlineFresh m e b) adv s] := by
  rw [hybridStopped_sample_online_eq base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
    leak m hm e b adv s hs hsrc]
  symm
  apply probOutput_optionRun_eq_of_state_map _ _ id
    (fun s => reachableInv base onoff ecEk ecCt0 ecCt1 s ∧ pinnedSources m e s)
  · intro t s hs z hz _
    change z ∈ support (do
      let online ← leak.encapsOnRleak m.off.1.1 m.keygen.1.1
      let out ← (hybridOracle base onoff ecEk ecCt0 ecCt1 leak
        { m with on := online } e b t).run s
      pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2)) at hz
    simp only [mem_support_bind_iff, mem_support_pure_iff] at hz
    obtain ⟨online, hon, out, hout, rfl⟩ := hz
    exact hybridOracle_preserves_simulationInv base onoff hDet ecEk hEk ecCt0 hCt0
      ecCt1 hCt1 leak { m with on := online }
      (sampleMaterial_update_online_mem leak m hm online hon) e b t s hs out hout
  · intro t s hs
    have hmap : Prod.map (id : Option ((securitySpec leak Sym).Range t) → _)
        (id : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) → _) =
        id := rfl
    simpa only [hmap, id_map, id_eq, sampleEachQuery_run] using
      (hybridStopped_sample_online_query_eq_fresh base onoff ecEk ecCt0 ecCt1 leak
        m e b t s hs.1 hs.2).symm
  · exact ⟨hs, hsrc⟩

end oppUniKemCKA.Security.Embedding
