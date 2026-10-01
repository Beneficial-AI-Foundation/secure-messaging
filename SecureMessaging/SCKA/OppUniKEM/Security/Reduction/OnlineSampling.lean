/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.OnlineFirstUse
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.SamplingStages

/-!
# Deferring the selected online sample

Fix selected key-generation and offline material. The selected online
sampler is `leak.encapsOnRleak m.off.1.1 m.keygen.1.1`. The pinned hybrid
reads its output at fresh online encapsulation; later real challenges use
the recorded key, and random challenges draw independently.

The one-use argument separates three facts: queries outside that sampling
phase are independent of the online material; a continuing first use
records B's epoch key; and that record persists. Transcript consistency
identifies the sampler's stored inputs with the protocol's actual inputs.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable [DecidableEq Sym]

set_option maxHeartbeats 800000 in
-- Split only the local send phases; the game bookkeeping is handled separately.
/-- Fix key-generation and offline material. Whenever B is outside the
selected epoch or its next send is not ready for online encapsulation,
changing the pinned online output leaves its ordinary send unchanged. -/
theorem sendB_online_independent
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hh : ¬(s.stB.t = e ∧ onlineReady s.stB))
    (online online' : (onoff.C₁ × K) × leak.OnRand) :
    (honestScheme ecEk ecCt0 ecCt1
      { m with on := online } e s).sendB s.stB =
    (honestScheme ecEk ecCt0 ecCt1
      { m with on := online' } e s).sendB s.stB := by
  by_cases he : s.stB.t = e <;> cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;>
    cases hc1 : s.stB.ct1 <;> cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
  all_goals
    simp only [onlineReady, he, hc0, hp, hc1, hst, ha,
      Option.isSome_none, Option.isSome_some, Option.isNone_none, Option.isNone_some,
      Bool.false_eq_true, and_false, and_true,
      false_or, true_or, or_self, not_true_eq_false] at hh
  all_goals
    simp only [honestScheme, scheme, sendB, hc0, hp, hc1, hst, ha, pure_bind,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      Pinned.onOff, Pinned.encapsOff, Pinned.encapsOn, he, decide_true, decide_false]

set_option maxHeartbeats 800000 in
-- Split only the local send phases; the game bookkeeping is handled separately.
/-- Fix key-generation and offline material. Whenever B is outside the
selected epoch or its next send is not ready for online encapsulation,
changing the pinned online output leaves its leaking send unchanged. -/
theorem sendBrleak_online_independent
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hh : ¬(s.stB.t = e ∧ onlineReady s.stB))
    (online online' : (onoff.C₁ × K) × leak.OnRand) :
    (honestScheme ecEk ecCt0 ecCt1
      { m with on := online } e s).sendBrleak s.stB =
    (honestScheme ecEk ecCt0 ecCt1
      { m with on := online' } e s).sendBrleak s.stB := by
  by_cases he : s.stB.t = e <;> cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;>
    cases hc1 : s.stB.ct1 <;> cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
  all_goals
    simp only [onlineReady, he, hc0, hp, hc1, hst, ha,
      Option.isSome_none, Option.isSome_some, Option.isNone_none, Option.isNone_some,
      Bool.false_eq_true, and_false, and_true,
      false_or, true_or, or_self, not_true_eq_false] at hh
  all_goals
    simp only [honestScheme, scheme, sendBrleak, hc0, hp, hc1, hst, ha, pure_bind,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      Pinned.leakage, he, decide_true, decide_false]


/-- When B is ready for selected online encapsulation and that epoch has
already been challenged, its pinned leaking-send oracle rejects and retains
the entire input state, for every selected online output. -/
theorem oracleSendBrleak_online_rejected [DecidableEq K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (he : s.stB.t = e) (hready : onlineReady s.stB) (hc : e ∈ s.challenged) :
    (SCKAScheme.oracleSendBrleak sendExposureB
      (honestScheme ecEk ecCt0 ecCt1 m e s) ()).run s = pure (none, s) := by
  obtain ⟨ha, hp, hc1, hsrc⟩ := hready
  obtain ⟨pk, hp⟩ := Option.isSome_iff_exists.mp hp
  have hc1 : s.stB.ct1 = none := Option.isNone_iff_eq_none.mp hc1
  cases hc0 : s.stB.ct0 <;> cases hst : s.stB.stCt
  all_goals simp only [hc0, hst, Option.isNone_some, Option.isNone_none,
    Option.isSome_none, Option.isSome_some, Bool.false_eq_true, or_false] at hsrc
  all_goals
    simp [SCKAScheme.oracleSendBrleak, honestScheme, scheme, sendBrleak,
      Pinned.leakage, sendExposureB, he, ha, hp, hc1, hc0, hst, hc]

variable [DecidableEq K] [SampleableType K]

/-- Fix key-generation and offline material. For every query and state with
`usesOnline e t s = false`, replacing the online component of the material
leaves the pinned hybrid query's response/state computation unchanged. -/
theorem hybridOracle_online_independent
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hh : usesOnline e t s = false)
    (online online' : (onoff.C₁ × K) × leak.OnRand) :
    (hybridOracle base onoff ecEk ecCt0 ecCt1 leak { m with on := online } e b t).run s =
    (hybridOracle base onoff ecEk ecCt0 ecCt1 leak { m with on := online' } e b t).run s := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n)
    · rfl
    · cases u
      simp only [hybridOracle, honestOracle, StateT.run_bind, StateT.run_get, pure_bind,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        SCKAScheme.oracleSendA]
      congr 1
    · cases u
      have hno : ¬(s.stB.t = e ∧ onlineReady s.stB) := of_decide_eq_false hh
      simp only [hybridOracle, honestOracle, StateT.run_bind, StateT.run_get, pure_bind,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        SCKAScheme.oracleSendB]
      rw [sendB_online_independent base onoff ecEk ecCt0 ecCt1 leak m e s hno online online']
    · simp only [hybridOracle, honestOracle, StateT.run_bind, StateT.run_get, pure_bind,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        SCKAScheme.oracleRecvA]
      cases hm : s.msgB n with
      | none => rfl
      | some out =>
        rcases out with ⟨msg, epoch⟩
        simp only
        rw [honest_recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak
          { m with on := online } e s msg,
          honest_recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak
            { m with on := online' } e s msg]
    · rfl
  · cases u
    simp only [hybridOracle, honestOracle, SCKAScheme.oracleSendArleak,
      StateT.run_bind, StateT.run_get, pure_bind]
    congr 1
  · cases u
    by_cases hready : s.stB.t = e ∧ onlineReady s.stB
    · have hc : e ∈ s.challenged := by
        have hnot : ¬((s.stB.t = e ∧ onlineReady s.stB) ∧ e ∉ s.challenged) :=
          of_decide_eq_false hh
        by_contra hc
        exact hnot ⟨hready, hc⟩
      exact (oracleSendBrleak_online_rejected base onoff ecEk ecCt0 ecCt1 leak
        { m with on := online } e s hready.1 hready.2 hc).trans
        (oracleSendBrleak_online_rejected base onoff ecEk ecCt0 ecCt1 leak
          { m with on := online' } e s hready.1 hready.2 hc).symm
    · simp only [hybridOracle, honestOracle, SCKAScheme.oracleSendBrleak,
        StateT.run_bind, StateT.run_get, pure_bind]
      rw [sendBrleak_online_independent base onoff ecEk ecCt0 ecCt1 leak
        m e s hready online online']
      apply bind_congr
      rintro ⟨out, next⟩
      cases out with
      | none => rfl
      | some out =>
        rcases out with ⟨key, msg, epoch, state, coins⟩
        cases coins <;> cases key <;> rfl
  · rfl
  · rfl
  · rfl


omit [DecidableEq K] [DecidableEq Sym] [SampleableType K] in
/-- If `m` is supported, replacing its online output by any output supported
at the same public key and offline state yields supported complete material. -/
theorem sampleMaterial_update_online_mem
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) (m : Material leak)
    (hm : m ∈ support (sampleMaterial leak))
    (online : (onoff.C₁ × K) × leak.OnRand)
    (hon : online ∈ support (leak.encapsOnRleak m.off.1.1 m.keygen.1.1)) :
    { m with on := online } ∈ support (sampleMaterial leak) := by
  obtain ⟨hkg, hoff, _⟩ := sampleMaterial_support leak m hm
  simp only [sampleMaterial, mem_support_bind_iff, mem_support_pure_iff]
  exact ⟨m.keygen, hkg, m.off, hoff, online, hon, rfl⟩

/-- Assume supported source material, deterministic decapsulation, and
correct erasure codes. For every adversary and state satisfying transcript
consistency and `pinnedSources`, sampling the selected online output once
before execution or independently at each query gives equal acceptance
probabilities in either stopped pinned hybrid. -/
theorem hybridStopped_sample_online_eq
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
      (sampleEachQuery (leak.encapsOnRleak m.off.1.1 m.keygen.1.1)
        (fun online => hybridStopped base onoff ecEk ecCt0 ecCt1 leak
          { m with on := online } e b)) adv s] := by
  apply optionRun_sample_once_eq_sampleEachQuery _ _
    (fun s => reachableInv base onoff ecEk ecCt0 ecCt1 s ∧ pinnedSources m e s)
    (fun s => (s.keyB e).isSome) (usesOnline e)
  · intro online hon t s hs z hz _
    change z ∈ support (do
      let out ← (hybridOracle base onoff ecEk ecCt0 ecCt1 leak
        { m with on := online } e b t).run s
      pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2)) at hz
    obtain ⟨out, hout, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    obtain rfl := (mem_support_pure_iff _ _).mp hz
    exact hybridOracle_preserves_simulationInv base onoff hDet ecEk hEk ecCt0 hCt0
      ecCt1 hCt1 leak { m with on := online }
      (sampleMaterial_update_online_mem leak m hm online hon)
      e b t s hs out hout
  · intro online _ t s _ hu z hz _
    change z ∈ support (do
      let out ← (hybridOracle base onoff ecEk ecCt0 ecCt1 leak
        { m with on := online } e b t).run s
      pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2)) at hz
    obtain ⟨out, hout, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    obtain rfl := (mem_support_pure_iff _ _).mp hz
    exact hybridOracle_preserves_keyB_available base onoff ecEk ecCt0 ecCt1 leak
      { m with on := online } e b t s hu out hout
  · intro t s _ hh online _ online' _
    refine congrArg evalDist ?_
    change (do
      let out ← (hybridOracle base onoff ecEk ecCt0 ecCt1 leak
        { m with on := online } e b t).run s
      pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2)) = _
    rw [hybridOracle_online_independent base onoff ecEk ecCt0 ecCt1 leak
      m e b t s hh online online']
    rfl
  · intro t s hs hu
    exact usesOnline_eq_false_of_recorded base onoff ecEk ecCt0 ecCt1 leak e t s hs.1 hu
  · intro online _ t s _ hh z hz hcont
    exact hybridStopped_online_records_key base onoff ecEk ecCt0 ecCt1 leak
      { m with on := online } e b t s hh z hz hcont
  · exact ⟨hs, hsrc⟩

end oppUniKemCKA.Security.Embedding
