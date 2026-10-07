/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.SourceUse
import ToVCVio.OracleComp.QueryTracking.OneUseSampling
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.OnlineDeferral

/-!
# Deferring the offline sample

**Setting.** Fix complete material `m`, a selected epoch `e`, and a mode bit `b`.

**Results.**

- `oracle_offline_independent`: in the stage `onlineFresh`, a query with
  `usesSource .offline e t s = false` has the same response/state distribution for every stored
  offline output; a leaking first send by B at a challenged epoch rejects
  (`leaking_offline_rejected`).
- `oracle_sample_offline_eq_fresh`: averaging a query of `onlineFresh` over the offline output
  gives the query of `encapsFresh` (`sendB_sample_offline_eq_fresh`,
  `sendBrleak_sample_offline_eq_fresh`).
- `stopped_offline_deferred`: sampling the offline output once before the stopped stage
  `onlineFresh` gives the acceptance probability of the stopped stage `encapsFresh`.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding.Sampling

variable {K PK SK C Sym : Type}
variable [DecidableEq Sym]

/-- For every state outside the selected first B-send, replacing the
stored offline output leaves the local sendBrleak computation in `onlineFresh`
unchanged. The subsequent online phase samples at its actual inputs. -/
theorem sendBrleak_offline_independent
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hh : ¬(s.stB.t = e ∧ s.stB.ct0.isNone))
    (offline offline' : (onoff.St × onoff.C₀) × leak.OffRand) :
    (schemeAt ecEk ecCt0 ecCt1 .onlineFresh { m with off := offline } e s).sendBrleak s.stB =
    (schemeAt ecEk ecCt0 ecCt1 .onlineFresh { m with off := offline' } e s).sendBrleak s.stB := by
  have hf : Stage.onlineFresh ≠ .fixed := by decide
  by_cases he : s.stB.t = e <;> cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;>
    cases hc1 : s.stB.ct1 <;> cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
  all_goals
    simp only [he, hc0, Option.isNone_none, Option.isNone_some, Bool.false_eq_true,
      and_true, and_false, not_true_eq_false] at hh
  all_goals
    simp only [schemeAt, Stage.pinsKeygen, Stage.pinsOffline, Stage.pinsOnline,
      scheme, sendBrleak, hc0, hp, hc1, hst, ha, pure_bind,
      Pinned.onOff, Pinned.leakage, Pinned.encapsOff,
      he, hf, or_true, decide_true, decide_false, Bool.and_true, Bool.true_and, Bool.false_and,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

/-- For every state outside the selected first B-send, replacing the
stored offline output leaves the local sendB computation in `onlineFresh`
unchanged. Derived from `sendBrleak_offline_independent` by forgetting the coins. -/
theorem sendB_offline_independent
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hh : ¬(s.stB.t = e ∧ s.stB.ct0.isNone))
    (offline offline' : (onoff.St × onoff.C₀) × leak.OffRand) :
    (schemeAt ecEk ecCt0 ecCt1 .onlineFresh { m with off := offline } e s).sendB s.stB =
    (schemeAt ecEk ecCt0 ecCt1 .onlineFresh { m with off := offline' } e s).sendB s.stB := by
  rw [scheme_sendB_eq_map_sendBrleak, scheme_sendB_eq_map_sendBrleak,
    sendBrleak_offline_independent base onoff ecEk ecCt0 ecCt1 leak m e s hh offline offline']

variable [DecidableEq K]

/-- For every sampling stage, a leaking first B-send in already challenged
epoch `e` has the rejection distribution concentrated at `(none,s)`.
The conclusion includes combined offline/online sampling before the guard. -/
theorem leaking_offline_rejected
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (stage : Stage) (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (he : s.stB.t = e) (hfield : s.stB.ct0 = none) (hc : e ∈ s.challenged) :
    𝒟[(SCKAScheme.oracleSendBrleak vulnRleakB
      (schemeAt ecEk ecCt0 ecCt1 stage m e s) ()).run s] = 𝒟[(pure (none, s) : ProbComp _)] := by
  apply SCKAScheme.oracleSendBrleak_rejected_evalDist _ _ s {e} ?_ ?_
  · intro key msg epoch next coins hout
    have hex := sendBrleak_exposure
      (Pinned.kem m (stage.pinsKeygen && decide (s.stA.t = e))
        (stage.pinsOffline && decide (s.stB.t = e))
        (stage.pinsOnline && decide (s.stB.t = e)) (s.keyB s.stA.t))
      (Pinned.onOff m _ _ _ _) ecCt0 ecCt1 (Pinned.leakage leak m _ _ _ _) s.stB
      key msg epoch next coins hout
    simpa only [leakEpochsB, hfield, Option.isNone_none,
      Bool.true_or, ↓reduceIte, he] using hex
  · simp [hc]

variable [SampleableType K]

/-- For every query with `usesSource .offline = false`, replacing the
stored offline component in `onlineFresh` preserves the entire joint
response/state distribution, including rejected leaking sends. -/
theorem oracle_offline_independent
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hh : usesSource .offline e t s = false)
    (offline offline' : (onoff.St × onoff.C₀) × leak.OffRand) :
    𝒟[(oracle base onoff ecEk ecCt0 ecCt1 leak
      .onlineFresh { m with off := offline } e b t).run s] =
    𝒟[(oracle base onoff ecEk ecCt0 ecCt1 leak
      .onlineFresh { m with off := offline' } e b t).run s] := by
  rcases t with (((((t | u) | u) | _) | u) | u) <;> try rcases t with ((((n | u) | u) | n) | n)
  all_goals try cases u
  all_goals simp only [oracle, securityImplAt, StateT.run_bind, StateT.run_get, pure_bind,
    SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
  · exact congrArg evalDist (SCKAScheme.oracleSendA_run_congr _ _ s rfl)
  · exact congrArg evalDist (SCKAScheme.oracleSendB_run_congr _ _ s
      (sendB_offline_independent base onoff ecEk ecCt0 ecCt1 leak m e s
        (of_decide_eq_false hh) offline offline'))
  · exact congrArg evalDist (SCKAScheme.oracleRecvA_run_congr _ _ s (fun ρ =>
      (recvA_eq_auxiliary base onoff ecEk ecCt0 ecCt1 leak .onlineFresh
        { m with off := offline } e s ρ).trans
      (recvA_eq_auxiliary base onoff ecEk ecCt0 ecCt1 leak .onlineFresh
        { m with off := offline' } e s ρ).symm) n)
  · rfl
  · exact congrArg evalDist (SCKAScheme.oracleSendArleak_run_congr _ _ _ s rfl)
  · by_cases hready : s.stB.t = e ∧ s.stB.ct0.isNone
    · have hc : e ∈ s.challenged := by
        have hnot : ¬((s.stB.t = e ∧ s.stB.ct0.isNone) ∧ e ∉ s.challenged) :=
          of_decide_eq_false hh
        by_contra hc
        exact hnot ⟨hready, hc⟩
      exact (leaking_offline_rejected base onoff ecEk ecCt0 ecCt1 leak .onlineFresh
        { m with off := offline } e s hready.1
        (Option.isNone_iff_eq_none.mp hready.2) hc).trans
        (leaking_offline_rejected base onoff ecEk ecCt0 ecCt1 leak .onlineFresh
          { m with off := offline' } e s hready.1
          (Option.isNone_iff_eq_none.mp hready.2) hc).symm
    · exact congrArg evalDist (SCKAScheme.oracleSendBrleak_run_congr _ _ _ s
        (sendBrleak_offline_independent base onoff ecEk ecCt0 ecCt1 leak m e s hready
          offline offline'))

end oppUniKemCKA.Security.Embedding.Sampling

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

set_option maxHeartbeats 800000 in
-- Separate the local send phases before applying the shared game continuation.
/-- For every material value, selected epoch, and input state, averaging
selected offline material in the `onlineFresh` stage gives exactly the
leaking B-send distribution in the `encapsFresh` stage. -/
theorem sendBrleak_sample_offline_eq_fresh [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    𝒟[(do
      let offline ← leak.encapsOffRleak
      (Sampling.schemeAt ecEk ecCt0 ecCt1 .onlineFresh { m with off := offline } e s).sendBrleak
        s.stB)] =
    𝒟[(Sampling.schemeAt ecEk ecCt0 ecCt1 .encapsFresh m e s).sendBrleak s.stB] := by
  have hf : Sampling.Stage.onlineFresh ≠ .fixed := by decide
  have he₀ : Sampling.Stage.encapsFresh ≠ .fixed := by decide
  have he₁ : Sampling.Stage.encapsFresh ≠ .onlineFresh := by decide
  apply evalDist_ext
  intro out
  by_cases he : s.stB.t = e <;> cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;>
    cases hc1 : s.stB.ct1 <;> cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
  all_goals
    simp only [Sampling.schemeAt, Sampling.Stage.pinsKeygen,
      Sampling.Stage.pinsOffline, Sampling.Stage.pinsOnline, scheme, sendBrleak,
      hc0, hp, hc1, hst, ha, pure_bind, Pinned.onOff, Pinned.leakage,
      Pinned.encapsOff, he, decide_true, decide_false,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, hf, he₀, he₁,
      or_true, or_false, Bool.and_true, Bool.false_and, ↓reduceIte]
  all_goals
    apply ToVCVio.probOutput_bind_of_const'
    intro offline _
    rfl

/-- For every material value, selected epoch, and input state, averaging
selected offline material in the `onlineFresh` stage gives exactly the
ordinary B-send distribution in the `encapsFresh` stage. Derived from
`sendBrleak_sample_offline_eq_fresh` by forgetting the coins. -/
theorem sendB_sample_offline_eq_fresh [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    𝒟[(do
      let offline ← leak.encapsOffRleak
      (Sampling.schemeAt ecEk ecCt0 ecCt1 .onlineFresh { m with off := offline } e s).sendB
        s.stB)] =
    𝒟[(Sampling.schemeAt ecEk ecCt0 ecCt1 .encapsFresh m e s).sendB s.stB] := by
  have h := evalDist_map_eq_of_evalDist_eq
    (sendBrleak_sample_offline_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e s)
    (fun out => out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))
  rw [map_bind] at h
  simpa only [scheme_sendB_eq_map_sendBrleak] using h

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- For every query, material value, selected epoch, mode, and input state,
averaging offline material in the `onlineFresh` stage gives the joint
response/state distribution of the `encapsFresh` stage. -/
theorem oracle_sample_offline_eq_fresh
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    𝒟[(do
      let offline ← leak.encapsOffRleak
      (Sampling.oracle base onoff ecEk ecCt0 ecCt1 leak
        .onlineFresh { m with off := offline } e b t).run s)] =
    𝒟[(Sampling.oracle base onoff ecEk ecCt0 ecCt1 leak .encapsFresh m e b t).run s] :=
  securityImplAt_sample_eq base onoff leak leak.encapsOffRleak
    (fun offline => Sampling.schemeAt ecEk ecCt0 ecCt1 .onlineFresh { m with off := offline } e)
    (Sampling.schemeAt ecEk ecCt0 ecCt1 .encapsFresh m e)
    (SCKAScheme.challOf (adjacentMode e b)) s
    (ToVCVio.evalDist_bind_of_const' _ fun _ _ => rfl)
    (sendB_sample_offline_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e s)
    (ToVCVio.evalDist_bind_of_const' _ fun _ _ => rfl)
    (sendBrleak_sample_offline_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e s)
    (fun offline _ ρ => (Sampling.recvA_eq_auxiliary base onoff ecEk ecCt0 ecCt1 leak
      .onlineFresh { m with off := offline } e s ρ).trans
      (Sampling.recvA_eq_auxiliary base onoff ecEk ecCt0 ecCt1 leak .encapsFresh m e s ρ).symm)
    (fun _ _ _ => rfl) t

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding.Sampling

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- For every material value `m`, selected epoch `e`, mode `b`, adversary `adv`, and state `s`,
sampling the selected offline output once before the stopped `onlineFresh` execution gives
the acceptance probability of the stopped `encapsFresh` stage. -/
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
      adv s] :=
  stoppedRun_sample_once_eq leak.encapsOffRleak
    (fun offline => oracle base onoff ecEk ecCt0 ecCt1 leak
      .onlineFresh { m with off := offline } e b)
    (oracle base onoff ecEk ecCt0 ecCt1 leak .encapsFresh m e b)
    (fun s => decide (e ∈ s.exposed))
    (fun _ => True) (fun s => sourceUsed .offline e s.stA s.stB) (usesSource .offline e)
    (fun _ _ _ _ _ _ _ _ => trivial)
    (fun offline _ t s _ hu z hz _ => oracle_preserves_sourceUsed base onoff ecEk ecCt0 ecCt1
      leak .onlineFresh { m with off := offline } e b .offline t s hu z hz)
    (fun t s _ hh offline _ offline' _ => oracle_offline_independent base onoff ecEk ecCt0
      ecCt1 leak m e b t s hh offline offline')
    (fun t s _ hu => usesSource_false_of_used .offline e t s hu)
    (fun offline _ t s _ hh z hz hcont => oracle_first_source_use base onoff ecEk ecCt0 ecCt1
      leak .onlineFresh { m with off := offline } e b .offline t s hh z hz hcont)
    (fun t s _ => oracle_sample_offline_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e b t s)
    adv s trivial

end oppUniKemCKA.Security.Embedding.Sampling
