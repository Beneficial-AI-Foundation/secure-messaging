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

**Setting.** Let `m` be complete material, `e` a selected epoch, and `b` a mode bit. The
material `{ m with off := off }` replaces the offline output of `m` by `off`, resampled as
`off ← leak.encapsOffRleak`. The one-use conditions of `stoppedRun_sample_once_eq` take
`used := sourceUsed .offline e` and `hit := usesSource .offline e` (`SourceUse`) and hold in
every game state.

**Results.**

- `oracle_sample_offline_eq_fresh`: for every query, averaging
  `oracle .onlineFresh { m with off := off } e b` over `off` gives the joint distribution of
  response and successor state of `oracle .encapsFresh m e b`.
- `stopped_offline_deferred`: drawing `off` once before
  `stopped .onlineFresh { m with off := off } e b` gives the acceptance probability of
  `stopped .encapsFresh m e b`.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding.Sampling

variable {K PK SK C Sym : Type}
variable [DecidableEq Sym]

/-- Unless B is at `e` with no offline ciphertext, B's leaking send in
`schemeAt .onlineFresh { m with off := off } e s` is the same computation for every offline
output `off`. -/
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
  by_cases he : s.stB.t = e <;> cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;>
    cases hc1 : s.stB.ct1 <;> cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
  all_goals
    simp only [he, hc0, Option.isNone_none, Option.isNone_some, Bool.false_eq_true,
      and_true, and_false, not_true_eq_false] at hh
  all_goals
    simp only [schemeAt, Stage.pinsKeygen, Stage.pinsOffline,
      scheme, sendBrleak, hc0, hp, hc1, hst, ha, pure_bind,
      Pinned.onOff, Pinned.leakage, Pinned.encapsOff,
      he, decide_true, decide_false, Bool.true_and,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

/-- The ordinary-send version of `sendBrleak_offline_independent`. -/
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

/-- In every stage, if B is at `e` with no offline ciphertext and `e ∈ s.challenged`, B's
leaking-send oracle rejects from `s`: its distribution is that of `pure (none, s)`. The send
samples before its guard rejects, so only the distributions agree. -/
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
      (stageKem stage m e s) (stageOnOff stage m e s) ecCt0 ecCt1 (stageLeak stage m e s) s.stB
      key msg epoch next coins hout
    simpa only [leakEpochsB, hfield, Option.isNone_none,
      Bool.true_or, ↓reduceIte, he] using hex
  · simp [hc]

variable [SampleableType K]

/-- If `usesSource .offline e t s = false`, the joint distribution of response and successor
state of query `t` of `oracle .onlineFresh { m with off := off } e b` from `s` is the same for
every offline output `off`. -/
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
      (recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak .onlineFresh
        { m with off := offline } e s ρ).trans
      (recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak .onlineFresh
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

/-- For every state `s`, averaging B's leaking send in
`schemeAt .onlineFresh { m with off := off } e s` over `off ← leak.encapsOffRleak` gives the
output distribution of B's leaking send in `schemeAt .encapsFresh m e s`. -/
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
  have he₁ : Sampling.Stage.encapsFresh ≠ .onlineFresh := by decide
  apply evalDist_ext
  intro out
  by_cases he : s.stB.t = e <;> cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;>
    cases hc1 : s.stB.ct1 <;> cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
  all_goals
    simp only [Sampling.schemeAt, Sampling.Stage.pinsKeygen,
      Sampling.Stage.pinsOffline, scheme, sendBrleak,
      hc0, hp, hc1, hst, ha, pure_bind, Pinned.onOff, Pinned.leakage,
      Pinned.encapsOff, he, decide_true, decide_false,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, he₁,
      Bool.and_true, Bool.false_and, ↓reduceIte]
  all_goals
    apply ToVCVio.probOutput_bind_of_const'
    intro offline _
    rfl

/-- The ordinary-send version of `sendBrleak_sample_offline_eq_fresh`. -/
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

/-- For every query `t` and state `s`, averaging query `t` of
`oracle .onlineFresh { m with off := off } e b` from `s` over `off ← leak.encapsOffRleak` gives
the joint distribution of response and successor state of query `t` of
`oracle .encapsFresh m e b` from `s`. -/
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
    (fun offline _ ρ => (Sampling.recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak
      .onlineFresh { m with off := offline } e s ρ).trans
      (Sampling.recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak .encapsFresh m e s ρ).symm)
    (fun _ _ _ => rfl) t

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding.Sampling

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- For every adversary `adv` and state `s`, drawing `off ← leak.encapsOffRleak` once and
running `optionRun (stopped .onlineFresh { m with off := off } e b) adv s` returns `true` with
the probability of `optionRun (stopped .encapsFresh m e b) adv s`. -/
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
