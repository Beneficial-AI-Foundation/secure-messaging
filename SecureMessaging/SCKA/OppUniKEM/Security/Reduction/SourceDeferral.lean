/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.SourceUse
import ToVCVio.OracleComp.QueryTracking.OneUseSampling
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.OnlineDeferral

/-!
# Deferring the source samples

**Setting.** Throughout this module, we consider:

- a KEM material `kemMat` (`Simulator`) and the materials `{ kemMat with off := off }` and
  `{ kemMat with keygen := kg }`, that is, `kemMat` with its offline output resampled as
  `off ← leak.encapsOffRleak` and with its key-generation output resampled as
  `kg ← leak.keygenRleak`;
- the one-use test `hit := usesSource phase e` and the predicate `used := sourceUsed phase e`
  (`SourceUse`), which satisfy the one-use conditions in every state;
- the pinned hybrid `hybridStopped kemMat e b` (`HybridGame`), that is, the ideal game with
  challenge mode `adjacentMode e b` whose three samples at epoch `e` are those of `kemMat`, stopped
  at the first exposure of `e`, and the ideal game `idealSecurityImpl μ` with challenge mode `μ`
  (`Endpoints`).

**Main results.** For the stages of `HybridGame`:

- For every query, averaging `oracle .onlineFresh { kemMat with off := off } e b t` over `off` gives
  the response/successor distribution of `oracle .encapsFresh kemMat e b t`
  (`oracle_sample_offline_eq_fresh`).
- Drawing `off` once before `stopped .onlineFresh { kemMat with off := off } e b` gives the
  acceptance probability of `stopped .encapsFresh kemMat e b` (`stopped_offline_deferred`).
- The same identities for `kg`, from stage `encapsFresh` to stage `fresh`
  (`oracle_sample_keygen_eq_fresh`, `stopped_keygen_deferred`).

**Combined** (step 3 of the proof structure in `OppUniKEM/Security`):

- Averaged over `kemMat ← sampleMaterial leak`, `hybridStopped kemMat e b` has the acceptance
  probability of `idealSecurityImpl (adjacentMode e b)` stopped at the first exposure of `e`
  (`pinnedHybrid_eq_fresh`, `pinnedHybrid_eq_ideal`).
- For `e > 0`, `fixedBranch adv e b` has that of the mode `adjacentMode e (!b)`
  (`fixedBranch_eq_ideal`).
-/

/-! ## Offline encapsulation -/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding.Sampling

variable {K PK SK C Sym : Type}
variable [DecidableEq Sym]

/-- Unless B is at `e` without `ct0`, B's leaking send in
`schemeAt .onlineFresh { kemMat with off := off } e s` is the same computation for every `off`. -/
theorem sendBrleak_offline_independent
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hh : ¬(s.stB.t = e ∧ s.stB.ct0.isNone))
    (offline offline' : (onoff.St × onoff.C₀) × leak.OffRand) :
    (schemeAt ecEk ecCt0 ecCt1 .onlineFresh { kemMat with off := offline } e s).sendBrleak s.stB =
    (schemeAt ecEk ecCt0 ecCt1 .onlineFresh { kemMat with off := offline' } e s).sendBrleak
      s.stB := by
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

/-- Ordinary-send version of `sendBrleak_offline_independent`. -/
theorem sendB_offline_independent
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hh : ¬(s.stB.t = e ∧ s.stB.ct0.isNone))
    (offline offline' : (onoff.St × onoff.C₀) × leak.OffRand) :
    (schemeAt ecEk ecCt0 ecCt1 .onlineFresh { kemMat with off := offline } e s).sendB s.stB =
    (schemeAt ecEk ecCt0 ecCt1 .onlineFresh { kemMat with off := offline' } e s).sendB s.stB := by
  rw [scheme_sendB_eq_map_sendBrleak, scheme_sendB_eq_map_sendBrleak,
    sendBrleak_offline_independent base onoff ecEk ecCt0 ecCt1 leak kemMat e s hh offline offline']

variable [DecidableEq K]

/-- In every stage, if B is at `e` without `ct0` and `e ∈ s.challenged`, B's leaking-send
oracle from `s` has the distribution of `pure (none, s)`; it samples before rejecting. -/
theorem leaking_offline_rejected
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (he : s.stB.t = e) (hfield : s.stB.ct0 = none) (hc : e ∈ s.challenged) :
    𝒟[(SCKAScheme.oracleSendBrleak vulnRleakB
      (schemeAt ecEk ecCt0 ecCt1 stage kemMat e s) ()).run s] =
      𝒟[(pure (none, s) : ProbComp _)] := by
  apply SCKAScheme.oracleSendBrleak_rejected_evalDist _ _ s {e} ?_ ?_
  · intro key msg epoch next coins hout
    have hex := sendBrleak_exposure
      (stageKem stage kemMat e s) (stageOnOff stage kemMat e s) ecCt0 ecCt1
      (stageLeak stage kemMat e s) s.stB key msg epoch next coins hout
    simpa only [leakEpochsB, hfield, Option.isNone_none,
      Bool.true_or, ↓reduceIte, he] using hex
  · simp [hc]

variable [SampleableType K]

/-- If `usesSource .offline e t s = false`, the response/successor distribution of query `t` of
`oracle .onlineFresh { kemMat with off := off } e b` from `s` does not depend on `off`. -/
theorem oracle_offline_independent
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hh : usesSource .offline e t s = false)
    (offline offline' : (onoff.St × onoff.C₀) × leak.OffRand) :
    𝒟[(oracle base onoff ecEk ecCt0 ecCt1 leak
      .onlineFresh { kemMat with off := offline } e b t).run s] =
    𝒟[(oracle base onoff ecEk ecCt0 ecCt1 leak
      .onlineFresh { kemMat with off := offline' } e b t).run s] := by
  rcases t with (((((t | u) | u) | _) | u) | u) <;> try rcases t with ((((n | u) | u) | n) | n)
  all_goals try cases u
  all_goals simp only [oracle, securityImplAt, StateT.run_bind, StateT.run_get, pure_bind,
    SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
  · exact congrArg evalDist (SCKAScheme.oracleSendA_run_congr _ _ s rfl)
  · exact congrArg evalDist (SCKAScheme.oracleSendB_run_congr _ _ s
      (sendB_offline_independent base onoff ecEk ecCt0 ecCt1 leak kemMat e s
        (of_decide_eq_false hh) offline offline'))
  · exact congrArg evalDist (SCKAScheme.oracleRecvA_run_congr _ _ s (fun ρ =>
      (recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak .onlineFresh
        { kemMat with off := offline } e s ρ).trans
      (recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak .onlineFresh
        { kemMat with off := offline' } e s ρ).symm) n)
  · rfl
  · exact congrArg evalDist (SCKAScheme.oracleSendArleak_run_congr _ _ _ s rfl)
  · by_cases hready : s.stB.t = e ∧ s.stB.ct0.isNone
    · have hc : e ∈ s.challenged := by
        have hnot : ¬((s.stB.t = e ∧ s.stB.ct0.isNone) ∧ e ∉ s.challenged) :=
          of_decide_eq_false hh
        by_contra hc
        exact hnot ⟨hready, hc⟩
      exact (leaking_offline_rejected base onoff ecEk ecCt0 ecCt1 leak .onlineFresh
        { kemMat with off := offline } e s hready.1
        (Option.isNone_iff_eq_none.mp hready.2) hc).trans
        (leaking_offline_rejected base onoff ecEk ecCt0 ecCt1 leak .onlineFresh
          { kemMat with off := offline' } e s hready.1
          (Option.isNone_iff_eq_none.mp hready.2) hc).symm
    · exact congrArg evalDist (SCKAScheme.oracleSendBrleak_run_congr _ _ _ s
        (sendBrleak_offline_independent base onoff ecEk ecCt0 ecCt1 leak kemMat e s hready
          offline offline'))

end oppUniKemCKA.Security.Embedding.Sampling

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- Averaging B's leaking send in `schemeAt .onlineFresh { kemMat with off := off } e s` over `off`
gives the output distribution of B's leaking send in `schemeAt .encapsFresh kemMat e s`. -/
theorem sendBrleak_sample_offline_eq_fresh [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    𝒟[(do
      let offline ← leak.encapsOffRleak
      (Sampling.schemeAt ecEk ecCt0 ecCt1 .onlineFresh
        { kemMat with off := offline } e s).sendBrleak s.stB)] =
    𝒟[(Sampling.schemeAt ecEk ecCt0 ecCt1 .encapsFresh kemMat e s).sendBrleak s.stB] := by
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

/-- Ordinary-send version of `sendBrleak_sample_offline_eq_fresh`. -/
theorem sendB_sample_offline_eq_fresh [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    𝒟[(do
      let offline ← leak.encapsOffRleak
      (Sampling.schemeAt ecEk ecCt0 ecCt1 .onlineFresh { kemMat with off := offline } e s).sendB
        s.stB)] =
    𝒟[(Sampling.schemeAt ecEk ecCt0 ecCt1 .encapsFresh kemMat e s).sendB s.stB] := by
  have h := evalDist_map_eq_of_evalDist_eq
    (sendBrleak_sample_offline_eq_fresh base onoff ecEk ecCt0 ecCt1 leak kemMat e s)
    (fun out => out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))
  rw [map_bind] at h
  simpa only [scheme_sendB_eq_map_sendBrleak] using h

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- For every query `t` and state `s`, averaging query `t` of
`oracle .onlineFresh { kemMat with off := off } e b` over `off` gives the response/successor
distribution of query `t` of `oracle .encapsFresh kemMat e b`. -/
theorem oracle_sample_offline_eq_fresh
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    𝒟[(do
      let offline ← leak.encapsOffRleak
      (Sampling.oracle base onoff ecEk ecCt0 ecCt1 leak
        .onlineFresh { kemMat with off := offline } e b t).run s)] =
    𝒟[(Sampling.oracle base onoff ecEk ecCt0 ecCt1 leak .encapsFresh kemMat e b t).run s] :=
  securityImplAt_sample_eq base onoff leak leak.encapsOffRleak
    (fun offline =>
      Sampling.schemeAt ecEk ecCt0 ecCt1 .onlineFresh { kemMat with off := offline } e)
    (Sampling.schemeAt ecEk ecCt0 ecCt1 .encapsFresh kemMat e)
    (SCKAScheme.challOf (adjacentMode e b)) s
    (ToVCVio.evalDist_bind_of_const' _ fun _ _ => rfl)
    (sendB_sample_offline_eq_fresh base onoff ecEk ecCt0 ecCt1 leak kemMat e s)
    (ToVCVio.evalDist_bind_of_const' _ fun _ _ => rfl)
    (sendBrleak_sample_offline_eq_fresh base onoff ecEk ecCt0 ecCt1 leak kemMat e s)
    (fun offline _ ρ => (Sampling.recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak
      .onlineFresh { kemMat with off := offline } e s ρ).trans
      (Sampling.recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak .encapsFresh kemMat e s ρ).symm)
    (fun _ _ _ => rfl) t

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding.Sampling

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- From every state, drawing `off ← leak.encapsOffRleak` once before
`stopped .onlineFresh { kemMat with off := off } e b` gives the acceptance probability of
`stopped .encapsFresh kemMat e b`. -/
theorem stopped_offline_deferred
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool) (adv : SecurityAdversary leak Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    Pr[= true | do
      let offline ← leak.encapsOffRleak
      optionRun (stopped base onoff ecEk ecCt0 ecCt1 leak
        .onlineFresh { kemMat with off := offline } e b) adv s] =
    Pr[= true | optionRun (stopped base onoff ecEk ecCt0 ecCt1 leak .encapsFresh kemMat e b)
      adv s] :=
  stoppedRun_sample_once_eq leak.encapsOffRleak
    (fun offline => oracle base onoff ecEk ecCt0 ecCt1 leak
      .onlineFresh { kemMat with off := offline } e b)
    (oracle base onoff ecEk ecCt0 ecCt1 leak .encapsFresh kemMat e b)
    (fun s => decide (e ∈ s.exposed))
    (fun _ => True) (fun s => sourceUsed .offline e s.stA s.stB) (usesSource .offline e)
    (fun _ _ _ _ _ _ _ _ => trivial)
    (fun offline _ t s _ hu z hz _ => oracle_preserves_sourceUsed base onoff ecEk ecCt0 ecCt1
      leak .onlineFresh { kemMat with off := offline } e b .offline t s hu z hz)
    (fun t s _ hh offline _ offline' _ => oracle_offline_independent base onoff ecEk ecCt0
      ecCt1 leak kemMat e b t s hh offline offline')
    (fun t s _ hu => usesSource_false_of_used .offline e t s hu)
    (fun offline _ t s _ hh z hz hcont => oracle_first_source_use base onoff ecEk ecCt0 ecCt1
      leak .onlineFresh { kemMat with off := offline } e b .offline t s hh z hz hcont)
    (fun t s _ => oracle_sample_offline_eq_fresh base onoff ecEk ecCt0 ecCt1 leak kemMat e b t s)
    adv s trivial

end oppUniKemCKA.Security.Embedding.Sampling

/-! ## Key generation -/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding.Sampling

variable {K PK SK C Sym : Type}

/-- Averaging A's leaking send in `schemeAt .encapsFresh { kemMat with keygen := kg } e s` over `kg`
gives the output distribution of A's leaking send in `schemeAt .fresh kemMat e s`. -/
theorem sendArleak_sample_keygen_eq_fresh [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    𝒟[(do
      let pair ← leak.keygenRleak
      (schemeAt ecEk ecCt0 ecCt1 .encapsFresh { kemMat with keygen := pair } e s).sendArleak
        s.stA)] =
    𝒟[(schemeAt ecEk ecCt0 ecCt1 .fresh kemMat e s).sendArleak s.stA] := by
  have hf : Stage.encapsFresh ≠ .fresh := by decide
  apply evalDist_ext
  intro out
  by_cases he : s.stA.t = e <;> cases hd : s.stA.dkA <;>
    cases hp : s.stA.ekA <;> cases ha : s.stA.ack.ekRec
  all_goals
    simp only [schemeAt, Stage.pinsKeygen, scheme, sendArleak, Pinned.leakage,
      hd, hp, ha, he, hf, ne_eq, not_true_eq_false, not_false_eq_true,
      decide_true, decide_false, Bool.true_and, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte, pure_bind]
  all_goals
    apply ToVCVio.probOutput_bind_of_const'
    intro pair _
    rfl

/-- Ordinary-send version of `sendArleak_sample_keygen_eq_fresh`. -/
theorem sendA_sample_keygen_eq_fresh [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    𝒟[(do
      let pair ← leak.keygenRleak
      (schemeAt ecEk ecCt0 ecCt1 .encapsFresh { kemMat with keygen := pair } e s).sendA s.stA)] =
    𝒟[(schemeAt ecEk ecCt0 ecCt1 .fresh kemMat e s).sendA s.stA] := by
  have h := evalDist_map_eq_of_evalDist_eq
    (sendArleak_sample_keygen_eq_fresh base onoff ecEk ecCt0 ecCt1 leak kemMat e s)
    (fun out => out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))
  rw [map_bind] at h
  simpa only [scheme_sendA_eq_map_sendArleak] using h

/-- For every `kg`, B's leaking send in `schemeAt .encapsFresh { kemMat with keygen := kg } e s` is
that of `schemeAt .fresh kemMat e s`. -/
theorem sendBrleak_encapsFresh_eq_fresh [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (pair : (PK × SK) × leak.KeygenRand) :
    (schemeAt ecEk ecCt0 ecCt1 .encapsFresh { kemMat with keygen := pair } e s).sendBrleak s.stB =
    (schemeAt ecEk ecCt0 ecCt1 .fresh kemMat e s).sendBrleak s.stB := by
  cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;> cases hc1 : s.stB.ct1 <;>
    cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
  all_goals
    simp only [schemeAt, scheme, sendBrleak, hc0, hp, hc1, hst, ha, pure_bind,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;> rfl

/-- Ordinary-send version of `sendBrleak_encapsFresh_eq_fresh`. -/
theorem sendB_encapsFresh_eq_fresh [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (pair : (PK × SK) × leak.KeygenRand) :
    (schemeAt ecEk ecCt0 ecCt1 .encapsFresh { kemMat with keygen := pair } e s).sendB s.stB =
    (schemeAt ecEk ecCt0 ecCt1 .fresh kemMat e s).sendB s.stB := by
  rw [scheme_sendB_eq_map_sendBrleak, scheme_sendB_eq_map_sendBrleak,
    sendBrleak_encapsFresh_eq_fresh base onoff ecEk ecCt0 ecCt1 leak kemMat e s pair]

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Key-generation version of `oracle_sample_offline_eq_fresh`, from stage `encapsFresh` to
stage `fresh`. -/
theorem oracle_sample_keygen_eq_fresh
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    𝒟[(do
      let pair ← leak.keygenRleak
      (oracle base onoff ecEk ecCt0 ecCt1 leak .encapsFresh
        { kemMat with keygen := pair } e b t).run s)] =
    𝒟[(oracle base onoff ecEk ecCt0 ecCt1 leak .fresh kemMat e b t).run s] :=
  securityImplAt_sample_eq base onoff leak leak.keygenRleak
    (fun pair => schemeAt ecEk ecCt0 ecCt1 .encapsFresh { kemMat with keygen := pair } e)
    (schemeAt ecEk ecCt0 ecCt1 .fresh kemMat e) (SCKAScheme.challOf (adjacentMode e b)) s
    (sendA_sample_keygen_eq_fresh base onoff ecEk ecCt0 ecCt1 leak kemMat e s)
    (ToVCVio.evalDist_bind_of_const' _ fun pair _ =>
      sendB_encapsFresh_eq_fresh base onoff ecEk ecCt0 ecCt1 leak kemMat e s pair)
    (sendArleak_sample_keygen_eq_fresh base onoff ecEk ecCt0 ecCt1 leak kemMat e s)
    (ToVCVio.evalDist_bind_of_const' _ fun pair _ =>
      sendBrleak_encapsFresh_eq_fresh base onoff ecEk ecCt0 ecCt1 leak kemMat e s pair)
    (fun pair _ ρ => (recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak .encapsFresh
      { kemMat with keygen := pair } e s ρ).trans
      (recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak .fresh kemMat e s ρ).symm)
    (fun _ _ _ => rfl) t

end oppUniKemCKA.Security.Embedding.Sampling

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding.Sampling

variable {K PK SK C Sym : Type}
variable [DecidableEq Sym]

/-- Unless A is at `e` without `dkA`, A's ordinary send in
`schemeAt .encapsFresh { kemMat with keygen := kg } e s` is the same computation for every `kg`. -/
theorem sendA_keygen_independent
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hh : ¬(s.stA.t = e ∧ s.stA.dkA.isNone))
    (pair pair' : (PK × SK) × leak.KeygenRand) :
    (schemeAt ecEk ecCt0 ecCt1 .encapsFresh { kemMat with keygen := pair } e s).sendA s.stA =
    (schemeAt ecEk ecCt0 ecCt1 .encapsFresh { kemMat with keygen := pair' } e s).sendA s.stA := by
  by_cases he : s.stA.t = e <;> cases hd : s.stA.dkA <;>
    cases hp : s.stA.ekA <;> cases ha : s.stA.ack.ekRec
  all_goals
    simp only [he, hd, Option.isNone_none, Option.isNone_some, Bool.false_eq_true,
      and_true, and_false, not_true_eq_false] at hh
  all_goals
    simp only [schemeAt, Stage.pinsKeygen, scheme, sendA, Pinned.kem, Pinned.leakage,
      Pinned.keygen, hd, hp, ha, he, decide_false,
      Bool.and_false, Bool.false_eq_true, ↓reduceIte, pure_bind]

/-- Leaking-send version of `sendA_keygen_independent`. -/
theorem sendArleak_keygen_independent
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hh : ¬(s.stA.t = e ∧ s.stA.dkA.isNone))
    (pair pair' : (PK × SK) × leak.KeygenRand) :
    (schemeAt ecEk ecCt0 ecCt1 .encapsFresh { kemMat with keygen := pair } e s).sendArleak s.stA =
    (schemeAt ecEk ecCt0 ecCt1 .encapsFresh { kemMat with keygen := pair' } e s).sendArleak
      s.stA := by
  by_cases he : s.stA.t = e <;> cases hd : s.stA.dkA <;>
    cases hp : s.stA.ekA <;> cases ha : s.stA.ack.ekRec
  all_goals
    simp only [he, hd, Option.isNone_none, Option.isNone_some, Bool.false_eq_true,
      and_true, and_false, not_true_eq_false] at hh
  all_goals
    simp only [schemeAt, Stage.pinsKeygen, scheme, sendArleak, Pinned.kem, Pinned.leakage,
      Pinned.keygen, hd, hp, ha, he, decide_false,
      Bool.and_false, Bool.false_eq_true, ↓reduceIte, pure_bind]

variable [DecidableEq K]

/-- A version of `leaking_offline_rejected`, for A without `dkA`. -/
theorem leaking_keygen_rejected
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (he : s.stA.t = e) (hfield : s.stA.dkA = none) (hc : e ∈ s.challenged) :
    𝒟[(SCKAScheme.oracleSendArleak vulnRleakA
      (schemeAt ecEk ecCt0 ecCt1 stage kemMat e s) ()).run s] =
    𝒟[(pure (none, s) : ProbComp _)] := by
  apply SCKAScheme.oracleSendArleak_rejected_evalDist _ _ s {e} ?_ ?_
  · intro key msg epoch next coins hout
    have hex := sendArleak_exposure
      (stageKem stage kemMat e s) (stageOnOff stage kemMat e s) ecEk (stageLeak stage kemMat e s)
      s.stA key msg epoch next coins hout
    simpa only [leakEpochsA, hfield, Option.isNone_none, ↓reduceIte, he] using hex
  · simp [hc]

variable [SampleableType K]

/-- Key-generation version of `oracle_offline_independent`, for
`oracle .encapsFresh { kemMat with keygen := kg } e b`. -/
theorem oracle_keygen_independent
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hh : usesSource .keygen e t s = false)
    (pair pair' : (PK × SK) × leak.KeygenRand) :
    𝒟[(oracle base onoff ecEk ecCt0 ecCt1 leak
      .encapsFresh { kemMat with keygen := pair } e b t).run s] =
    𝒟[(oracle base onoff ecEk ecCt0 ecCt1 leak
      .encapsFresh { kemMat with keygen := pair' } e b t).run s] := by
  rcases t with (((((t | u) | u) | _) | u) | u) <;> try rcases t with ((((n | u) | u) | n) | n)
  all_goals try cases u
  all_goals simp only [oracle, securityImplAt, StateT.run_bind, StateT.run_get, pure_bind,
    SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
  · exact congrArg evalDist (SCKAScheme.oracleSendA_run_congr _ _ s
      (sendA_keygen_independent base onoff ecEk ecCt0 ecCt1 leak kemMat e s
        (of_decide_eq_false hh) pair pair'))
  · exact congrArg evalDist (SCKAScheme.oracleSendB_run_congr _ _ s
      ((sendB_encapsFresh_eq_fresh base onoff ecEk ecCt0 ecCt1 leak kemMat e s pair).trans
        (sendB_encapsFresh_eq_fresh base onoff ecEk ecCt0 ecCt1 leak kemMat e s pair').symm))
  · exact congrArg evalDist (SCKAScheme.oracleRecvA_run_congr _ _ s (fun ρ =>
      (recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak .encapsFresh
        { kemMat with keygen := pair } e s ρ).trans
      (recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak .encapsFresh
        { kemMat with keygen := pair' } e s ρ).symm) n)
  · rfl
  · by_cases hready : s.stA.t = e ∧ s.stA.dkA.isNone
    · have hc : e ∈ s.challenged := by
        have hnot : ¬((s.stA.t = e ∧ s.stA.dkA.isNone) ∧ e ∉ s.challenged) :=
          of_decide_eq_false hh
        by_contra hc
        exact hnot ⟨hready, hc⟩
      exact (leaking_keygen_rejected base onoff ecEk ecCt0 ecCt1 leak .encapsFresh
        { kemMat with keygen := pair } e s hready.1
        (Option.isNone_iff_eq_none.mp hready.2) hc).trans
        (leaking_keygen_rejected base onoff ecEk ecCt0 ecCt1 leak .encapsFresh
          { kemMat with keygen := pair' } e s hready.1
          (Option.isNone_iff_eq_none.mp hready.2) hc).symm
    · exact congrArg evalDist (SCKAScheme.oracleSendArleak_run_congr _ _ _ s
        (sendArleak_keygen_independent base onoff ecEk ecCt0 ecCt1 leak kemMat e s hready
          pair pair'))
  · exact congrArg evalDist (SCKAScheme.oracleSendBrleak_run_congr _ _ _ s
      ((sendBrleak_encapsFresh_eq_fresh base onoff ecEk ecCt0 ecCt1 leak kemMat e s pair).trans
        (sendBrleak_encapsFresh_eq_fresh base onoff ecEk ecCt0 ecCt1 leak kemMat e s pair').symm))

end oppUniKemCKA.Security.Embedding.Sampling

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding.Sampling

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Key-generation version of `stopped_offline_deferred`: drawing `kg ← leak.keygenRleak` once
before `stopped .encapsFresh { kemMat with keygen := kg } e b` gives the acceptance probability of
`stopped .fresh kemMat e b`. -/
theorem stopped_keygen_deferred
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool) (adv : SecurityAdversary leak Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    Pr[= true | do
      let keygen ← leak.keygenRleak
      optionRun (stopped base onoff ecEk ecCt0 ecCt1 leak
        .encapsFresh { kemMat with keygen := keygen } e b) adv s] =
    Pr[= true | optionRun (stopped base onoff ecEk ecCt0 ecCt1 leak .fresh kemMat e b)
      adv s] :=
  stoppedRun_sample_once_eq leak.keygenRleak
    (fun keygen => oracle base onoff ecEk ecCt0 ecCt1 leak
      .encapsFresh { kemMat with keygen := keygen } e b)
    (oracle base onoff ecEk ecCt0 ecCt1 leak .fresh kemMat e b) (fun s => decide (e ∈ s.exposed))
    (fun _ => True) (fun s => sourceUsed .keygen e s.stA s.stB) (usesSource .keygen e)
    (fun _ _ _ _ _ _ _ _ => trivial)
    (fun keygen _ t s _ hu z hz _ => oracle_preserves_sourceUsed base onoff ecEk ecCt0 ecCt1
      leak .encapsFresh { kemMat with keygen := keygen } e b .keygen t s hu z hz)
    (fun t s _ hh keygen _ keygen' _ => oracle_keygen_independent base onoff ecEk ecCt0 ecCt1
      leak kemMat e b t s hh keygen keygen')
    (fun t s _ hu => usesSource_false_of_used .keygen e t s hu)
    (fun keygen _ t s _ hh z hz hcont => oracle_first_source_use base onoff ecEk ecCt0 ecCt1
      leak .encapsFresh { kemMat with keygen := keygen } e b .keygen t s hh z hz hcont)
    (fun t s _ => oracle_sample_keygen_eq_fresh base onoff ecEk ecCt0 ecCt1 leak kemMat e b t s)
    adv s trivial

end oppUniKemCKA.Security.Embedding.Sampling

/-! ## The three deferrals combined -/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Pre-sampling the KEM material `kemMat ← sampleMaterial leak` of
epoch `e` in `hybridStopped kemMat e b` yields the same acceptance probability as
`stopped .fresh kemMat₀ e b`, which samples each phase on demand and is independent of the dummy
material `kemMat₀`:
`Pr[kemMat ← sampleMaterial leak; hybridStopped kemMat e b = true] =
Pr[stopped .fresh kemMat₀ e b = true]`. -/
theorem pinnedHybrid_eq_fresh
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff)
    (kemMat₀ : KEMMaterial leak) (e : ℕ) (b : Bool) (adv : SecurityAdversary leak Sym) :
    Pr[= true | do
      let kemMat ← sampleMaterial leak
      optionRun (hybridStopped base onoff ecEk ecCt0 ecCt1 leak kemMat e b) adv
        (oppUniKemCKA.Reduction.Internal.initialGame base onoff)] =
    Pr[= true | optionRun
      (Sampling.stopped base onoff ecEk ecCt0 ecCt1 leak .fresh kemMat₀ e b) adv
      (oppUniKemCKA.Reduction.Internal.initialGame base onoff)] := by
  trans Pr[= true | do
    let kg ← leak.keygenRleak
    let off ← leak.encapsOffRleak
    optionRun (Sampling.stopped base onoff ecEk ecCt0 ecCt1 leak
      .onlineFresh { kemMat₀ with keygen := kg, off := off } e b) adv
      (oppUniKemCKA.Reduction.Internal.initialGame base onoff)]
  · simp only [sampleMaterial, bind_assoc, pure_bind]
    apply probOutput_bind_congr
    intro kg hkg
    apply probOutput_bind_congr
    intro off hoff
    obtain ⟨online, hon⟩ : (support (leak.encapsOnRleak off.1.1 kg.1.1)).Nonempty := by
      simp [Set.nonempty_iff_ne_empty, ← probFailure_eq_one_iff]
    let kemMat : KEMMaterial leak := ⟨kg, off, online⟩
    have hm : kemMat ∈ support (sampleMaterial leak) := by
      simp only [sampleMaterial, mem_support_bind_iff, mem_support_pure_iff]
      exact ⟨kg, hkg, off, hoff, online, hon, rfl⟩
    exact hybridStopped_online_deferred base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
      leak kemMat hm e b adv _
      (reachableInv_init base onoff ecEk ecCt0 ecCt1 ecEk.ec.nchunk_pos ecCt0.ec.nchunk_pos)
      (pinnedSources_initial base onoff leak kemMat e)
  trans Pr[= true | do
    let kg ← leak.keygenRleak
    optionRun (Sampling.stopped base onoff ecEk ecCt0 ecCt1 leak
      .encapsFresh { kemMat₀ with keygen := kg } e b) adv
      (oppUniKemCKA.Reduction.Internal.initialGame base onoff)]
  · apply probOutput_bind_congr
    intro kg _
    exact Sampling.stopped_offline_deferred base onoff ecEk ecCt0 ecCt1 leak
      { kemMat₀ with keygen := kg } e b adv _
  · exact Sampling.stopped_keygen_deferred base onoff ecEk ecCt0 ecCt1 leak kemMat₀ e b adv _

/-- The pinned hybrid `kemMat ← sampleMaterial leak; hybridStopped kemMat e b` has the same
acceptance probability as the ideal game `idealSecurityImpl (adjacentMode e b)` stopped at the
first exposure of `e`. -/
theorem pinnedHybrid_eq_ideal
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff) (e : ℕ) (b : Bool) (adv : SecurityAdversary leak Sym) :
    Pr[= true | do
      let kemMat ← sampleMaterial leak
      optionRun (hybridStopped base onoff ecEk ecCt0 ecCt1 leak kemMat e b) adv
        (oppUniKemCKA.Reduction.Internal.initialGame base onoff)] =
    Pr[= true | optionRun
      (stopOnState (idealSecurityImpl base onoff hDet ecEk ecCt0 ecCt1 leak (adjacentMode e b))
        (fun s => decide (e ∈ s.exposed))) adv
      (oppUniKemCKA.Reduction.Internal.initialGame base onoff)] := by
  obtain ⟨kemMat₀, _⟩ : (support (sampleMaterial leak)).Nonempty := by
    simp [Set.nonempty_iff_ne_empty, ← probFailure_eq_one_iff]
  rw [pinnedHybrid_eq_fresh base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1 leak kemMat₀ e b adv]
  unfold Sampling.stopped
  rw [Sampling.oracle_fresh_eq_ideal base onoff hDet ecEk ecCt0 ecCt1 leak kemMat₀ e b]

/-- For `e > 0`, the reduction's fixed branch `fixedBranch adv e b` (`Simulator`) has the same
acceptance probability as the ideal game `idealSecurityImpl (adjacentMode e (!b))` stopped at the
first exposure of `e`. -/
theorem fixedBranch_eq_ideal
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff) (e : ℕ) (he : 0 < e)
    (b : Bool) (adv : SecurityAdversary leak Sym) :
    Pr[= true | fixedBranch base onoff ecEk ecCt0 ecCt1 leak adv e b] =
    Pr[= true | optionRun
      (stopOnState (idealSecurityImpl base onoff hDet ecEk ecCt0 ecCt1 leak
        (adjacentMode e (!b))) (fun s => decide (e ∈ s.exposed))) adv
      (oppUniKemCKA.Reduction.Internal.initialGame base onoff)] := by
  rw [fixedBranch_eq_pinnedHybrid base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
    leak adv e he b]
  exact pinnedHybrid_eq_ideal base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
    leak e (!b) adv

end oppUniKemCKA.Security.Embedding
