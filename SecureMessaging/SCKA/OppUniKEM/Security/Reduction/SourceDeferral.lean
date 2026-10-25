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
- the pinned hybrid `stageStopped .pinned kemMat e b` (`HybridGame`), that is, the ideal game with
  challenge mode `adjacentMode e b` whose three samples at epoch `e` are those of `kemMat`, stopped
  at the first exposure of `e`, and the ideal game `idealSecurityImpl μ` with challenge mode `μ`
  (`Endpoints`).

**Main result** (step 3 of the proof structure in `OppUniKEM/Security`). For `e > 0`, each fixed
branch `fixedBranch adv e b` of `𝓑` (`Simulator`) has the acceptance probability of the ideal game
`idealSecurityImpl (adjacentMode e (!b))` stopped at the first exposure of `e`
(`fixedBranch_eq_ideal`).
-/

/-! ## Offline encapsulation -/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable [DecidableEq Sym]

/-- Unless B is at `e` without `ct0`, B's leaking send in
`stageScheme .onlineFresh { kemMat with off := off } e s` is the same computation for every `off`.
-/
theorem sendBrleak_offline_independent
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hh : ¬(s.stB.t = e ∧ s.stB.ct0.isNone))
    (offline offline' : (onoff.St × onoff.C₀) × leak.OffRand) :
    (stageScheme ecEk ecCt0 ecCt1 .onlineFresh { kemMat with off := offline } e s).sendBrleak
      s.stB =
    (stageScheme ecEk ecCt0 ecCt1 .onlineFresh { kemMat with off := offline' } e s).sendBrleak
      s.stB := by
  by_cases he : s.stB.t = e <;> cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;>
    cases hc1 : s.stB.ct1 <;> cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
  all_goals
    simp only [he, hc0, Option.isNone_none, Option.isNone_some, Bool.false_eq_true,
      and_true, and_false, not_true_eq_false] at hh
  all_goals
    simp only [stageScheme, Stage.keygenFlag, Stage.offlineFlag, Stage.onlineFlag,
      scheme, sendBrleak, hc0, hp, hc1, hst, ha, pure_bind,
      Pinned.onOff, Pinned.leakage, Pinned.encapsOff,
      he, decide_false,
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
    (stageScheme ecEk ecCt0 ecCt1 .onlineFresh { kemMat with off := offline } e s).sendB s.stB =
    (stageScheme ecEk ecCt0 ecCt1 .onlineFresh { kemMat with off := offline' } e s).sendB
      s.stB := by
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
    (SCKAScheme.oracleSendBrleak vulnRleakB
      (stageScheme ecEk ecCt0 ecCt1 stage kemMat e s) ()).run s =ᵈ
      (pure (none, s) : ProbComp _) := by
  apply SCKAScheme.oracleSendBrleak_rejected_evalDistEq _ _ s {e} ?_ ?_
  · intro key msg epoch next coins hout
    have hex := sendBrleak_exposure
      (stageKem stage kemMat e s) (stageOnOff stage kemMat e s) ecCt0 ecCt1
      (stageLeak stage kemMat e s) s.stB key msg epoch next coins hout
    simpa only [leakEpochsB, hfield, Option.isNone_none,
      Bool.true_or, ↓reduceIte, he] using hex
  · simp [hc]

variable [SampleableType K]

/-- If `usesSource .offline e t s = false`, the response/successor distribution of query `t` of
`stageOracle .onlineFresh { kemMat with off := off } e b` from `s` does not depend on `off`. -/
theorem stageOracle_offline_independent
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hh : usesSource .offline e t s = false)
    (offline offline' : (onoff.St × onoff.C₀) × leak.OffRand) :
    (stageOracle base onoff ecEk ecCt0 ecCt1 leak
      .onlineFresh { kemMat with off := offline } e b t).run s =ᵈ
    (stageOracle base onoff ecEk ecCt0 ecCt1 leak
      .onlineFresh { kemMat with off := offline' } e b t).run s := by
  rcases t with (((((t | u) | u) | _) | u) | u) <;> try rcases t with ((((n | u) | u) | n) | n)
  all_goals try cases u
  all_goals simp only [stageOracle, securityImplAt, StateT.run_bind, StateT.run_get, pure_bind,
    SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
    EvalDistEq.refl]
  · exact ToVCVio.evalDistEq_of_eq (SCKAScheme.oracleSendA_run_congr _ _ s rfl)
  · exact ToVCVio.evalDistEq_of_eq (SCKAScheme.oracleSendB_run_congr _ _ s
      (sendB_offline_independent base onoff ecEk ecCt0 ecCt1 leak kemMat e s
        (of_decide_eq_false hh) offline offline'))
  · exact ToVCVio.evalDistEq_of_eq (SCKAScheme.oracleRecvA_run_congr _ _ s (fun ρ =>
      (stageScheme_recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak .onlineFresh
        { kemMat with off := offline } e s ρ).trans
      (stageScheme_recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak .onlineFresh
        { kemMat with off := offline' } e s ρ).symm) n)
  · rfl
  · exact ToVCVio.evalDistEq_of_eq (SCKAScheme.oracleSendArleak_run_congr _ _ _ s rfl)
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
    · exact ToVCVio.evalDistEq_of_eq (SCKAScheme.oracleSendBrleak_run_congr _ _ _ s
        (sendBrleak_offline_independent base onoff ecEk ecCt0 ecCt1 leak kemMat e s hready
          offline offline'))

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- Averaging B's leaking send in `stageScheme .onlineFresh { kemMat with off := off } e s` over
`off` gives the output distribution of B's leaking send in `stageScheme .encapsFresh kemMat e s`. -/
theorem sendBrleak_sample_offline_eq_fresh [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    (do
      let offline ← leak.encapsOffRleak
      (stageScheme ecEk ecCt0 ecCt1 .onlineFresh
        { kemMat with off := offline } e s).sendBrleak s.stB) =ᵈ
    (stageScheme ecEk ecCt0 ecCt1 .encapsFresh kemMat e s).sendBrleak s.stB := by
  by_cases he : s.stB.t = e <;> cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;>
    cases hc1 : s.stB.ct1 <;> cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
  all_goals
    simp only [stageScheme, Stage.keygenFlag, Stage.offlineFlag, Stage.onlineFlag, scheme,
      sendBrleak, hc0, hp, hc1, hst, ha, pure_bind, Pinned.onOff, Pinned.leakage,
      Pinned.encapsOff, he, decide_true, decide_false,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, EvalDistEq.refl]
  all_goals
    exact ToVCVio.evalDistEq_bind_of_const' _ fun offline _ => rfl

/-- Ordinary-send version of `sendBrleak_sample_offline_eq_fresh`. -/
theorem sendB_sample_offline_eq_fresh [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    (do
      let offline ← leak.encapsOffRleak
      (stageScheme ecEk ecCt0 ecCt1 .onlineFresh { kemMat with off := offline } e s).sendB
        s.stB) =ᵈ
    (stageScheme ecEk ecCt0 ecCt1 .encapsFresh kemMat e s).sendB s.stB := by
  have h := EvalDistEq.map
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
`stageOracle .onlineFresh { kemMat with off := off } e b` over `off` gives the response/successor
distribution of query `t` of `stageOracle .encapsFresh kemMat e b`. -/
theorem stageOracle_sample_offline_eq_fresh
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    (do
      let offline ← leak.encapsOffRleak
      (stageOracle base onoff ecEk ecCt0 ecCt1 leak
        .onlineFresh { kemMat with off := offline } e b t).run s) =ᵈ
    (stageOracle base onoff ecEk ecCt0 ecCt1 leak .encapsFresh kemMat e b t).run s :=
  securityImplAt_sample_eq base onoff leak leak.encapsOffRleak
    (fun offline =>
      stageScheme ecEk ecCt0 ecCt1 .onlineFresh { kemMat with off := offline } e)
    (stageScheme ecEk ecCt0 ecCt1 .encapsFresh kemMat e)
    (SCKAScheme.challOf (adjacentMode e b)) s
    (ToVCVio.evalDistEq_bind_of_const' _ fun _ _ => rfl)
    (sendB_sample_offline_eq_fresh base onoff ecEk ecCt0 ecCt1 leak kemMat e s)
    (ToVCVio.evalDistEq_bind_of_const' _ fun _ _ => rfl)
    (sendBrleak_sample_offline_eq_fresh base onoff ecEk ecCt0 ecCt1 leak kemMat e s)
    (fun offline _ ρ => (stageScheme_recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak
      .onlineFresh { kemMat with off := offline } e s ρ).trans
      (stageScheme_recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak .encapsFresh kemMat e s ρ).symm)
    (fun _ _ _ => rfl) t

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- From every state, drawing `off ← leak.encapsOffRleak` once before
`stageStopped .onlineFresh { kemMat with off := off } e b` gives the acceptance probability of
`stageStopped .encapsFresh kemMat e b`. -/
theorem stageStopped_offline_deferred
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool) (adv : SecurityAdversary leak Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    Pr{let x ← (do
      let offline ← leak.encapsOffRleak
      optionRun (stageStopped base onoff ecEk ecCt0 ecCt1 leak
        .onlineFresh { kemMat with off := offline } e b) adv s)}[x = true] =
    Pr{let x ← (optionRun (stageStopped base onoff ecEk ecCt0 ecCt1 leak .encapsFresh kemMat e b)
      adv s)}[x = true] :=
  stoppedRun_sample_once_eq leak.encapsOffRleak
    (fun offline => stageOracle base onoff ecEk ecCt0 ecCt1 leak
      .onlineFresh { kemMat with off := offline } e b)
    (stageOracle base onoff ecEk ecCt0 ecCt1 leak .encapsFresh kemMat e b)
    (fun s => decide (e ∈ s.exposed))
    (fun _ => True) (fun s => sourceUsed .offline e s.stA s.stB) (usesSource .offline e)
    (fun _ _ _ _ _ _ _ _ => trivial)
    (fun offline _ t s _ hu z hz _ => stageOracle_preserves_sourceUsed base onoff ecEk ecCt0 ecCt1
      leak .onlineFresh { kemMat with off := offline } e b .offline t s hu z hz)
    (fun t s _ hh offline _ offline' _ => stageOracle_offline_independent base onoff ecEk ecCt0
      ecCt1 leak kemMat e b t s hh offline offline')
    (fun t s _ hu => usesSource_false_of_used .offline e t s hu)
    (fun offline _ t s _ hh z hz hcont => stageOracle_first_source_use base onoff ecEk ecCt0 ecCt1
      leak .onlineFresh { kemMat with off := offline } e b .offline t s hh z hz hcont)
    (fun t s _ => stageOracle_sample_offline_eq_fresh base onoff ecEk ecCt0 ecCt1 leak kemMat e b t
      s)
    adv s trivial

end oppUniKemCKA.Security.Embedding

/-! ## Key generation -/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- Averaging A's leaking send in `stageScheme .encapsFresh { kemMat with keygen := kg } e s` over
`kg` gives the output distribution of A's leaking send in `stageScheme .fresh kemMat e s`. -/
theorem sendArleak_sample_keygen_eq_fresh [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    (do
      let pair ← leak.keygenRleak
      (stageScheme ecEk ecCt0 ecCt1 .encapsFresh { kemMat with keygen := pair } e s).sendArleak
        s.stA) =ᵈ
    (stageScheme ecEk ecCt0 ecCt1 .fresh kemMat e s).sendArleak s.stA := by
  by_cases he : s.stA.t = e <;> cases hd : s.stA.dkA <;>
    cases hp : s.stA.ekA <;> cases ha : s.stA.ack.ekRec
  all_goals
    simp only [stageScheme, Stage.keygenFlag, scheme, sendArleak, Pinned.leakage,
      hd, hp, ha, he, decide_true, decide_false,
      Bool.false_eq_true, ↓reduceIte, pure_bind, EvalDistEq.refl]
  all_goals
    exact ToVCVio.evalDistEq_bind_of_const' _ fun pair _ => rfl

/-- Ordinary-send version of `sendArleak_sample_keygen_eq_fresh`. -/
theorem sendA_sample_keygen_eq_fresh [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    (do
      let pair ← leak.keygenRleak
      (stageScheme ecEk ecCt0 ecCt1 .encapsFresh { kemMat with keygen := pair } e s).sendA s.stA) =ᵈ
    (stageScheme ecEk ecCt0 ecCt1 .fresh kemMat e s).sendA s.stA := by
  have h := EvalDistEq.map
    (sendArleak_sample_keygen_eq_fresh base onoff ecEk ecCt0 ecCt1 leak kemMat e s)
    (fun out => out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))
  rw [map_bind] at h
  simpa only [scheme_sendA_eq_map_sendArleak] using h

/-- For every `kg`, B's leaking send in `stageScheme .encapsFresh { kemMat with keygen := kg } e s`
is that of `stageScheme .fresh kemMat e s`. -/
theorem sendBrleak_encapsFresh_eq_fresh [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (pair : (PK × SK) × leak.KeygenRand) :
    (stageScheme ecEk ecCt0 ecCt1 .encapsFresh { kemMat with keygen := pair } e s).sendBrleak
      s.stB =
    (stageScheme ecEk ecCt0 ecCt1 .fresh kemMat e s).sendBrleak s.stB := by
  cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;> cases hc1 : s.stB.ct1 <;>
    cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
  all_goals
    simp only [stageScheme, scheme, sendBrleak, hc0, hp, hc1, hst, ha, pure_bind,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    all_goals rfl

/-- Ordinary-send version of `sendBrleak_encapsFresh_eq_fresh`. -/
theorem sendB_encapsFresh_eq_fresh [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (pair : (PK × SK) × leak.KeygenRand) :
    (stageScheme ecEk ecCt0 ecCt1 .encapsFresh { kemMat with keygen := pair } e s).sendB s.stB =
    (stageScheme ecEk ecCt0 ecCt1 .fresh kemMat e s).sendB s.stB := by
  rw [scheme_sendB_eq_map_sendBrleak, scheme_sendB_eq_map_sendBrleak,
    sendBrleak_encapsFresh_eq_fresh base onoff ecEk ecCt0 ecCt1 leak kemMat e s pair]

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Key-generation version of `stageOracle_sample_offline_eq_fresh`, from stage `encapsFresh` to
stage `fresh`. -/
theorem stageOracle_sample_keygen_eq_fresh
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    (do
      let pair ← leak.keygenRleak
      (stageOracle base onoff ecEk ecCt0 ecCt1 leak .encapsFresh
        { kemMat with keygen := pair } e b t).run s) =ᵈ
    (stageOracle base onoff ecEk ecCt0 ecCt1 leak .fresh kemMat e b t).run s :=
  securityImplAt_sample_eq base onoff leak leak.keygenRleak
    (fun pair => stageScheme ecEk ecCt0 ecCt1 .encapsFresh { kemMat with keygen := pair } e)
    (stageScheme ecEk ecCt0 ecCt1 .fresh kemMat e) (SCKAScheme.challOf (adjacentMode e b)) s
    (sendA_sample_keygen_eq_fresh base onoff ecEk ecCt0 ecCt1 leak kemMat e s)
    (ToVCVio.evalDistEq_bind_of_const' _ fun pair _ =>
      sendB_encapsFresh_eq_fresh base onoff ecEk ecCt0 ecCt1 leak kemMat e s pair)
    (sendArleak_sample_keygen_eq_fresh base onoff ecEk ecCt0 ecCt1 leak kemMat e s)
    (ToVCVio.evalDistEq_bind_of_const' _ fun pair _ =>
      sendBrleak_encapsFresh_eq_fresh base onoff ecEk ecCt0 ecCt1 leak kemMat e s pair)
    (fun pair _ ρ => (stageScheme_recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak .encapsFresh
      { kemMat with keygen := pair } e s ρ).trans
      (stageScheme_recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak .fresh kemMat e s ρ).symm)
    (fun _ _ _ => rfl) t

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable [DecidableEq Sym]

/-- Unless A is at `e` without `dkA`, A's ordinary send in
`stageScheme .encapsFresh { kemMat with keygen := kg } e s` is the same computation for every `kg`.
-/
theorem sendA_keygen_independent
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hh : ¬(s.stA.t = e ∧ s.stA.dkA.isNone))
    (pair pair' : (PK × SK) × leak.KeygenRand) :
    (stageScheme ecEk ecCt0 ecCt1 .encapsFresh { kemMat with keygen := pair } e s).sendA s.stA =
    (stageScheme ecEk ecCt0 ecCt1 .encapsFresh { kemMat with keygen := pair' } e s).sendA
      s.stA := by
  by_cases he : s.stA.t = e <;> cases hd : s.stA.dkA <;>
    cases hp : s.stA.ekA <;> cases ha : s.stA.ack.ekRec
  all_goals
    simp only [he, hd, Option.isNone_none, Option.isNone_some, Bool.false_eq_true,
      and_true, and_false, not_true_eq_false] at hh
  all_goals
    simp only [stageScheme, Stage.keygenFlag, scheme, sendA, Pinned.kem, Pinned.leakage,
      Pinned.keygen, hd, hp, ha, he, decide_false,
      Bool.false_eq_true, ↓reduceIte, pure_bind]

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
    (stageScheme ecEk ecCt0 ecCt1 .encapsFresh { kemMat with keygen := pair } e s).sendArleak
      s.stA =
    (stageScheme ecEk ecCt0 ecCt1 .encapsFresh { kemMat with keygen := pair' } e s).sendArleak
      s.stA := by
  by_cases he : s.stA.t = e <;> cases hd : s.stA.dkA <;>
    cases hp : s.stA.ekA <;> cases ha : s.stA.ack.ekRec
  all_goals
    simp only [he, hd, Option.isNone_none, Option.isNone_some, Bool.false_eq_true,
      and_true, and_false, not_true_eq_false] at hh
  all_goals
    simp only [stageScheme, Stage.keygenFlag, scheme, sendArleak, Pinned.kem, Pinned.leakage,
      Pinned.keygen, hd, hp, ha, he, decide_false,
      Bool.false_eq_true, ↓reduceIte, pure_bind]

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
    (SCKAScheme.oracleSendArleak vulnRleakA
      (stageScheme ecEk ecCt0 ecCt1 stage kemMat e s) ()).run s =ᵈ
    (pure (none, s) : ProbComp _) := by
  apply SCKAScheme.oracleSendArleak_rejected_evalDistEq _ _ s {e} ?_ ?_
  · intro key msg epoch next coins hout
    have hex := sendArleak_exposure
      (stageKem stage kemMat e s) (stageOnOff stage kemMat e s) ecEk (stageLeak stage kemMat e s)
      s.stA key msg epoch next coins hout
    simpa only [leakEpochsA, hfield, Option.isNone_none, ↓reduceIte, he] using hex
  · simp [hc]

variable [SampleableType K]

/-- Key-generation version of `stageOracle_offline_independent`, for
`stageOracle .encapsFresh { kemMat with keygen := kg } e b`. -/
theorem stageOracle_keygen_independent
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hh : usesSource .keygen e t s = false)
    (pair pair' : (PK × SK) × leak.KeygenRand) :
    (stageOracle base onoff ecEk ecCt0 ecCt1 leak
      .encapsFresh { kemMat with keygen := pair } e b t).run s =ᵈ
    (stageOracle base onoff ecEk ecCt0 ecCt1 leak
      .encapsFresh { kemMat with keygen := pair' } e b t).run s := by
  rcases t with (((((t | u) | u) | _) | u) | u) <;> try rcases t with ((((n | u) | u) | n) | n)
  all_goals try cases u
  all_goals simp only [stageOracle, securityImplAt, StateT.run_bind, StateT.run_get, pure_bind,
    SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
    EvalDistEq.refl]
  · exact ToVCVio.evalDistEq_of_eq (SCKAScheme.oracleSendA_run_congr _ _ s
      (sendA_keygen_independent base onoff ecEk ecCt0 ecCt1 leak kemMat e s
        (of_decide_eq_false hh) pair pair'))
  · exact ToVCVio.evalDistEq_of_eq (SCKAScheme.oracleSendB_run_congr _ _ s
      ((sendB_encapsFresh_eq_fresh base onoff ecEk ecCt0 ecCt1 leak kemMat e s pair).trans
        (sendB_encapsFresh_eq_fresh base onoff ecEk ecCt0 ecCt1 leak kemMat e s pair').symm))
  · exact ToVCVio.evalDistEq_of_eq (SCKAScheme.oracleRecvA_run_congr _ _ s (fun ρ =>
      (stageScheme_recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak .encapsFresh
        { kemMat with keygen := pair } e s ρ).trans
      (stageScheme_recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak .encapsFresh
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
    · exact ToVCVio.evalDistEq_of_eq (SCKAScheme.oracleSendArleak_run_congr _ _ _ s
        (sendArleak_keygen_independent base onoff ecEk ecCt0 ecCt1 leak kemMat e s hready
          pair pair'))
  · exact ToVCVio.evalDistEq_of_eq (SCKAScheme.oracleSendBrleak_run_congr _ _ _ s
      ((sendBrleak_encapsFresh_eq_fresh base onoff ecEk ecCt0 ecCt1 leak kemMat e s pair).trans
        (sendBrleak_encapsFresh_eq_fresh base onoff ecEk ecCt0 ecCt1 leak kemMat e s pair').symm))

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Key-generation version of `stageStopped_offline_deferred`: drawing `kg ← leak.keygenRleak` once
before `stageStopped .encapsFresh { kemMat with keygen := kg } e b` gives the acceptance probability
of `stageStopped .fresh kemMat e b`. -/
theorem stageStopped_keygen_deferred
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool) (adv : SecurityAdversary leak Sym)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    Pr{let x ← (do
      let keygen ← leak.keygenRleak
      optionRun (stageStopped base onoff ecEk ecCt0 ecCt1 leak
        .encapsFresh { kemMat with keygen := keygen } e b) adv s)}[x = true] =
    Pr{let x ← (optionRun (stageStopped base onoff ecEk ecCt0 ecCt1 leak .fresh kemMat e b)
      adv s)}[x = true] :=
  stoppedRun_sample_once_eq leak.keygenRleak
    (fun keygen => stageOracle base onoff ecEk ecCt0 ecCt1 leak
      .encapsFresh { kemMat with keygen := keygen } e b)
    (stageOracle base onoff ecEk ecCt0 ecCt1 leak .fresh kemMat e b) (fun s => decide (e ∈
      s.exposed))
    (fun _ => True) (fun s => sourceUsed .keygen e s.stA s.stB) (usesSource .keygen e)
    (fun _ _ _ _ _ _ _ _ => trivial)
    (fun keygen _ t s _ hu z hz _ => stageOracle_preserves_sourceUsed base onoff ecEk ecCt0 ecCt1
      leak .encapsFresh { kemMat with keygen := keygen } e b .keygen t s hu z hz)
    (fun t s _ hh keygen _ keygen' _ => stageOracle_keygen_independent base onoff ecEk ecCt0 ecCt1
      leak kemMat e b t s hh keygen keygen')
    (fun t s _ hu => usesSource_false_of_used .keygen e t s hu)
    (fun keygen _ t s _ hh z hz hcont => stageOracle_first_source_use base onoff ecEk ecCt0 ecCt1
      leak .encapsFresh { kemMat with keygen := keygen } e b .keygen t s hh z hz hcont)
    (fun t s _ => stageOracle_sample_keygen_eq_fresh base onoff ecEk ecCt0 ecCt1 leak kemMat e b t
      s)
    adv s trivial

end oppUniKemCKA.Security.Embedding

/-! ## The three deferrals combined -/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- Pre-sampling the KEM material `kemMat ← sampleMaterial leak` of
epoch `e` in `stageStopped .pinned kemMat e b` yields the same acceptance probability as
`stageStopped .fresh kemMat₀ e b`, which samples each phase on demand and is independent of the
dummy material `kemMat₀`:
`Pr[kemMat ← sampleMaterial leak; stageStopped .pinned kemMat e b = true] =
Pr[stopped .fresh kemMat₀ e b = true]`. -/
theorem pinnedHybrid_eq_fresh
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff)
    (kemMat₀ : KEMMaterial leak) (e : ℕ) (b : Bool) (adv : SecurityAdversary leak Sym) :
    Pr{let x ← (do
      let kemMat ← sampleMaterial leak
      optionRun (stageStopped base onoff ecEk ecCt0 ecCt1 leak .pinned kemMat e b) adv
        (oppUniKemCKA.Reduction.Internal.initialGame base onoff))}[x = true] =
    Pr{let x ← (optionRun
      (stageStopped base onoff ecEk ecCt0 ecCt1 leak .fresh kemMat₀ e b) adv
      (oppUniKemCKA.Reduction.Internal.initialGame base onoff))}[x = true] := by
  trans Pr{let x ← (do
    let kg ← leak.keygenRleak
    let off ← leak.encapsOffRleak
    optionRun (stageStopped base onoff ecEk ecCt0 ecCt1 leak
      .onlineFresh { kemMat₀ with keygen := kg, off := off } e b) adv
      (oppUniKemCKA.Reduction.Internal.initialGame base onoff))}[x = true]
  · simp only [sampleMaterial, bind_assoc, pure_bind]
    rw [map_bind, map_bind]
    refine OracleComp.prEvent_bind_congr_of_support _ _ _ fun kg hkg => ?_
    rw [map_bind, map_bind]
    refine OracleComp.prEvent_bind_congr_of_support _ _ _ fun off hoff => ?_
    obtain ⟨online, hon⟩ := OracleComp.support_nonempty (leak.encapsOnRleak off.1.1 kg.1.1)
    let kemMat : KEMMaterial leak := ⟨kg, off, online⟩
    have hm : kemMat ∈ support (sampleMaterial leak) := by
      simp only [sampleMaterial, mem_support_bind_iff, mem_support_pure_iff]
      exact ⟨kg, hkg, off, hoff, online, hon, rfl⟩
    exact stageStopped_online_deferred base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
      leak kemMat hm e b adv _
      (reachableInv_init base onoff ecEk ecCt0 ecCt1 ecEk.ec.nchunk_pos ecCt0.ec.nchunk_pos)
      (consistentMat_initial base onoff leak kemMat e)
  trans Pr{let x ← (do
    let kg ← leak.keygenRleak
    optionRun (stageStopped base onoff ecEk ecCt0 ecCt1 leak
      .encapsFresh { kemMat₀ with keygen := kg } e b) adv
      (oppUniKemCKA.Reduction.Internal.initialGame base onoff))}[x = true]
  · rw [map_bind, map_bind]
    refine OracleComp.prEvent_bind_congr_of_support _ _ _ fun kg _ => ?_
    exact stageStopped_offline_deferred base onoff ecEk ecCt0 ecCt1 leak
      { kemMat₀ with keygen := kg } e b adv _
  · exact stageStopped_keygen_deferred base onoff ecEk ecCt0 ecCt1 leak kemMat₀ e b adv _

/-- The pinned hybrid `kemMat ← sampleMaterial leak; stageStopped .pinned kemMat e b` has the same
acceptance probability as the ideal game `idealSecurityImpl (adjacentMode e b)` stopped at the
first exposure of `e`. -/
theorem pinnedHybrid_eq_ideal
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : base.OnOffRandLeak onoff) (e : ℕ) (b : Bool) (adv : SecurityAdversary leak Sym) :
    Pr{let x ← (do
      let kemMat ← sampleMaterial leak
      optionRun (stageStopped base onoff ecEk ecCt0 ecCt1 leak .pinned kemMat e b) adv
        (oppUniKemCKA.Reduction.Internal.initialGame base onoff))}[x = true] =
    Pr{let x ← (optionRun
      (stopOnState (idealSecurityImpl base onoff hDet ecEk ecCt0 ecCt1 leak (adjacentMode e b))
        (fun s => decide (e ∈ s.exposed))) adv
      (oppUniKemCKA.Reduction.Internal.initialGame base onoff))}[x = true] := by
  obtain ⟨kemMat₀, _⟩ := OracleComp.support_nonempty (sampleMaterial leak)
  rw [pinnedHybrid_eq_fresh base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1 leak kemMat₀ e b adv]
  unfold stageStopped
  rw [stageOracle_fresh_eq_ideal base onoff hDet ecEk ecCt0 ecCt1 leak kemMat₀ e b]

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
    Pr{let x ← fixedBranch base onoff ecEk ecCt0 ecCt1 leak adv e b}[x = true] =
    Pr{let x ← (optionRun
      (stopOnState (idealSecurityImpl base onoff hDet ecEk ecCt0 ecCt1 leak
        (adjacentMode e (!b))) (fun s => decide (e ∈ s.exposed))) adv
      (oppUniKemCKA.Reduction.Internal.initialGame base onoff))}[x = true] := by
  rw [fixedBranch_eq_pinnedHybrid base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
    leak adv e he b]
  exact pinnedHybrid_eq_ideal base onoff hDet ecEk hEk ecCt0 hCt0 ecCt1 hCt1
    leak e (!b) adv

end oppUniKemCKA.Security.Embedding
