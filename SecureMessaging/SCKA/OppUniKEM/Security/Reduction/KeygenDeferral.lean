/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.OfflineDeferral
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.SourceUse
import ToVCVio.OracleComp.QueryTracking.OneUseSampling

/-!
# Deferring the key-generation sample

**Setting.** Let `m` be complete material, `e` a selected epoch, and `b` a mode bit. The
material `{ m with keygen := kg }` replaces the key-generation output of `m` by `kg`, resampled
as `kg ← leak.keygenRleak`. The one-use conditions of `stoppedRun_sample_once_eq` take
`used := sourceUsed .keygen e` and `hit := usesSource .keygen e` (`SourceUse`) and hold in
every game state.

**Results.**

- `oracle_sample_keygen_eq_fresh`: for every query, averaging
  `oracle .encapsFresh { m with keygen := kg } e b` over `kg` gives the joint distribution of
  response and successor state of `oracle .fresh m e b`.
- `stopped_keygen_deferred`: drawing `kg` once before
  `stopped .encapsFresh { m with keygen := kg } e b` gives the acceptance probability of
  `stopped .fresh m e b`.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding.Sampling

variable {K PK SK C Sym : Type}

/-- For every state `s`, averaging A's leaking send in
`schemeAt .encapsFresh { m with keygen := kg } e s` over `kg ← leak.keygenRleak` gives the
output distribution of A's leaking send in `schemeAt .fresh m e s`. -/
theorem sendArleak_sample_keygen_eq_fresh [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    𝒟[(do
      let pair ← leak.keygenRleak
      (schemeAt ecEk ecCt0 ecCt1 .encapsFresh { m with keygen := pair } e s).sendArleak s.stA)] =
    𝒟[(schemeAt ecEk ecCt0 ecCt1 .fresh m e s).sendArleak s.stA] := by
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

/-- The ordinary-send version of `sendArleak_sample_keygen_eq_fresh`. -/
theorem sendA_sample_keygen_eq_fresh [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    𝒟[(do
      let pair ← leak.keygenRleak
      (schemeAt ecEk ecCt0 ecCt1 .encapsFresh { m with keygen := pair } e s).sendA s.stA)] =
    𝒟[(schemeAt ecEk ecCt0 ecCt1 .fresh m e s).sendA s.stA] := by
  have h := evalDist_map_eq_of_evalDist_eq
    (sendArleak_sample_keygen_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e s)
    (fun out => out.map fun (key, msg, epoch, state, _) => (key, msg, epoch, state))
  rw [map_bind] at h
  simpa only [scheme_sendA_eq_map_sendArleak] using h

/-- For every key-generation output `kg`, B's leaking send in
`schemeAt .encapsFresh { m with keygen := kg } e s` is that of `schemeAt .fresh m e s`. -/
theorem sendBrleak_encapsFresh_eq_fresh [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (pair : (PK × SK) × leak.KeygenRand) :
    (schemeAt ecEk ecCt0 ecCt1 .encapsFresh { m with keygen := pair } e s).sendBrleak s.stB =
    (schemeAt ecEk ecCt0 ecCt1 .fresh m e s).sendBrleak s.stB := by
  cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;> cases hc1 : s.stB.ct1 <;>
    cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
  all_goals
    simp only [schemeAt, scheme, sendBrleak, hc0, hp, hc1, hst, ha, pure_bind,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;> rfl

/-- The ordinary-send version of `sendBrleak_encapsFresh_eq_fresh`. -/
theorem sendB_encapsFresh_eq_fresh [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (pair : (PK × SK) × leak.KeygenRand) :
    (schemeAt ecEk ecCt0 ecCt1 .encapsFresh { m with keygen := pair } e s).sendB s.stB =
    (schemeAt ecEk ecCt0 ecCt1 .fresh m e s).sendB s.stB := by
  rw [scheme_sendB_eq_map_sendBrleak, scheme_sendB_eq_map_sendBrleak,
    sendBrleak_encapsFresh_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e s pair]

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- For every query `t` and state `s`, averaging query `t` of
`oracle .encapsFresh { m with keygen := kg } e b` from `s` over `kg ← leak.keygenRleak` gives
the joint distribution of response and successor state of query `t` of `oracle .fresh m e b`
from `s`. -/
theorem oracle_sample_keygen_eq_fresh
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    𝒟[(do
      let pair ← leak.keygenRleak
      (oracle base onoff ecEk ecCt0 ecCt1 leak .encapsFresh
        { m with keygen := pair } e b t).run s)] =
    𝒟[(oracle base onoff ecEk ecCt0 ecCt1 leak .fresh m e b t).run s] :=
  securityImplAt_sample_eq base onoff leak leak.keygenRleak
    (fun pair => schemeAt ecEk ecCt0 ecCt1 .encapsFresh { m with keygen := pair } e)
    (schemeAt ecEk ecCt0 ecCt1 .fresh m e) (SCKAScheme.challOf (adjacentMode e b)) s
    (sendA_sample_keygen_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e s)
    (ToVCVio.evalDist_bind_of_const' _ fun pair _ =>
      sendB_encapsFresh_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e s pair)
    (sendArleak_sample_keygen_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e s)
    (ToVCVio.evalDist_bind_of_const' _ fun pair _ =>
      sendBrleak_encapsFresh_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e s pair)
    (fun pair _ ρ => (recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak .encapsFresh
      { m with keygen := pair } e s ρ).trans
      (recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak .fresh m e s ρ).symm)
    (fun _ _ _ => rfl) t

end oppUniKemCKA.Security.Embedding.Sampling

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding.Sampling

variable {K PK SK C Sym : Type}
variable [DecidableEq Sym]

/-- Unless A is at `e` with no decapsulation key, A's ordinary send in
`schemeAt .encapsFresh { m with keygen := kg } e s` is the same computation for every
key-generation output `kg`. -/
theorem sendA_keygen_independent
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hh : ¬(s.stA.t = e ∧ s.stA.dkA.isNone))
    (pair pair' : (PK × SK) × leak.KeygenRand) :
    (schemeAt ecEk ecCt0 ecCt1 .encapsFresh { m with keygen := pair } e s).sendA s.stA =
    (schemeAt ecEk ecCt0 ecCt1 .encapsFresh { m with keygen := pair' } e s).sendA s.stA := by
  by_cases he : s.stA.t = e <;> cases hd : s.stA.dkA <;>
    cases hp : s.stA.ekA <;> cases ha : s.stA.ack.ekRec
  all_goals
    simp only [he, hd, Option.isNone_none, Option.isNone_some, Bool.false_eq_true,
      and_true, and_false, not_true_eq_false] at hh
  all_goals
    simp only [schemeAt, Stage.pinsKeygen, scheme, sendA, Pinned.kem, Pinned.leakage,
      Pinned.keygen, hd, hp, ha, he, decide_false,
      Bool.and_false, Bool.false_eq_true, ↓reduceIte, pure_bind]

/-- The leaking-send version of `sendA_keygen_independent`. -/
theorem sendArleak_keygen_independent
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hh : ¬(s.stA.t = e ∧ s.stA.dkA.isNone))
    (pair pair' : (PK × SK) × leak.KeygenRand) :
    (schemeAt ecEk ecCt0 ecCt1 .encapsFresh { m with keygen := pair } e s).sendArleak s.stA =
    (schemeAt ecEk ecCt0 ecCt1 .encapsFresh { m with keygen := pair' } e s).sendArleak s.stA := by
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

/-- The version of `leaking_offline_rejected` for A's leaking send with no decapsulation
key. -/
theorem leaking_keygen_rejected
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (stage : Stage) (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (he : s.stA.t = e) (hfield : s.stA.dkA = none) (hc : e ∈ s.challenged) :
    𝒟[(SCKAScheme.oracleSendArleak vulnRleakA
      (schemeAt ecEk ecCt0 ecCt1 stage m e s) ()).run s] =
    𝒟[(pure (none, s) : ProbComp _)] := by
  apply SCKAScheme.oracleSendArleak_rejected_evalDist _ _ s {e} ?_ ?_
  · intro key msg epoch next coins hout
    have hex := sendArleak_exposure
      (Pinned.kem m (stage.pinsKeygen && decide (s.stA.t = e))
        (stage.pinsOffline && decide (s.stB.t = e))
        false (s.keyB s.stA.t))
      (Pinned.onOff m _ _ _ _) ecEk (Pinned.leakage leak m _ _ _ _) s.stA
      key msg epoch next coins hout
    simpa only [leakEpochsA, hfield, Option.isNone_none, ↓reduceIte, he] using hex
  · simp [hc]

variable [SampleableType K]

/-- If `usesSource .keygen e t s = false`, the joint distribution of response and successor
state of query `t` of `oracle .encapsFresh { m with keygen := kg } e b` from `s` is the same
for every key-generation output `kg`. -/
theorem oracle_keygen_independent
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hh : usesSource .keygen e t s = false)
    (pair pair' : (PK × SK) × leak.KeygenRand) :
    𝒟[(oracle base onoff ecEk ecCt0 ecCt1 leak
      .encapsFresh { m with keygen := pair } e b t).run s] =
    𝒟[(oracle base onoff ecEk ecCt0 ecCt1 leak
      .encapsFresh { m with keygen := pair' } e b t).run s] := by
  rcases t with (((((t | u) | u) | _) | u) | u) <;> try rcases t with ((((n | u) | u) | n) | n)
  all_goals try cases u
  all_goals simp only [oracle, securityImplAt, StateT.run_bind, StateT.run_get, pure_bind,
    SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
  · exact congrArg evalDist (SCKAScheme.oracleSendA_run_congr _ _ s
      (sendA_keygen_independent base onoff ecEk ecCt0 ecCt1 leak m e s
        (of_decide_eq_false hh) pair pair'))
  · exact congrArg evalDist (SCKAScheme.oracleSendB_run_congr _ _ s
      ((sendB_encapsFresh_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e s pair).trans
        (sendB_encapsFresh_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e s pair').symm))
  · exact congrArg evalDist (SCKAScheme.oracleRecvA_run_congr _ _ s (fun ρ =>
      (recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak .encapsFresh
        { m with keygen := pair } e s ρ).trans
      (recvA_eq_ideal base onoff ecEk ecCt0 ecCt1 leak .encapsFresh
        { m with keygen := pair' } e s ρ).symm) n)
  · rfl
  · by_cases hready : s.stA.t = e ∧ s.stA.dkA.isNone
    · have hc : e ∈ s.challenged := by
        have hnot : ¬((s.stA.t = e ∧ s.stA.dkA.isNone) ∧ e ∉ s.challenged) :=
          of_decide_eq_false hh
        by_contra hc
        exact hnot ⟨hready, hc⟩
      exact (leaking_keygen_rejected base onoff ecEk ecCt0 ecCt1 leak .encapsFresh
        { m with keygen := pair } e s hready.1
        (Option.isNone_iff_eq_none.mp hready.2) hc).trans
        (leaking_keygen_rejected base onoff ecEk ecCt0 ecCt1 leak .encapsFresh
          { m with keygen := pair' } e s hready.1
          (Option.isNone_iff_eq_none.mp hready.2) hc).symm
    · exact congrArg evalDist (SCKAScheme.oracleSendArleak_run_congr _ _ _ s
        (sendArleak_keygen_independent base onoff ecEk ecCt0 ecCt1 leak m e s hready
          pair pair'))
  · exact congrArg evalDist (SCKAScheme.oracleSendBrleak_run_congr _ _ _ s
      ((sendBrleak_encapsFresh_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e s pair).trans
        (sendBrleak_encapsFresh_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e s pair').symm))

end oppUniKemCKA.Security.Embedding.Sampling

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding.Sampling

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- For every adversary `adv` and state `s`, drawing `kg ← leak.keygenRleak` once and running
`optionRun (stopped .encapsFresh { m with keygen := kg } e b) adv s` returns `true` with the
probability of `optionRun (stopped .fresh m e b) adv s`. -/
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
      adv s] :=
  stoppedRun_sample_once_eq leak.keygenRleak
    (fun keygen => oracle base onoff ecEk ecCt0 ecCt1 leak
      .encapsFresh { m with keygen := keygen } e b)
    (oracle base onoff ecEk ecCt0 ecCt1 leak .fresh m e b) (fun s => decide (e ∈ s.exposed))
    (fun _ => True) (fun s => sourceUsed .keygen e s.stA s.stB) (usesSource .keygen e)
    (fun _ _ _ _ _ _ _ _ => trivial)
    (fun keygen _ t s _ hu z hz _ => oracle_preserves_sourceUsed base onoff ecEk ecCt0 ecCt1
      leak .encapsFresh { m with keygen := keygen } e b .keygen t s hu z hz)
    (fun t s _ hh keygen _ keygen' _ => oracle_keygen_independent base onoff ecEk ecCt0 ecCt1
      leak m e b t s hh keygen keygen')
    (fun t s _ hu => usesSource_false_of_used .keygen e t s hu)
    (fun keygen _ t s _ hh z hz hcont => oracle_first_source_use base onoff ecEk ecCt0 ecCt1
      leak .encapsFresh { m with keygen := keygen } e b .keygen t s hh z hz hcont)
    (fun t s _ => oracle_sample_keygen_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e b t s)
    adv s trivial

end oppUniKemCKA.Security.Embedding.Sampling
