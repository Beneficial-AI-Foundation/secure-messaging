/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.SourceFirstUse
import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.KeygenOracle
import ToVCVio.OracleComp.QueryTracking.OneUseSampling

/-!
# Independence from unused selected key-generation material

For every query whose key-generation-use test is false, changing the
stored key pair and its coins in `encapsFresh` preserves the response/state
distribution. The first A-send at the selected epoch installs this material.
Later sends retain it; encapsulation samples freshly at the stored public
key. A leaking first send after a challenge rejects and retains its state.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding.Sampling

variable {K PK SK C Sym : Type}
variable [DecidableEq Sym]

/-- Outside the selected first A-send, replacing stored key-generation
material leaves the local sendA computation in `encapsFresh` unchanged. -/
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
    simp only [schemeAt, Stage.pinsKeygen, scheme, sendA, kem, leakage,
      Pinned.keygen, hd, hp, ha, he, decide_false,
      Bool.and_false, Bool.false_eq_true, ↓reduceIte, pure_bind]

/-- Outside the selected first A-send, replacing stored key-generation
material leaves the local sendArleak computation in `encapsFresh` unchanged. -/
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
    simp only [schemeAt, Stage.pinsKeygen, scheme, sendArleak, kem, leakage,
      Pinned.keygen, hd, hp, ha, he, decide_false,
      Bool.and_false, Bool.false_eq_true, ↓reduceIte, pure_bind]

variable [DecidableEq K]

/-- In every stage, a leaking first A-send at an already challenged epoch
has the rejection distribution concentrated at the original state. -/
theorem leaking_keygen_rejected
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (stage : Stage) (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (he : s.stA.t = e) (hfield : s.stA.dkA = none) (hc : e ∈ s.challenged) :
    𝒟[(SCKAScheme.oracleSendArleak sendExposureA
      (schemeAt ecEk ecCt0 ecCt1 stage m e s) ()).run s] =
    𝒟[(pure (none, s) : ProbComp _)] := by
  apply SCKAScheme.oracleSendArleak_rejected_evalDist _ _ s {e} ?_ ?_
  · intro key msg epoch next coins hout
    have hex := sendArleak_exposure
      (kem m (stage.pinsKeygen && decide (s.stA.t = e))
        (stage.pinsOffline && decide (s.stB.t = e))
        (stage.pinsOnline && decide (s.stB.t = e)) (s.keyB s.stA.t))
      (onOff m _ _ _ _) ecEk (leakage leak m _ _ _ _) s.stA _ hout
      key msg epoch next coins rfl
    simpa only [leakEpochsA, hfield, Option.isNone_none, ↓reduceIte, he] using hex
  · simp [hc]

variable [SampleableType K]

/-- For every query with `usesSource .keygen = false`, changing the stored
key-generation component in `encapsFresh` preserves the joint response/state
distribution, including the rejection of a challenged-epoch leaking send. -/
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
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n)
    · rfl
    · cases u
      have hno : ¬(s.stA.t = e ∧ s.stA.dkA.isNone) := of_decide_eq_false hh
      simp only [oracle, StateT.run_bind, StateT.run_get, pure_bind,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        SCKAScheme.oracleSendA]
      rw [sendA_keygen_independent base onoff ecEk ecCt0 ecCt1 leak m e s hno pair pair']
    · cases u
      simp only [oracle, StateT.run_bind, StateT.run_get, pure_bind,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        SCKAScheme.oracleSendB]
      rw [sendB_encapsFresh_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e s pair,
        sendB_encapsFresh_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e s pair']
    · simp only [oracle, StateT.run_bind, StateT.run_get, pure_bind,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        SCKAScheme.oracleRecvA]
      cases hm : s.msgB n with
      | none => rfl
      | some out =>
        rcases out with ⟨msg, epoch⟩
        simp only
        rw [recvA_eq_auxiliary base onoff ecEk ecCt0 ecCt1 leak .encapsFresh
          { m with keygen := pair } e s msg,
          recvA_eq_auxiliary base onoff ecEk ecCt0 ecCt1 leak .encapsFresh
            { m with keygen := pair' } e s msg]
    · rfl
  · cases u
    by_cases hready : s.stA.t = e ∧ s.stA.dkA.isNone
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
    · simp only [oracle, StateT.run_bind, StateT.run_get, pure_bind,
        sendExposureA_eq, SCKAScheme.oracleSendArleak]
      rw [sendArleak_keygen_independent base onoff ecEk ecCt0 ecCt1 leak
        m e s hready pair pair']
  · cases u
    simp only [oracle, StateT.run_bind, StateT.run_get, pure_bind,
      sendExposureB_eq, SCKAScheme.oracleSendBrleak]
    rw [sendBrleak_encapsFresh_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e s pair,
      sendBrleak_encapsFresh_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e s pair']
  · rfl
  · rfl
  · rfl

end oppUniKemCKA.Security.Embedding.Sampling
