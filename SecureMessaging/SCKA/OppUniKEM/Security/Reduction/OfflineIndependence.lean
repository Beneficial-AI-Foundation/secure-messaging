/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.SourceFirstUse
import ToVCVio.OracleComp.QueryTracking.OneUseDistribution

/-!
# Independence from unused selected offline material

Fix key-generation material and use fresh online encapsulation. For every
query whose offline-use test is false, its joint response/state distribution
is independent of the stored offline output. Outside the selected first
B-send, the protocol retains the existing offline state. If the selected
epoch has already been challenged, its leaking first send rejects every
sample and retains the input state. Distribution equality covers the online
sampling performed before that rejection.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding.Sampling

variable {K PK SK C Sym : Type}
variable [DecidableEq Sym]

/-- For every state outside the selected first B-send, replacing the
stored offline output leaves the local sendB computation in `onlineFresh`
unchanged. The subsequent online phase samples at its actual inputs. -/
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
  have hf : Stage.onlineFresh ≠ .fixed := by decide
  by_cases he : s.stB.t = e <;> cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;>
    cases hc1 : s.stB.ct1 <;> cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
  all_goals
    simp only [he, hc0, Option.isNone_none, Option.isNone_some, Bool.false_eq_true,
      and_true, and_false, not_true_eq_false] at hh
  all_goals
    simp only [schemeAt, Stage.pinsKeygen, Stage.pinsOffline, Stage.pinsOnline,
      scheme, sendB, hc0, hp, hc1, hst, ha, pure_bind,
      onOff, leakage, Pinned.encapsOff, Pinned.encapsOn,
      he, hf, or_true, decide_true, decide_false, Bool.and_true, Bool.true_and, Bool.false_and,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

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
      onOff, leakage, Pinned.encapsOff,
      he, hf, or_true, decide_true, decide_false, Bool.and_true, Bool.true_and, Bool.false_and,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

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
    𝒟[(SCKAScheme.oracleSendBrleak sendExposureB
      (schemeAt ecEk ecCt0 ecCt1 stage m e s) ()).run s] = 𝒟[(pure (none, s) : ProbComp _)] := by
  apply SCKAScheme.oracleSendBrleak_rejected_evalDist _ _ s {e} ?_ ?_
  · intro key msg epoch next coins hout
    have hex := sendBrleak_exposure
      (kem m (stage.pinsKeygen && decide (s.stA.t = e))
        (stage.pinsOffline && decide (s.stB.t = e))
        (stage.pinsOnline && decide (s.stB.t = e)) (s.keyB s.stA.t))
      (onOff m _ _ _ _) ecCt0 ecCt1 (leakage leak m _ _ _ _) s.stB _ hout
      key msg epoch next coins rfl
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
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n)
    · rfl
    · cases u
      simp only [oracle, StateT.run_bind, StateT.run_get, pure_bind,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        SCKAScheme.oracleSendA]
      congr 2
    · cases u
      have hno : ¬(s.stB.t = e ∧ s.stB.ct0.isNone) := of_decide_eq_false hh
      simp only [oracle, StateT.run_bind, StateT.run_get, pure_bind,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        SCKAScheme.oracleSendB]
      rw [sendB_offline_independent base onoff ecEk ecCt0 ecCt1 leak m e s hno offline offline']
    · simp only [oracle, StateT.run_bind, StateT.run_get, pure_bind,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        SCKAScheme.oracleRecvA]
      cases hm : s.msgB n with
      | none => rfl
      | some out =>
        rcases out with ⟨msg, epoch⟩
        simp only
        rw [recvA_eq_auxiliary base onoff ecEk ecCt0 ecCt1 leak .onlineFresh
          { m with off := offline } e s msg,
          recvA_eq_auxiliary base onoff ecEk ecCt0 ecCt1 leak .onlineFresh
            { m with off := offline' } e s msg]
    · rfl
  · cases u
    simp only [oracle, StateT.run_bind, StateT.run_get, pure_bind,
      sendExposureA_eq, SCKAScheme.oracleSendArleak]
    congr 2
  · cases u
    by_cases hready : s.stB.t = e ∧ s.stB.ct0.isNone
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
    · simp only [oracle, StateT.run_bind, StateT.run_get, pure_bind,
        sendExposureB_eq, SCKAScheme.oracleSendBrleak]
      rw [sendBrleak_offline_independent base onoff ecEk ecCt0 ecCt1 leak
        m e s hready offline offline']
  · rfl
  · rfl
  · rfl

end oppUniKemCKA.Security.Embedding.Sampling
