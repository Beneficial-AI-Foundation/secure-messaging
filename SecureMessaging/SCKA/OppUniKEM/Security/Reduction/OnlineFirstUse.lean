/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.OnlineUse

/-!
# State after use of the selected online sample

For every pinned hybrid query satisfying `usesOnline e t s = true`, a
continuing successor has a key recorded by B at epoch `e`. An ordinary
online send records the selected key. An accepted leaking online send
exposes `e`, so the stopped game terminates. Together with persistence of
key availability, this is the first-use condition for one-use sampling.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

set_option maxHeartbeats 800000 in
-- The selected online and combined sends are reduced with their exposure guards.
/-- For every material value, epoch, mode, and query using the selected
online sample, every supported successor with a returned response has a
present B-table key at that epoch. -/
theorem hybridStopped_online_records_key
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hh : usesOnline e t s = true)
    (z : Option ((securitySpec leak Sym).Range t) ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support (((hybridStopped base onoff ecEk ecCt0 ecCt1 leak m e b t).run).run s))
    (hcont : z.1.isSome) : (z.2.keyB e).isSome := by
  change z ∈ support (do
    let out ← (hybridOracle base onoff ecEk ecCt0 ecCt1 leak m e b t).run s
    pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2)) at hz
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n)
    all_goals try simp only [usesOnline, Bool.false_eq_true] at hh
    cases u
    have hr : s.stB.t = e ∧ onlineReady s.stB := of_decide_eq_true hh
    obtain ⟨he, ha, hp, hc1, hsrc⟩ := hr
    obtain ⟨pk, hp⟩ := Option.isSome_iff_exists.mp hp
    have hc1 : s.stB.ct1 = none := Option.isNone_iff_eq_none.mp hc1
    cases hc0 : s.stB.ct0 <;> cases hst : s.stB.stCt
    all_goals simp only [hc0, hst, Option.isNone_some, Option.isNone_none,
      Option.isSome_none, Option.isSome_some, Bool.false_eq_true, or_false] at hsrc
    all_goals
      simp only [hybridOracle, honestOracle, SCKAScheme.sckaCorrectnessImpl,
        SCKAScheme.oracleSendB, honestScheme, scheme, sendB, Pinned.kem,
        Pinned.onOff, Pinned.encapsOff, Pinned.encapsOn, he, ha, hp, hc1, hc0, hst,
        QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
        StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte, decide_true,
        mem_support_pure_iff] at hz
      obtain rfl := hz
      simp [Function.update]
  · simp only [usesOnline, Bool.false_eq_true] at hh
  · cases u
    have hr : (s.stB.t = e ∧ onlineReady s.stB) ∧ e ∉ s.challenged := of_decide_eq_true hh
    obtain ⟨⟨he, ha, hp, hc1, hsrc⟩, hchall⟩ := hr
    obtain ⟨pk, hp⟩ := Option.isSome_iff_exists.mp hp
    have hc1 : s.stB.ct1 = none := Option.isNone_iff_eq_none.mp hc1
    cases hc0 : s.stB.ct0 <;> cases hst : s.stB.stCt
    all_goals simp only [hc0, hst, Option.isNone_some, Option.isNone_none,
      Option.isSome_none, Option.isSome_some, Bool.false_eq_true, or_false] at hsrc
    all_goals
      simp only [hybridOracle, honestOracle, SCKAScheme.oracleSendBrleak,
        honestScheme, scheme, sendBrleak, Pinned.leakage, sendExposureB,
        he, ha, hp, hc1, hc0, hst, hchall, StateT.run_bind, StateT.run_get,
        StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte, decide_true,
        Finset.singleton_inter] at hz
      obtain rfl := hz
      simp at hcont
  · simp only [usesOnline, Bool.false_eq_true] at hh
  · simp only [usesOnline, Bool.false_eq_true] at hh
  · simp only [usesOnline, Bool.false_eq_true] at hh

end oppUniKemCKA.Security.Embedding
