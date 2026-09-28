/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.OfflineOracle

/-!
# Key-generation sampling in the full security oracle

For every query and input state, averaging the selected key-generation
material in `encapsFresh` gives the query distribution of the fully fresh
stage. Ordinary A-sends use the key-generation marginal; leaking A-sends
retain the sampled coins. Other queries already use fresh encapsulation
and auxiliary decapsulation and retain the same response/state computation.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding.Sampling

variable {K PK SK C Sym : Type}

/-- For every material value, selected epoch, and state, averaging selected
key-generation material gives the fully fresh ordinary A-send distribution. -/
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
  have hf : Stage.encapsFresh ≠ .fresh := by decide
  apply evalDist_ext
  intro out
  by_cases he : s.stA.t = e <;> cases hd : s.stA.dkA <;>
    cases hp : s.stA.ekA <;> cases ha : s.stA.ack.ekRec
  all_goals
    simp only [schemeAt, Stage.pinsKeygen, scheme, sendA, kem,
      Pinned.keygen, hd, hp, ha, he, hf, ne_eq, not_true_eq_false, not_false_eq_true,
      decide_true, decide_false, Bool.true_and, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte, pure_bind]
  all_goals
    first
    | solve
      | apply ToVCVio.probOutput_bind_of_const'
        intro pair _
        rfl
    | simp only [← leak.keygen_fst, bind_assoc, pure_bind]

/-- For every material value, selected epoch, and state, averaging selected
key-generation material gives the fully fresh leaking A-send distribution,
including the returned key-generation coins. -/
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
    simp only [schemeAt, Stage.pinsKeygen, scheme, sendArleak, leakage,
      hd, hp, ha, he, hf, ne_eq, not_true_eq_false, not_false_eq_true,
      decide_true, decide_false, Bool.true_and, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte, pure_bind]
  all_goals
    apply ToVCVio.probOutput_bind_of_const'
    intro pair _
    rfl

/-- With both encapsulation phases fresh, B's local `sendB` computation
is independent of the pinned key-generation component. For every input
state it equals the same computation in the fully fresh stage. -/
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
  cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;> cases hc1 : s.stB.ct1 <;>
    cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
  all_goals
    simp only [schemeAt, scheme, sendB, hc0, hp, hc1, hst, ha, pure_bind,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;> rfl

/-- With both encapsulation phases fresh, B's local `sendBrleak` computation
is independent of the pinned key-generation component. For every input
state it equals the same computation in the fully fresh stage. -/
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

variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- For every query, material value, selected epoch, mode, and input state,
averaging key-generation material in `encapsFresh` gives the fully fresh
query's joint response/state distribution. -/
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
    𝒟[(oracle base onoff ecEk ecCt0 ecCt1 leak .fresh m e b t).run s] := by
  rcases t with (((((t | u) | u) | t) | u) | u)
  · rcases t with ((((n | u) | u) | n) | n)
    · apply evalDist_ext
      intro z
      apply ToVCVio.probOutput_bind_of_const'
      intro pair _
      rfl
    · cases u
      simp only [oracle, StateT.run_bind, StateT.run_get, pure_bind,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
      exact SCKAScheme.oracleSendA_sample_eq _ _ _ s
        (sendA_sample_keygen_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e s)
    · cases u
      apply evalDist_ext
      intro z
      apply ToVCVio.probOutput_bind_of_const'
      intro pair _
      simp only [oracle, StateT.run_bind, StateT.run_get, pure_bind,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        SCKAScheme.oracleSendB]
      rw [sendB_encapsFresh_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e s pair]
    · apply evalDist_ext
      intro z
      apply ToVCVio.probOutput_bind_of_const'
      intro pair _
      simp only [oracle, StateT.run_bind, StateT.run_get, pure_bind,
        SCKAScheme.sckaCorrectnessImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        SCKAScheme.oracleRecvA]
      cases hm : s.msgB n with
      | none => rfl
      | some out =>
        rcases out with ⟨msg, epoch⟩
        simp only
        rw [recvA_eq_auxiliary base onoff ecEk ecCt0 ecCt1 leak .encapsFresh
          { m with keygen := pair } e s msg,
          recvA_eq_auxiliary base onoff ecEk ecCt0 ecCt1 leak .fresh m e s msg]
    · apply evalDist_ext
      intro z
      apply ToVCVio.probOutput_bind_of_const'
      intro pair _
      rfl
  · cases u
    simp only [oracle, StateT.run_bind, StateT.run_get, pure_bind, sendExposureA_eq]
    exact SCKAScheme.oracleSendArleak_sample_eq _ _ _ _ s
      (sendArleak_sample_keygen_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e s)
  all_goals
    apply evalDist_ext
    intro z
    apply ToVCVio.probOutput_bind_of_const'
    intro pair _
    first
    | rfl
    | simp only [oracle, StateT.run_bind, StateT.run_get, pure_bind,
        sendExposureB_eq, SCKAScheme.oracleSendBrleak]
      rw [sendBrleak_encapsFresh_eq_fresh base onoff ecEk ecCt0 ecCt1 leak m e s pair]

end oppUniKemCKA.Security.Embedding.Sampling
