/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.OnlineSampling

/-!
# Online sampling at the protocol call

Fix selected source material `m` and epoch `e`. In a transcript-consistent
state satisfying `pinnedSources m e`, fresh online encapsulation at `e`
uses `m.keygen.1.1` and `m.off.1.1`. Therefore sampling the pinned online
output at each query gives the same query law as the `onlineFresh` stage.
The ordinary-send comparison uses the online coin-forgetting marginal;
the leaking-send comparison retains those coins.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- For every transcript-consistent state satisfying the selected source
invariant, B's decoded public key equals the selected public key whenever
B is in epoch `e` and its online ciphertext is absent. -/
theorem selected_online_public_key
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hsrc : pinnedSources m e s)
    (he : s.stB.t = e) (pk : PK) (hp : s.stB.ekA = some pk) (hc1 : s.stB.ct1 = none) :
    pk = m.keygen.1.1 := by
  have ht := epochs_eq_before_online base onoff ecEk ecCt0 ecCt1 s hs hc1
  obtain ⟨T, hT⟩ := hs
  obtain ⟨sk, hpk⟩ := hT.decodedEk pk hp
  have hpair := hT.keypairA
  rw [ht, hpk] at hpair
  have ha : s.stA.ekA = some pk ∧ s.stA.dkA = some sk := by
    cases hpA : s.stA.ekA <;> cases hsA : s.stA.dkA <;> simp_all [Option.map₂]
  exact Option.some.inj (ha.1.symm.trans (hsrc.1 (ht.trans he) (by simp [ha.2])).1)

set_option maxHeartbeats 800000 in
-- Compare the local phase branches before lifting the result through game bookkeeping.
/-- For every transcript-consistent state with fixed selected sources,
averaging the pinned online sample gives exactly the ordinary-send law
of the stage that samples online encapsulation at the protocol call. -/
theorem sendB_sample_online_eq_fresh [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hsrc : pinnedSources m e s) :
    𝒟[(do
      let online ← leak.encapsOnRleak m.off.1.1 m.keygen.1.1
      (honestScheme ecEk ecCt0 ecCt1 { m with on := online } e s).sendB s.stB)] =
    𝒟[(Sampling.schemeAt ecEk ecCt0 ecCt1 .onlineFresh m e s).sendB s.stB] := by
  have hpub := selected_online_public_key base onoff ecEk ecCt0 ecCt1 leak m e s hs hsrc
  have hoff (he : s.stB.t = e) (st : onoff.St) (hst : s.stB.stCt = some st) :
      st = m.off.1.1 :=
    Option.some.inj (hst.symm.trans (hsrc.2 he (by simp [hst])).1)
  have hstage : Sampling.Stage.onlineFresh ≠ .fixed := by decide
  apply evalDist_ext
  intro out
  by_cases he : s.stB.t = e <;> cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;>
    cases hc1 : s.stB.ct1 <;> cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
  all_goals
    simp only [honestScheme, Sampling.schemeAt, Sampling.Stage.pinsKeygen,
      Sampling.Stage.pinsOffline, Sampling.Stage.pinsOnline, scheme, sendB,
      hc0, hp, hc1, hst, ha, pure_bind, Pinned.onOff, Sampling.onOff,
      Pinned.encapsOff, Pinned.encapsOn, he, decide_true, decide_false,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, hstage, or_true,
      Bool.and_true, ↓reduceIte]
  all_goals
    first
    | solve
      | apply ToVCVio.probOutput_bind_of_const'
        intro online _
        rfl
    | have hpk := hpub he _ hp hc1
      first
      | solve | simp only [hpk, ← leak.encapsOn_fst, bind_assoc, pure_bind]
      | have hstate := hoff he _ hst
        simp only [hpk, hstate, ← leak.encapsOn_fst, bind_assoc, pure_bind]

set_option maxHeartbeats 800000 in
-- Compare the local phase branches before lifting the result through game bookkeeping.
/-- For every transcript-consistent state with fixed selected sources,
averaging the pinned online sample gives exactly the leaking-send law
of the stage that samples online encapsulation at the protocol call. -/
theorem sendBrleak_sample_online_eq_fresh [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hsrc : pinnedSources m e s) :
    𝒟[(do
      let online ← leak.encapsOnRleak m.off.1.1 m.keygen.1.1
      (honestScheme ecEk ecCt0 ecCt1 { m with on := online } e s).sendBrleak s.stB)] =
    𝒟[(Sampling.schemeAt ecEk ecCt0 ecCt1 .onlineFresh m e s).sendBrleak s.stB] := by
  have hpub := selected_online_public_key base onoff ecEk ecCt0 ecCt1 leak m e s hs hsrc
  have hoff (he : s.stB.t = e) (st : onoff.St) (hst : s.stB.stCt = some st) :
      st = m.off.1.1 :=
    Option.some.inj (hst.symm.trans (hsrc.2 he (by simp [hst])).1)
  have hstage : Sampling.Stage.onlineFresh ≠ .fixed := by decide
  apply evalDist_ext
  intro out
  by_cases he : s.stB.t = e <;> cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;>
    cases hc1 : s.stB.ct1 <;> cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
  all_goals
    simp only [honestScheme, Sampling.schemeAt, Sampling.Stage.pinsKeygen,
      Sampling.Stage.pinsOffline, Sampling.Stage.pinsOnline, scheme, sendBrleak,
      hc0, hp, hc1, hst, ha, pure_bind, Pinned.leakage, Sampling.leakage,
      he, decide_true, decide_false,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, hstage, or_true,
      Bool.and_true, ↓reduceIte]
  all_goals
    first
    | solve
      | apply ToVCVio.probOutput_bind_of_const'
        intro online _
        rfl
    | have hpk := hpub he _ hp hc1
      first
      | solve | simp only [hpk]
      | have hstate := hoff he _ hst
        simp only [hpk, hstate]

end oppUniKemCKA.Security.Embedding
