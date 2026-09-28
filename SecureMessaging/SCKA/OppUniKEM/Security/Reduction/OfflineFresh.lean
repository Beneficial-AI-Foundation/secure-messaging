/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.OnlineOracle

/-!
# Offline sampling at the protocol call

**Parameters.** Fix selected material `m`, epoch `e`, and an arbitrary game
state `s`. Online encapsulation already samples at its actual inputs.

**Statement.** For each ordinary or leaking B-send, averaging the selected
offline material gives the corresponding send in the `encapsFresh` stage.

**Proof.** The fresh offline sampler replaces its stored output on the
first B-send of the selected epoch. Every other branch retains its local
offline state. Online sampling follows the same continuation in both games.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

set_option maxHeartbeats 800000 in
-- Separate the local send phases before applying the shared game continuation.
/-- For every material value, selected epoch, and input state, averaging
selected offline material in the `onlineFresh` stage gives exactly the
ordinary B-send distribution in the `encapsFresh` stage. -/
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
  have hf : Sampling.Stage.onlineFresh ≠ .fixed := by decide
  have he₀ : Sampling.Stage.encapsFresh ≠ .fixed := by decide
  have he₁ : Sampling.Stage.encapsFresh ≠ .onlineFresh := by decide
  apply evalDist_ext
  intro out
  by_cases he : s.stB.t = e <;> cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;>
    cases hc1 : s.stB.ct1 <;> cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
  all_goals
    simp only [Sampling.schemeAt, Sampling.Stage.pinsKeygen,
      Sampling.Stage.pinsOffline, Sampling.Stage.pinsOnline, scheme, sendB,
      hc0, hp, hc1, hst, ha, pure_bind, Sampling.onOff, Sampling.leakage,
      Pinned.encapsOff, Pinned.encapsOn, he, decide_true, decide_false,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, hf, he₀, he₁,
      or_true, or_false, Bool.and_true, Bool.false_and, ↓reduceIte]
  all_goals
    first
    | solve
      | apply ToVCVio.probOutput_bind_of_const'
        intro offline _
        rfl
    | simp only [← leak.encapsOff_fst, bind_assoc, pure_bind]

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
      hc0, hp, hc1, hst, ha, pure_bind, Sampling.onOff, Sampling.leakage,
      Pinned.encapsOff, he, decide_true, decide_false,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, hf, he₀, he₁,
      or_true, or_false, Bool.and_true, Bool.false_and, ↓reduceIte]
  all_goals
    apply ToVCVio.probOutput_bind_of_const'
    intro offline _
    rfl

end oppUniKemCKA.Security.Embedding
