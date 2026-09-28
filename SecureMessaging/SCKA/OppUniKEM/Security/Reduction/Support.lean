/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.SourcePreservation
import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction.Send

/-!
# Honest support of pinned sends

**Parameters.** Fix `m ∈ support (sampleMaterial leak)`, selected epoch `e`,
and a game state `s`.

**Statement.** Every supported pinned A-send is supported by the ordinary
A-send. The same holds for B when `s` is transcript-consistent and satisfies
`pinnedSources m e`.

**Proof.** Selected key-generation and offline samples belong to their
ordinary supports by the leakage marginal laws. Transcript consistency
and the source invariant identify the selected online inputs with those
used to sample `m.on`. This support inclusion allows reuse of the ordinary
send preservation theorems for the honest intermediate game.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- For every supported complete material value and selection bit, every
supported pinned key pair belongs to the original key-generation support. -/
theorem pinned_keygen_support
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) (m : Material leak)
    (hm : m ∈ support (sampleMaterial leak)) (selected : Bool)
    (pair : PK × SK) (h : pair ∈ support (Pinned.keygen m selected)) :
    pair ∈ support base.keygen := by
  cases selected
  · exact h
  · obtain rfl := (mem_support_pure_iff _ _).mp h
    exact (sampleMaterial_ordinary_support leak m hm).1

/-- For every supported complete material value and selection bit, every
supported pinned offline output belongs to the original offline support. -/
theorem pinned_off_support
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) (m : Material leak)
    (hm : m ∈ support (sampleMaterial leak)) (selected : Bool)
    (out : onoff.St × onoff.C₀) (h : out ∈ support (Pinned.encapsOff m selected)) :
    out ∈ support onoff.encapsOff := by
  cases selected
  · exact h
  · obtain rfl := (mem_support_pure_iff _ _).mp h
    exact (sampleMaterial_ordinary_support leak m hm).2.1

/-- For every supported material value and state, a supported pinned
A-send output is also supported by the original A-send computation. -/
theorem sendA_pinned_support
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (hm : m ∈ support (sampleMaterial leak)) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (out : Option (Option (ℕ × K) × Message Sym × ℕ × StA onoff Sym))
    (hout : out ∈ support
      (sendA (Pinned.kem m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (s.keyB s.stA.t))
        (Pinned.onOff m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (s.keyB s.stA.t))
        ecEk s.stA)) :
    out ∈ support (sendA base onoff ecEk s.stA) := by
  cases hd : s.stA.dkA with
  | none =>
    simp only [sendA, hd, pure_bind, mem_support_bind_iff] at hout ⊢
    obtain ⟨pair, hpair, hout⟩ := hout
    exact ⟨pair, pinned_keygen_support leak m hm _ pair hpair, hout⟩
  | some sk => simpa only [sendA, hd] using hout

/-- For every supported material value, a transcript-consistent state
satisfying the source invariant, and a supported pinned B-send output,
that output also belongs to the original B-send support. -/
theorem sendB_pinned_support
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (hm : m ∈ support (sampleMaterial leak)) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hsrc : pinnedSources m e s)
    (out : Option (Option (ℕ × K) × Message Sym × ℕ × StB onoff Sym))
    (hout : out ∈ support
      (sendB (Pinned.kem m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (s.keyB s.stA.t))
        (Pinned.onOff m (decide (s.stA.t = e)) (decide (s.stB.t = e)) (s.keyB s.stA.t))
        ecCt0 ecCt1 s.stB)) :
    out ∈ support (sendB base onoff ecCt0 ecCt1 s.stB) := by
  have hoff := (sampleMaterial_ordinary_support leak m hm).2.1
  have hon := (sampleMaterial_ordinary_support leak m hm).2.2
  by_cases he : s.stB.t = e
  · cases hc0 : s.stB.ct0 with
    | none =>
      have honpk : ∀ pk, s.stB.ekA = some pk →
          m.on.1 ∈ support (onoff.encapsOn m.off.1.1 pk) := by
        intro pk hp
        obtain ⟨sk, ht, hpA, hdA⟩ := oppUniKemCKA.Reduction.Internal.newOff_source_shape
          base onoff ecEk ecCt0 ecCt1 s hs pk hp hc0
        have h := (hsrc.1 (ht.trans he) (by simp [hdA])).1
        have heq : pk = m.keygen.1.1 := Option.some.inj (hpA.symm.trans h)
        simpa only [heq] using hon
      simp only [sendB, hc0, Pinned.onOff, Pinned.encapsOff, he, decide_true,
        ↓reduceIte, pure_bind] at hout
      simp only [sendB, hc0, pure_bind, mem_support_bind_iff]
      refine ⟨m.off.1, hoff, ?_⟩
      cases hp : s.stB.ekA <;> cases hc1 : s.stB.ct1 <;> cases ha : s.stB.ack.ctRec
      all_goals
        simp only [hp, hc1, ha, Bool.not_false, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte, pure_bind, Pinned.encapsOn, he] at hout ⊢
        first
        | exact hout
        | exact (mem_support_bind_iff _ _ _).mpr ⟨m.on.1, honpk _ hp, hout⟩
    | some ct0 =>
      simp only [sendB, hc0, pure_bind] at hout ⊢
      cases hp : s.stB.ekA <;> cases hc1 : s.stB.ct1 <;>
        cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
      all_goals
        simp only [hp, hc1, hst, ha, Bool.not_false, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte, pure_bind, Pinned.onOff, Pinned.encapsOn, he, decide_true] at hout ⊢
        first
        | exact hout
        | have hinputs := pinned_online_inputs base onoff ecEk ecCt0 ecCt1
            leak m e s hs hsrc he _ _ hp hst hc1
          apply (mem_support_bind_iff _ _ _).mpr
          refine ⟨m.on.1, ?_, hout⟩
          simpa only [hinputs.1, hinputs.2] using hon
  · cases hc0 : s.stB.ct0 <;> cases hp : s.stB.ekA <;>
      cases hc1 : s.stB.ct1 <;> cases hst : s.stB.stCt <;> cases ha : s.stB.ack.ctRec
    all_goals
      simpa only [sendB, hc0, hp, hc1, hst, ha, pure_bind,
        Pinned.onOff, Pinned.encapsOff, Pinned.encapsOn, he, decide_false,
        Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] using hout


/-- Fix supported material and an honest state. Every response/state pair
of the pinned A-send oracle is supported by the original A-send oracle,
including message-table, key-table, and correctness bookkeeping. -/
theorem oracleSendA_pinned_support [DecidableEq K] [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (hm : m ∈ support (sampleMaterial leak)) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (z : Option (ℕ × Option ℕ × Message Sym) ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.oracleSendA (honestScheme ecEk ecCt0 ecCt1 m e s) ()).run s)) :
    z ∈ support
      ((SCKAScheme.oracleSendA (scheme base onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s) := by
  simp only [SCKAScheme.oracleSendA, StateT.run_bind, StateT.run_get,
    StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
    mem_support_bind_iff] at hz ⊢
  obtain ⟨out, hout, hz⟩ := hz
  refine ⟨out, sendA_pinned_support base onoff ecEk leak m hm e s out hout, ?_⟩
  cases out with
  | none => exact hz
  | some out => rcases out with ⟨key, msg, t, next⟩; cases key <;> exact hz

/-- Fix supported material and a transcript-consistent state satisfying
`pinnedSources m e`. Every response/state pair of the pinned B-send oracle
is supported by the original B-send oracle. -/
theorem oracleSendB_pinned_support [DecidableEq K] [DecidableEq Sym]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (hDet : base.DeterministicDecaps)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (m : Material leak) (hm : m ∈ support (sampleMaterial leak)) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv base onoff ecEk ecCt0 ecCt1 s) (hsrc : pinnedSources m e s)
    (z : Option (ℕ × Option ℕ × Message Sym) ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.oracleSendB (honestScheme ecEk ecCt0 ecCt1 m e s) ()).run s)) :
    z ∈ support
      ((SCKAScheme.oracleSendB (scheme base onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s) := by
  simp only [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get,
    StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
    mem_support_bind_iff] at hz ⊢
  obtain ⟨out, hout, hz⟩ := hz
  refine ⟨out, sendB_pinned_support base onoff ecEk ecCt0 ecCt1 leak
    m hm e s hs hsrc out hout, ?_⟩
  cases out with
  | none => exact hz
  | some out => rcases out with ⟨key, msg, t, next⟩; cases key <;> exact hz

end oppUniKemCKA.Security.Embedding
