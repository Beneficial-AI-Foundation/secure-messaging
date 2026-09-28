/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.SourceSuccess
import SecureMessaging.SCKA.OppUniKEM.Security.Leakage

/-!
# Continuing first uses install the selected source

**Use test.** `usesSource phase e query s` selects the first send invoking
the phase at epoch `e`. A leaking send also requires `e ∉ s.challenged`.

**Results.** Used states have no further uses. Every continuing first use
establishes `sourceUsed`: ordinary sends install the source field, and
accepted leaking sends expose `e`, terminating the stopped execution.
These statements supply the first-use premises for both source samplers.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding.Sampling

variable {K PK SK C Sym : Type}

/-- Whether query `t` invokes source phase `phase` in selected epoch `e`.
For leaking sends the test includes the selected-epoch exposure guard. -/
def usesSource {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (phase : SourcePhase) (e : ℕ)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) : Bool :=
  match phase, t with
  | .keygen, .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr ())))))))) =>
    decide (s.stA.t = e ∧ s.stA.dkA.isNone)
  | .offline, .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr ()))))))) =>
    decide (s.stB.t = e ∧ s.stB.ct0.isNone)
  | .keygen, .inl (.inl (.inl (.inl (.inr ())))) =>
    decide ((s.stA.t = e ∧ s.stA.dkA.isNone) ∧ e ∉ s.challenged)
  | .offline, .inl (.inl (.inl (.inr ()))) =>
    decide ((s.stB.t = e ∧ s.stB.ct0.isNone) ∧ e ∉ s.challenged)
  | _, _ => false

/-- For every phase, epoch, query, and state where the phase is used,
`usesSource` is false. Its field remains present in that epoch, or the
party has already advanced beyond the selected epoch. -/
theorem usesSource_false_of_used
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (phase : SourcePhase) (e : ℕ)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : sourceUsed phase e s.stA s.stB) : usesSource phase e t s = false := by
  cases phase with
  | keygen =>
    have hno : ¬(s.stA.t = e ∧ s.stA.dkA.isNone) := by
      rintro ⟨ht, hp⟩
      cases hd : s.stA.dkA <;> simp_all [sourceUsed]
    simp only [Option.isNone_iff_eq_none] at hno
    rcases t with (((((t | u) | u) | t) | u) | u)
    · rcases t with ((((n | u) | u) | n) | n)
      all_goals simp [usesSource] <;> aesop
    all_goals simp [usesSource] <;> aesop
  | offline =>
    have hno : ¬(s.stB.t = e ∧ s.stB.ct0.isNone) := by
      rintro ⟨ht, hp⟩
      cases hc : s.stB.ct0 <;> simp_all [sourceUsed]
    simp only [Option.isNone_iff_eq_none] at hno
    rcases t with (((((t | u) | u) | t) | u) | u)
    · rcases t with ((((n | u) | u) | n) | n)
      all_goals simp [usesSource] <;> aesop
    all_goals simp [usesSource] <;> aesop

variable [DecidableEq K] [DecidableEq Sym]

/-- For every stage and state with party A at the selected epoch,
every supported ordinary A-send successor satisfies `sourceUsed .keygen`. -/
theorem oracleSendA_installs_source
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (stage : Stage) (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (he : s.stA.t = e)
    (z : Option (ℕ × Option ℕ × Message Sym) ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.oracleSendA (schemeAt ecEk ecCt0 ecCt1 stage m e s) ()).run s)) :
    sourceUsed .keygen e z.2.stA z.2.stB := by
  simp only [SCKAScheme.oracleSendA, StateT.run_bind, StateT.run_get,
    StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
    mem_support_bind_iff] at hz
  obtain ⟨out, hout, hz⟩ := hz
  cases out with
  | none => exact False.elim (sendA_none_not_mem_support _ _ ecEk _ hout)
  | some out =>
    rcases out with ⟨key, msg, epoch, next⟩
    have hshape := sendA_source_shape
      (kem m (stage.pinsKeygen && decide (s.stA.t = e))
        (stage.pinsOffline && decide (s.stB.t = e))
        (stage.pinsOnline && decide (s.stB.t = e)) (s.keyB s.stA.t))
      (onOff m _ _ _ _) ecEk s.stA key msg epoch next hout
    cases key <;>
      simp only [StateT.run_bind, StateT.run_set, pure_bind,
        StateT.run_pure, mem_support_pure_iff] at hz
    all_goals obtain rfl := hz; exact Or.inr ⟨hshape.1.trans he, hshape.2⟩

/-- If party A is at `e` with its source field absent and `e` has not
been challenged, its leaking source send terminates the stopped game in
every sampling stage, because the accepted coins expose `e`. -/
theorem leaking_keygen_stops
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (stage : Stage) (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (he : s.stA.t = e) (hfield : s.stA.dkA = none) (hc : e ∉ s.challenged)
    (z : Option (Option (ℕ × Option ℕ × Message Sym ×
      SendRand leak.KeygenRand leak.OffRand leak.OnRand)) ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support (((stopOnState
      (SCKAScheme.oracleSendArleak sendExposureA (schemeAt ecEk ecCt0 ecCt1 stage m e s))
      (fun s => decide (e ∈ s.exposed)) ()).run).run s)) : z.1 = none := by
  apply SCKAScheme.oracleSendArleak_stop_of_exposure _ _ s {e} e ?_ ?_ ?_
    (Finset.mem_singleton_self e) z hz
  · exact sendArleak_none_not_mem_support _ _ ecEk _ _
  · intro key msg epoch next coins hout
    have hex := sendArleak_exposure
      (kem m (stage.pinsKeygen && decide (s.stA.t = e))
        (stage.pinsOffline && decide (s.stB.t = e))
        (stage.pinsOnline && decide (s.stB.t = e)) (s.keyB s.stA.t))
      (onOff m _ _ _ _) ecEk (leakage leak m _ _ _ _) s.stA _ hout
      key msg epoch next coins rfl
    simpa only [leakEpochsA, hfield, Option.isNone_none,
      Bool.true_or, ↓reduceIte, he] using hex
  · simp [hc]

/-- For every stage and state with party B at the selected epoch,
every supported ordinary B-send successor satisfies `sourceUsed .offline`. -/
theorem oracleSendB_installs_source
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (stage : Stage) (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (he : s.stB.t = e)
    (z : Option (ℕ × Option ℕ × Message Sym) ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.oracleSendB (schemeAt ecEk ecCt0 ecCt1 stage m e s) ()).run s)) :
    sourceUsed .offline e z.2.stA z.2.stB := by
  simp only [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get,
    StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
    mem_support_bind_iff] at hz
  obtain ⟨out, hout, hz⟩ := hz
  cases out with
  | none =>
    exact False.elim (sendB_none_not_mem_support
      (kem m (stage.pinsKeygen && decide (s.stA.t = e))
        (stage.pinsOffline && decide (s.stB.t = e))
        (stage.pinsOnline && decide (s.stB.t = e)) (s.keyB s.stA.t))
      (onOff m _ _ _ _) ecCt0 ecCt1 _ hout)
  | some out =>
    rcases out with ⟨key, msg, epoch, next⟩
    have hshape := sendB_source_shape
      (kem m (stage.pinsKeygen && decide (s.stA.t = e))
        (stage.pinsOffline && decide (s.stB.t = e))
        (stage.pinsOnline && decide (s.stB.t = e)) (s.keyB s.stA.t))
      (onOff m _ _ _ _) ecCt0 ecCt1 s.stB key msg epoch next hout
    cases key <;>
      simp only [StateT.run_bind, StateT.run_set, pure_bind,
        StateT.run_pure, mem_support_pure_iff] at hz
    all_goals obtain rfl := hz; exact Or.inr ⟨hshape.1.trans he, hshape.2⟩

/-- If party B is at `e` with its source field absent and `e` has not
been challenged, its leaking source send terminates the stopped game in
every sampling stage, because the accepted coins expose `e`. -/
theorem leaking_offline_stops
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (stage : Stage) (m : Material leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (he : s.stB.t = e) (hfield : s.stB.ct0 = none) (hc : e ∉ s.challenged)
    (z : Option (Option (ℕ × Option ℕ × Message Sym ×
      SendRand leak.KeygenRand leak.OffRand leak.OnRand)) ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support (((stopOnState
      (SCKAScheme.oracleSendBrleak sendExposureB (schemeAt ecEk ecCt0 ecCt1 stage m e s))
      (fun s => decide (e ∈ s.exposed)) ()).run).run s)) : z.1 = none := by
  apply SCKAScheme.oracleSendBrleak_stop_of_exposure _ _ s {e} e ?_ ?_ ?_
    (Finset.mem_singleton_self e) z hz
  · exact sendBrleak_none_not_mem_support
      (kem m (stage.pinsKeygen && decide (s.stA.t = e))
        (stage.pinsOffline && decide (s.stB.t = e))
        (stage.pinsOnline && decide (s.stB.t = e)) (s.keyB s.stA.t))
      (onOff m _ _ _ _) ecCt0 ecCt1 (leakage leak m _ _ _ _) _
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

/-- For every stage, material value, phase, epoch, mode, and query with
`usesSource = true`, every supported continuing stopped-query successor
satisfies `sourceUsed` for that phase and epoch. -/
theorem stopped_first_source_use
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (stage : Stage) (m : Material leak) (e : ℕ) (b : Bool) (phase : SourcePhase)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hh : usesSource phase e t s = true)
    (z : Option ((securitySpec leak Sym).Range t) ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support (((stopped base onoff ecEk ecCt0 ecCt1 leak stage m e b t).run).run s))
    (hcont : z.1.isSome) : sourceUsed phase e z.2.stA z.2.stB := by
  cases phase <;> rcases t with (((((t | u) | u) | t) | u) | u)
  all_goals try (rcases t with ((((n | u) | u) | n) | n))
  all_goals try (simp only [usesSource, Bool.false_eq_true] at hh)
  all_goals cases u
  all_goals
    first
    | have hhit : s.stA.t = e ∧ s.stA.dkA.isNone := of_decide_eq_true hh
      change z ∈ support (do
        let out ← (SCKAScheme.oracleSendA (schemeAt ecEk ecCt0 ecCt1 stage m e s) ()).run s
        pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2)) at hz
      obtain ⟨out, hout, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
      obtain rfl := (mem_support_pure_iff _ _).mp hz
      exact oracleSendA_installs_source base onoff ecEk ecCt0 ecCt1 leak
        stage m e s hhit.1 out hout
    | have hhit : s.stB.t = e ∧ s.stB.ct0.isNone := of_decide_eq_true hh
      change z ∈ support (do
        let out ← (SCKAScheme.oracleSendB (schemeAt ecEk ecCt0 ecCt1 stage m e s) ()).run s
        pure (if decide (e ∈ out.2.exposed) then none else some out.1, out.2)) at hz
      obtain ⟨out, hout, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
      obtain rfl := (mem_support_pure_iff _ _).mp hz
      exact oracleSendB_installs_source base onoff ecEk ecCt0 ecCt1 leak
        stage m e s hhit.1 out hout
    | have hhit : (s.stA.t = e ∧ s.stA.dkA.isNone) ∧ e ∉ s.challenged :=
        of_decide_eq_true hh
      have hstop := leaking_keygen_stops base onoff ecEk ecCt0 ecCt1 leak stage m e s
        hhit.1.1 (Option.isNone_iff_eq_none.mp hhit.1.2) hhit.2 z hz
      simp only [hstop, Option.isSome_none, Bool.false_eq_true] at hcont
    | have hhit : (s.stB.t = e ∧ s.stB.ct0.isNone) ∧ e ∉ s.challenged :=
        of_decide_eq_true hh
      have hstop := leaking_offline_stops base onoff ecEk ecCt0 ecCt1 leak stage m e s
        hhit.1.1 (Option.isNone_iff_eq_none.mp hhit.1.2) hhit.2 z hz
      simp only [hstop, Option.isSome_none, Bool.false_eq_true] at hcont

end oppUniKemCKA.Security.Embedding.Sampling
