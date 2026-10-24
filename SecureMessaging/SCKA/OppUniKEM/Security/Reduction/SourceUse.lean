/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.HybridGame
import SecureMessaging.SCKA.Security
import SecureMessaging.SCKA.OppUniKEM.Security.Basic

/-!
# Single use of the source samples

**Main results.** For a *source phase* (A's key generation or B's offline encapsulation,
`SourcePhase`), let `used := sourceUsed phase e` (the phase output of `e` is present, or its party
has passed `e`) and `hit := usesSource phase e` (the query runs the phase at `e`). These satisfy
the one-use conditions of `stoppedRun_sample_once_eq` for the stage oracles
`oracle stage kemMat e b` (`HybridGame`):

- every query preserves `used` (`oracle_preserves_sourceUsed`);
- `used` implies `hit = false` (`usesSource_false_of_used`);
- after a query satisfying `hit`, every possible successor in which `e` is unexposed satisfies
  `used` (`oracle_first_source_use`).
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding.Sampling

variable {K PK SK C Sym : Type}

/-- Sampling phases whose samplers read no protocol state. -/
inductive SourcePhase where
  /-- A's key generation. -/
  | keygen
  /-- B's offline encapsulation. -/
  | offline
  deriving DecidableEq

/-- Source phase `phase` of epoch `e` is used: its party has passed `e`, or is at `e` with the
phase output (`dkA`, respectively `ct0`) present. -/
def sourceUsed {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (phase : SourcePhase) (e : ℕ) (a : StA onoff Sym) (b : StB onoff Sym) : Prop :=
  match phase with
  | .keygen => e < a.t ∨ (a.t = e ∧ a.dkA.isSome)
  | .offline => e < b.t ∨ (b.t = e ∧ b.ct0.isSome)

/-- Every possible successful result of `sendA a` keeps A's epoch and has `dkA` present. -/
theorem sendA_source_shape
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym) (a : StA onoff Sym)
    (key : Option (ℕ × K)) (msg : Message Sym) (t : ℕ) (next : StA onoff Sym)
    (h : some (key, msg, t, next) ∈ support (sendA base onoff ecEk a)) :
    next.t = a.t ∧ next.dkA.isSome := by
  cases hd : a.dkA <;> cases hp : a.ekA <;> cases ha : a.ack.ekRec
  all_goals
    simp only [sendA, hd, hp, ha, Bool.false_eq_true, ↓reduceIte, pure_bind,
      mem_support_bind_iff, mem_support_pure_iff, Prod.exists,
      Option.some.injEq, Prod.mk.injEq] at h
    aesop

/-- Every possible successful result of `sendB b` keeps B's epoch and has `ct0` present. -/
theorem sendB_source_shape
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (b : StB onoff Sym)
    (key : Option (ℕ × K)) (msg : Message Sym) (t : ℕ) (next : StB onoff Sym)
    (h : some (key, msg, t, next) ∈ support (sendB base onoff ecCt0 ecCt1 b)) :
    next.t = b.t ∧ next.ct0.isSome := by
  cases hc0 : b.ct0 <;> cases hp : b.ekA <;> cases hc1 : b.ct1 <;>
    cases hst : b.stCt <;> cases ha : b.ack.ctRec
  all_goals
    simp only [sendB, hc0, hp, hc1, hst, ha, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, pure_bind,
      mem_support_bind_iff, mem_support_pure_iff, Prod.exists,
      Option.some.injEq, Prod.mk.injEq] at h
    aesop

variable [DecidableEq K] [DecidableEq Sym]

/-- The correctness queries of `schemeAt stage kemMat e s` from `s` preserve
`sourceUsed phase e`. -/
theorem correctness_preserves_sourceUsed
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ) (phase : SourcePhase)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : sourceUsed phase e s.stA s.stB)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (z : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Range t ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.sckaCorrectnessImpl (schemeAt ecEk ecCt0 ecCt1 stage kemMat e s) t).run s)) :
    sourceUsed phase e z.2.stA z.2.stB := by
  apply SCKAScheme.correctnessImpl_preserves_localInv_at _ (sourceUsed phase e) s hs
    ?_ ?_ ?_ ?_ t z hz
  · intro key msg epoch next hout
    have hshape := sendA_source_shape
      (stageKem stage kemMat e s) (stageOnOff stage kemMat e s) ecEk s.stA key msg epoch next hout
    cases phase with
    | keygen =>
      rcases hs with h | ⟨h, _⟩
      · exact Or.inl (by simpa only [hshape.1] using h)
      · exact Or.inr ⟨hshape.1.trans h, hshape.2⟩
    | offline => exact hs
  · intro key msg epoch next hout
    have hshape := sendB_source_shape
      (stageKem stage kemMat e s) (stageOnOff stage kemMat e s) ecCt0 ecCt1 s.stB key msg epoch
      next hout
    cases phase with
    | keygen => exact hs
    | offline =>
      rcases hs with h | ⟨h, _⟩
      · exact Or.inl (by simpa only [hshape.1] using h)
      · exact Or.inr ⟨hshape.1.trans h, hshape.2⟩
  · intro msg key epoch next hout
    rw [recvA_eq_ideal] at hout
    have hshape := oppUniKemCKA.Reduction.Internal.recvA_kem_source_shape
      base onoff (fun _ _ => s.keyB s.stA.t)
      ecCt0 ecCt1 s.stA msg key epoch next hout
    cases phase with
    | offline => exact hs
    | keygen =>
      rcases hshape with h | h
      · simpa only [sourceUsed, h.1, h.2.2] using hs
      · apply Or.inl
        rcases hs with hs | ⟨hs, _⟩ <;> omega
  · intro msg key epoch next hout
    have hshape := oppUniKemCKA.Reduction.Internal.recvB_kem_source_shape
      base onoff ecEk s.stB msg key epoch next hout
    cases phase with
    | keygen => exact hs
    | offline =>
      rcases hshape with h | h
      · simpa only [sourceUsed, h.1, h.2.2.1] using hs
      · apply Or.inl
        rcases hs with hs | ⟨hs, _⟩ <;> omega

/-- `oracle stage kemMat e b` preserves `sourceUsed phase e`. -/
theorem oracle_preserves_sourceUsed [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool) (phase : SourcePhase) :
    QueryImpl.PreservesInv (oracle base onoff ecEk ecCt0 ecCt1 leak stage kemMat e b)
      (fun s => sourceUsed phase e s.stA s.stB) :=
  securityImplAt_preservesInv base onoff leak _ _ _ (fun _ _ _ h => h)
    (fun _ => sendArleak_forget (onoff := Pinned.onOff kemMat _ _ _ _) _ _ _)
    (fun _ => sendBrleak_forget (onoff := Pinned.onOff kemMat _ _ _ _) _ _ _ _)
    (SCKAScheme.challOf_recordsChallenges _)
    (fun s hs t => correctness_preserves_sourceUsed base onoff ecEk ecCt0 ecCt1 leak
      stage kemMat e phase s hs t)

end oppUniKemCKA.Security.Embedding.Sampling

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding.Sampling

variable {K PK SK C Sym : Type}

/-- A's ordinary send never fails: `none ∉ support (sendA s)`. -/
theorem sendA_none_not_mem_support
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (s : StA onoff Sym) :
    none ∉ support (sendA base onoff ecEk s) := by
  cases hd : s.dkA <;> cases hp : s.ekA <;> cases ha : s.ack.ekRec <;>
    simp [sendA, hd, hp, ha]

/-- Leaking-send version of `sendA_none_not_mem_support`. -/
theorem sendArleak_none_not_mem_support
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (leak : base.OnOffRandLeak onoff)
    (s : StA onoff Sym) :
    none ∉ support (sendArleak base onoff ecEk leak s) := by
  intro h
  apply sendA_none_not_mem_support base onoff ecEk s
  rw [sendA_eq_map_sendArleak base onoff ecEk leak s, support_map]
  exact ⟨none, h, rfl⟩

/-- B version of `sendA_none_not_mem_support`. -/
theorem sendB_none_not_mem_support
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (s : StB onoff Sym) :
    none ∉ support (sendB base onoff ecCt0 ecCt1 s) := by
  cases hc0 : s.ct0 <;> cases hp : s.ekA <;> cases hc1 : s.ct1 <;>
    cases hst : s.stCt <;> cases ha : s.ack.ctRec <;>
    simp [sendB, hc0, hp, hc1, hst, ha]

/-- B version of `sendArleak_none_not_mem_support`. -/
theorem sendBrleak_none_not_mem_support
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : base.OnOffRandLeak onoff)
    (s : StB onoff Sym) :
    none ∉ support (sendBrleak base onoff ecCt0 ecCt1 leak s) := by
  intro h
  apply sendB_none_not_mem_support base onoff ecCt0 ecCt1 s
  rw [sendB_eq_map_sendBrleak base onoff ecCt0 ecCt1 leak s, support_map]
  exact ⟨none, h, rfl⟩

end oppUniKemCKA.Security.Embedding.Sampling

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding.Sampling

variable {K PK SK C Sym : Type}

/-- Query `t` from `s` runs source phase `phase` of epoch `e`: the party is at `e` without the
phase output, and `t` is its ordinary send or its leaking send with `e ∉ s.challenged`. -/
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

/-- `sourceUsed phase e` implies `usesSource phase e t s = false`. -/
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
      all_goals
        simp [usesSource]
        all_goals aesop
    all_goals
      simp [usesSource]
      all_goals aesop
  | offline =>
    have hno : ¬(s.stB.t = e ∧ s.stB.ct0.isNone) := by
      rintro ⟨ht, hp⟩
      cases hc : s.stB.ct0 <;> simp_all [sourceUsed]
    simp only [Option.isNone_iff_eq_none] at hno
    rcases t with (((((t | u) | u) | t) | u) | u)
    · rcases t with ((((n | u) | u) | n) | n)
      all_goals
        simp [usesSource]
        all_goals aesop
    all_goals
      simp [usesSource]
      all_goals aesop

variable [DecidableEq K] [DecidableEq Sym]

/-- If A is at `e`, every possible successor of A's ordinary send satisfies
`sourceUsed .keygen e`. -/
theorem oracleSendA_installs_source
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (he : s.stA.t = e)
    (z : Option (ℕ × Option ℕ × Message Sym) ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.oracleSendA (schemeAt ecEk ecCt0 ecCt1 stage kemMat e s) ()).run s)) :
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
      (stageKem stage kemMat e s) (stageOnOff stage kemMat e s) ecEk s.stA key msg epoch next hout
    cases key <;>
      simp only [StateT.run_bind, StateT.run_set, pure_bind,
        StateT.run_pure, mem_support_pure_iff] at hz
    all_goals obtain rfl := hz; exact Or.inr ⟨hshape.1.trans he, hshape.2⟩

/-- If A is at `e` without `dkA` and `e ∉ s.challenged`, A's leaking send stopped at the
exposure of `e` answers `none` on every path: the send is accepted and its coins expose `e`. -/
theorem leaking_keygen_stops
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (he : s.stA.t = e) (hfield : s.stA.dkA = none) (hc : e ∉ s.challenged)
    (z : Option (Option (ℕ × Option ℕ × Message Sym ×
      SendRand leak.KeygenRand leak.OffRand leak.OnRand)) ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support (((stopOnState
      (SCKAScheme.oracleSendArleak vulnRleakA (schemeAt ecEk ecCt0 ecCt1 stage kemMat e s))
      (fun s => decide (e ∈ s.exposed)) ()).run).run s)) : z.1 = none := by
  apply SCKAScheme.oracleSendArleak_stop_of_exposure _ _ s {e} e ?_ ?_ ?_
    (Finset.mem_singleton_self e) z hz
  · exact sendArleak_none_not_mem_support _ _ ecEk _ _
  · intro key msg epoch next coins hout
    have hex := sendArleak_exposure
      (stageKem stage kemMat e s) (stageOnOff stage kemMat e s) ecEk (stageLeak stage kemMat e s)
      s.stA key msg epoch next coins hout
    simpa only [leakEpochsA, hfield, Option.isNone_none,
      Bool.true_or, ↓reduceIte, he] using hex
  · simp [hc]

/-- B version of `oracleSendA_installs_source`, for `sourceUsed .offline e`. -/
theorem oracleSendB_installs_source
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (he : s.stB.t = e)
    (z : Option (ℕ × Option ℕ × Message Sym) ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.oracleSendB (schemeAt ecEk ecCt0 ecCt1 stage kemMat e s) ()).run s)) :
    sourceUsed .offline e z.2.stA z.2.stB := by
  simp only [SCKAScheme.oracleSendB, StateT.run_bind, StateT.run_get,
    StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
    mem_support_bind_iff] at hz
  obtain ⟨out, hout, hz⟩ := hz
  cases out with
  | none =>
    exact False.elim (sendB_none_not_mem_support
      (stageKem stage kemMat e s) (stageOnOff stage kemMat e s) ecCt0 ecCt1 _ hout)
  | some out =>
    rcases out with ⟨key, msg, epoch, next⟩
    have hshape := sendB_source_shape
      (stageKem stage kemMat e s) (stageOnOff stage kemMat e s) ecCt0 ecCt1 s.stB key msg epoch
      next hout
    cases key <;>
      simp only [StateT.run_bind, StateT.run_set, pure_bind,
        StateT.run_pure, mem_support_pure_iff] at hz
    all_goals obtain rfl := hz; exact Or.inr ⟨hshape.1.trans he, hshape.2⟩

/-- B version of `leaking_keygen_stops`, for B without `ct0`. -/
theorem leaking_offline_stops
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (he : s.stB.t = e) (hfield : s.stB.ct0 = none) (hc : e ∉ s.challenged)
    (z : Option (Option (ℕ × Option ℕ × Message Sym ×
      SendRand leak.KeygenRand leak.OffRand leak.OnRand)) ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support (((stopOnState
      (SCKAScheme.oracleSendBrleak vulnRleakB (schemeAt ecEk ecCt0 ecCt1 stage kemMat e s))
      (fun s => decide (e ∈ s.exposed)) ()).run).run s)) : z.1 = none := by
  apply SCKAScheme.oracleSendBrleak_stop_of_exposure _ _ s {e} e ?_ ?_ ?_
    (Finset.mem_singleton_self e) z hz
  · exact sendBrleak_none_not_mem_support
      (stageKem stage kemMat e s) (stageOnOff stage kemMat e s) ecCt0 ecCt1
      (stageLeak stage kemMat e s) _
  · intro key msg epoch next coins hout
    have hex := sendBrleak_exposure
      (stageKem stage kemMat e s) (stageOnOff stage kemMat e s) ecCt0 ecCt1
      (stageLeak stage kemMat e s) s.stB key msg epoch next coins hout
    simpa only [leakEpochsB, hfield, Option.isNone_none,
      Bool.true_or, ↓reduceIte, he] using hex
  · simp [hc]

variable [SampleableType K]

/-- If `usesSource phase e t s`, every possible successor of query `t` of `oracle stage kemMat e b`
with `e` unexposed satisfies `sourceUsed phase e`. -/
theorem oracle_first_source_use
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (stage : Stage) (kemMat : KEMMaterial leak) (e : ℕ) (b : Bool) (phase : SourcePhase)
    (t : (securitySpec leak Sym).Domain)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hh : usesSource phase e t s = true)
    (z : (securitySpec leak Sym).Range t ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support ((oracle base onoff ecEk ecCt0 ecCt1 leak stage kemMat e b t).run s))
    (hcont : decide (e ∈ z.2.exposed) = false) : sourceUsed phase e z.2.stA z.2.stB := by
  cases phase <;> rcases t with (((((t | u) | u) | t) | u) | u)
  all_goals try (rcases t with ((((n | u) | u) | n) | n))
  all_goals try (simp only [usesSource, Bool.false_eq_true] at hh)
  all_goals cases u
  · have hhit : s.stA.t = e ∧ s.stA.dkA.isNone := of_decide_eq_true hh
    change z ∈ support
      ((SCKAScheme.oracleSendA (schemeAt ecEk ecCt0 ecCt1 stage kemMat e s) ()).run s) at hz
    exact oracleSendA_installs_source base onoff ecEk ecCt0 ecCt1 leak
      stage kemMat e s hhit.1 z hz
  · have hhit : (s.stA.t = e ∧ s.stA.dkA.isNone) ∧ e ∉ s.challenged :=
      of_decide_eq_true hh
    change z ∈ support ((SCKAScheme.oracleSendArleak vulnRleakA
      (schemeAt ecEk ecCt0 ecCt1 stage kemMat e s) ()).run s) at hz
    have hstop := leaking_keygen_stops base onoff ecEk ecCt0 ecCt1 leak stage kemMat e s
      hhit.1.1 (Option.isNone_iff_eq_none.mp hhit.1.2) hhit.2 (some z.1, z.2)
      (mem_support_stopOnState_of_mem (SCKAScheme.oracleSendArleak vulnRleakA
        (schemeAt ecEk ecCt0 ecCt1 stage kemMat e s)) (fun s => decide (e ∈ s.exposed)) () s z hz
        hcont)
    exact absurd hstop (Option.some_ne_none _)
  · have hhit : s.stB.t = e ∧ s.stB.ct0.isNone := of_decide_eq_true hh
    change z ∈ support
      ((SCKAScheme.oracleSendB (schemeAt ecEk ecCt0 ecCt1 stage kemMat e s) ()).run s) at hz
    exact oracleSendB_installs_source base onoff ecEk ecCt0 ecCt1 leak
      stage kemMat e s hhit.1 z hz
  · have hhit : (s.stB.t = e ∧ s.stB.ct0.isNone) ∧ e ∉ s.challenged :=
      of_decide_eq_true hh
    change z ∈ support ((SCKAScheme.oracleSendBrleak vulnRleakB
      (schemeAt ecEk ecCt0 ecCt1 stage kemMat e s) ()).run s) at hz
    have hstop := leaking_offline_stops base onoff ecEk ecCt0 ecCt1 leak stage kemMat e s
      hhit.1.1 (Option.isNone_iff_eq_none.mp hhit.1.2) hhit.2 (some z.1, z.2)
      (mem_support_stopOnState_of_mem (SCKAScheme.oracleSendBrleak vulnRleakB
        (schemeAt ecEk ecCt0 ecCt1 stage kemMat e s)) (fun s => decide (e ∈ s.exposed)) () s z hz
        hcont)
    exact absurd hstop (Option.some_ne_none _)

end oppUniKemCKA.Security.Embedding.Sampling
