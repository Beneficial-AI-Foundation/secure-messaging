/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.SamplingStages
import SecureMessaging.SCKA.Security.LocalInvariant

/-!
# Single use of source samples within an epoch

**Predicate.** A selected source phase is used once its party has either
advanced beyond the selected epoch or installed that phase's output there.
The relevant fields are A's decapsulation key and B's offline ciphertext.

**Preservation.** Every sampling-stage query preserves this predicate.
Sends retain their epoch and install the relevant field. Receives either
retain both epoch and field or advance the epoch, as proved in correctness.
Challenge, corruption, and leakage bookkeeping preserve the local-state
property. These facts provide the used-state premise for lazy sampling.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding.Sampling

variable {K PK SK C Sym : Type}

/-- The two source phases whose samplers have no protocol-state input. -/
inductive SourcePhase where
  /-- A's generation of the epoch key pair. -/
  | keygen
  /-- B's offline encapsulation for the epoch. -/
  | offline
  deriving DecidableEq

/-- Phase `phase` at epoch `e` has been used if its party has advanced past
`e`, or is at `e` with the phase output installed in its local state. -/
def sourceUsed {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (phase : SourcePhase) (e : ℕ) (a : StA onoff Sym) (b : StB onoff Sym) : Prop :=
  match phase with
  | .keygen => e < a.t ∨ (a.t = e ∧ a.dkA.isSome)
  | .offline => e < b.t ∨ (b.t = e ∧ b.ct0.isSome)

/-- Every supported successful A-send retains A's epoch and leaves a
present decapsulation key, for any KEM and input local state. -/
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

set_option maxHeartbeats 800000 in
-- The branch split includes combined offline/online encapsulation.
/-- Every supported successful B-send retains B's epoch and leaves a
present offline ciphertext, for any KEM and input local state. -/
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

/-- For every sampling stage, source phase, epoch, and input state where
that phase has been used, every correctness query preserves its used status. -/
theorem correctness_preserves_sourceUsed
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (stage : Stage) (m : Material leak) (e : ℕ) (phase : SourcePhase)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : sourceUsed phase e s.stA s.stB)
    (t : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Domain)
    (z : (SCKAScheme.sckaCorrectnessSpec (Message Sym)).Range t ×
      SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hz : z ∈ support
      ((SCKAScheme.sckaCorrectnessImpl (schemeAt ecEk ecCt0 ecCt1 stage m e s) t).run s)) :
    sourceUsed phase e z.2.stA z.2.stB := by
  apply SCKAScheme.correctnessImpl_preserves_localInv_at _ (sourceUsed phase e) s hs
    ?_ ?_ ?_ ?_ t z hz
  · intro key msg epoch next hout
    have hshape := sendA_source_shape
      (kem m (stage.pinsKeygen && decide (s.stA.t = e))
        (stage.pinsOffline && decide (s.stB.t = e))
        (stage.pinsOnline && decide (s.stB.t = e)) (s.keyB s.stA.t))
      (onOff m _ _ _ _) ecEk s.stA key msg epoch next hout
    cases phase with
    | keygen =>
      rcases hs with h | ⟨h, _⟩
      · exact Or.inl (by simpa only [hshape.1] using h)
      · exact Or.inr ⟨hshape.1.trans h, hshape.2⟩
    | offline => exact hs
  · intro key msg epoch next hout
    have hshape := sendB_source_shape
      (kem m (stage.pinsKeygen && decide (s.stA.t = e))
        (stage.pinsOffline && decide (s.stB.t = e))
        (stage.pinsOnline && decide (s.stB.t = e)) (s.keyB s.stA.t))
      (onOff m _ _ _ _) ecCt0 ecCt1 s.stB key msg epoch next hout
    cases phase with
    | keygen => exact hs
    | offline =>
      rcases hs with h | ⟨h, _⟩
      · exact Or.inl (by simpa only [hshape.1] using h)
      · exact Or.inr ⟨hshape.1.trans h, hshape.2⟩
  · intro msg key epoch next hout
    rw [recvA_eq_auxiliary] at hout
    have hshape := oppUniKemCKA.Reduction.Internal.recvA_kem_source_shape
      (keyDecapsKEM base (s.keyB s.stA.t))
      (keyDecapsOnOff base onoff (s.keyB s.stA.t))
      (keyDecapsDet base (s.keyB s.stA.t)) ecCt0 ecCt1 s.stA msg key epoch next hout
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

/-- For every stage, material value, selected epoch, and source phase, all
security queries preserve the phase's used status. Leaking sends use their
ordinary-send marginals; guards and exposure updates retain this predicate. -/
theorem oracle_preserves_sourceUsed [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (stage : Stage) (m : Material leak) (e : ℕ) (b : Bool) (phase : SourcePhase) :
    QueryImpl.PreservesInv (oracle base onoff ecEk ecCt0 ecCt1 leak stage m e b)
      (fun s => sourceUsed phase e s.stA s.stB) := by
  intro t s hs z hz
  simp only [oracle, StateT.run_bind, StateT.run_get, pure_bind] at hz
  rcases t with (((((t | u) | u) | t) | u) | u)
  · exact correctness_preserves_sourceUsed base onoff ecEk ecCt0 ecCt1 leak
      stage m e phase s hs t z hz
  · cases u
    apply SCKAScheme.oracleSendArleak_preservesInv_at
      (schemeAt ecEk ecCt0 ecCt1 stage m e s) sendExposureA _
      (fun s => sourceUsed phase e s.stA s.stB) (fun _ _ h => h) s hs _ z hz
    · exact sendArleak_forget _ _ _ _
    · exact correctness_preserves_sourceUsed base onoff ecEk ecCt0 ecCt1 leak
        stage m e phase s hs SCKAScheme.sckaCorrectnessSpec.OSendA
  · cases u
    apply SCKAScheme.oracleSendBrleak_preservesInv_at
      (schemeAt ecEk ecCt0 ecCt1 stage m e s) sendExposureB _
      (fun s => sourceUsed phase e s.stA s.stB) (fun _ _ h => h) s hs _ z hz
    · exact sendBrleak_forget _ _ _ _ _
    · exact correctness_preserves_sourceUsed base onoff ecEk ecCt0 ecCt1 leak
        stage m e phase s hs SCKAScheme.sckaCorrectnessSpec.OSendB
  · exact SCKAScheme.oracleChall_preservesInv (adjacentMode e b t)
      (fun s => sourceUsed phase e s.stA s.stB) (fun _ _ h => h) t s hs z hz
  · exact SCKAScheme.oracleCorruptA_preservesInv (vulnA base onoff)
      (fun s => sourceUsed phase e s.stA s.stB) (fun _ _ h => h) u s hs z hz
  · exact SCKAScheme.oracleCorruptB_preservesInv (vulnB base onoff)
      (fun s => sourceUsed phase e s.stA s.stB) (fun _ _ h => h) u s hs z hz

end oppUniKemCKA.Security.Embedding.Sampling
