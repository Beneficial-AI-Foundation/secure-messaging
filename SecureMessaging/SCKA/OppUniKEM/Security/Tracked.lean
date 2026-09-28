/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Invariant
import SecureMessaging.SCKA.OppUniKEM.Correctness.Reduction.Projection

/-!
# Persistent KEM-failure tracking

**Construction.** Fix a challenge bit `b`. A tracked state is `(s, bad)`,
where `s` is the SCKA state. Each query returns the ordinary response and
updates `bad' = bad || currentKEMFailure(s')`. The test detects disagreement
between decapsulation and the current completed epoch's encapsulated key.

**Results.** For every adaptive computation and initial tracked state,
projecting away `bad` recovers the ordinary output/state computation.
With correct erasure codes, every query preserves `trackedInv`, defined by
`bad = true ∨ (reachableInv s ∧ currentKEMFailure(s) = false)`.

**Proof.** The projection follows from the flag update. Preservation follows
from `Invariant` while `bad = false`, and persistence once `bad = true`.
`FailureBound` bounds this flag's probability; `Endpoints` uses it to compare
real and auxiliary experiments.
-/

open OracleSpec OracleComp KEMScheme ENNReal

namespace oppUniKemCKA.Security

open Reduction.Internal

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- The fixed-bit security oracle with a persistent failure flag. After
each query, `bad` is set if decapsulation of the current completed epoch
disagrees with its encapsulated key. All answers and original state fields
are those of the ordinary security game. -/
def trackedSecurityImpl
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : kem.OnOffRandLeak onoff) (b : Bool) :
    QueryImpl (securitySpec leak Sym)
      (StateT
        (SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) × Bool)
        ProbComp) :=
  fun t p => do
    let z ← (SCKAScheme.sckaSecurityImpl b (exposureA kem onoff leak) (exposureB kem onoff leak)
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) t).run p.1
    pure (z.1, (z.2, p.2 || currentKEMFailure kem onoff hDet z.2))

/-- Removing the persistent failure flag after one tracked security query
recovers the complete ordinary response and game state. -/
theorem trackedSecurityImpl_project
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : kem.OnOffRandLeak onoff) (b : Bool)
    (t : (securitySpec leak Sym).Domain)
    (p : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) × Bool) :
    Prod.map id Prod.fst <$>
        (trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b t).run p =
      (SCKAScheme.sckaSecurityImpl b (exposureA kem onoff leak) (exposureB kem onoff leak)
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) t).run p.1 := by
  simp [trackedSecurityImpl, StateT.run, monad_norm]

/-- Removing the failure flag from a complete tracked execution recovers
the fixed-bit security execution, including its adversary output. -/
theorem trackedSecurity_run_project
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : kem.OnOffRandLeak onoff) (b : Bool)
    {α : Type} (adv : OracleComp (securitySpec leak Sym) α)
    (p : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym) × Bool) :
    Prod.map id Prod.fst <$>
        (simulateQ (trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b) adv).run p =
      (simulateQ (SCKAScheme.sckaSecurityImpl b (exposureA kem onoff leak)
        (exposureB kem onoff leak)
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak)) adv).run p.1 := by
  exact map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst
    (trackedSecurityImpl_project kem onoff hDet ecEk ecCt0 ecCt1 leak b) adv p

/-- Correct erasure codes make the full tracked oracle preserve the
correctness invariant: either a KEM failure has been recorded, or a
consistent transcript exists and the current epoch is KEM-correct. -/
theorem trackedSecurityImpl_preserves
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym) (hEk : ecEk.ec.Correct)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym) (hCt0 : ecCt0.ec.Correct)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (hCt1 : ecCt1.ec.Correct)
    (leak : kem.OnOffRandLeak onoff) (b : Bool) :
    QueryImpl.PreservesInv (trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b)
      (trackedInv kem onoff hDet ecEk ecCt0 ecCt1) := by
  intro t p hp z hz
  change z ∈ support (do
    let y ← (SCKAScheme.sckaSecurityImpl b (exposureA kem onoff leak) (exposureB kem onoff leak)
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) t).run p.1
    pure (y.1, (y.2, p.2 || currentKEMFailure kem onoff hDet y.2))) at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  simp only [mem_support_pure_iff] at hz
  subst z
  rcases hp with hbad | ⟨hreach, hfail⟩
  · left
    simp [hbad]
  have hc := currentKEMFailure_eq_false_implies_current kem onoff hDet ecEk ecCt0 ecCt1
    p.1 hreach hfail
  have hreach' := securityImpl_preserves_reachableInv kem onoff hDet ecEk hEk
    ecCt0 hCt0 ecCt1 hCt1 leak b t p.1 hreach hc y hy
  cases hbad : currentKEMFailure kem onoff hDet y.2
  · exact Or.inr ⟨hreach', hbad⟩
  · exact Or.inl (by simp)

end oppUniKemCKA.Security
