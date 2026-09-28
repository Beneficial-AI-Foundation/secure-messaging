/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Tracked
import SecureMessaging.SCKA.OppUniKEM.Security.Leakage
import SecureMessaging.SCKA.Security.LeakageScore

/-!
# Failure-score bounds for leaking sends

**Notation.** Let `Φ = trackedFailureScore` be the correctness proof's
potential on pairs `(s, bad)`, and `ε = factorCorrectnessError kem onoff`
the correctness error of factored encapsulation.

**Statement.** For each party's leaking-send oracle, every fixed challenge
bit, and every state `s` satisfying `reachableInv` and
`currentKEMFailure(s) = false`,
`E[Φ(s', bad')] ≤ Φ(s, false) + ε`.

**Proof.** `Leakage` identifies one exposure set for all supported successful
samples from `s`. The guard therefore accepts all such samples or rejects
all of them. Acceptance transfers the ordinary-send bound through the
coin-forgetting marginal; rejection retains the current score. `OneStep`
combines these results with the ordinary-send bounds.
-/

open OracleSpec OracleComp KEMScheme ENNReal

namespace oppUniKemCKA.Security

open Reduction.Internal

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]

/-- For every fixed bit and state `s` satisfying `reachableInv` and
`currentKEMFailure(s) = false`, A's leaking send from `(s, false)` has
expected tracked failure score at most its initial score plus
`factorCorrectnessError kem onoff`. -/
theorem tracked_sendArleak_score_le
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : kem.OnOffRandLeak onoff) (b : Bool)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (hf : currentKEMFailure kem onoff hDet s = false) :
    expectedPayoff
      ((trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b
        SCKAScheme.sckaSecuritySpec.OSendArleak).run (s, false))
      (fun z => trackedFailureScore kem onoff z.2) ≤
      trackedFailureScore kem onoff (s, false) + factorCorrectnessError kem onoff := by
  change expectedPayoff (do
    let y ← (SCKAScheme.oracleSendArleak sendExposureA
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s
    pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2))) _ ≤ _
  rw [bind_pure_comp, expectedPayoff_map]
  apply SCKAScheme.oracleSendArleak_expectedPayoff_le
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) sendExposureA
      (sendArleak_forget kem onoff ecEk leak) s (leakEpochsA s.stA)
      (score := fun state => trackedFailureScore kem onoff
        (state, false || currentKEMFailure kem onoff hDet state))
      (c := trackedFailureScore kem onoff (s, false) + factorCorrectnessError kem onoff)
  · intro key msg epoch state coins hout
    exact sendArleak_exposure kem onoff ecEk leak s.stA
      _ hout key msg epoch state coins rfl
  · intro state exposed
    rfl
  · simp [hf]
  · have h := tracked_sendA_score_le kem onoff hDet ecEk ecCt0 ecCt1 leak s hs hf
    change expectedPayoff (do
      let y ← (SCKAScheme.oracleSendA
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s
      pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2))) _ ≤ _ at h
    simpa only [bind_pure_comp, expectedPayoff_map] using h

/-- For every fixed bit and state `s` satisfying `reachableInv` and
`currentKEMFailure(s) = false`, B's leaking send from `(s, false)` has
expected tracked failure score at most its initial score plus
`factorCorrectnessError kem onoff`. -/
theorem tracked_sendBrleak_score_le
    (kem : KEMScheme ProbComp K PK SK C) (onoff : kem.OnOffStructure)
    (hDet : DeterministicDecaps kem)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym)
    (leak : kem.OnOffRandLeak onoff) (b : Bool)
    (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym))
    (hs : reachableInv kem onoff ecEk ecCt0 ecCt1 s)
    (hf : currentKEMFailure kem onoff hDet s = false) :
    expectedPayoff
      ((trackedSecurityImpl kem onoff hDet ecEk ecCt0 ecCt1 leak b
        SCKAScheme.sckaSecuritySpec.OSendBrleak).run (s, false))
      (fun z => trackedFailureScore kem onoff z.2) ≤
      trackedFailureScore kem onoff (s, false) + factorCorrectnessError kem onoff := by
  change expectedPayoff (do
    let y ← (SCKAScheme.oracleSendBrleak sendExposureB
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s
    pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2))) _ ≤ _
  rw [bind_pure_comp, expectedPayoff_map]
  apply SCKAScheme.oracleSendBrleak_expectedPayoff_le
      (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) sendExposureB
      (sendBrleak_forget kem onoff ecCt0 ecCt1 leak) s (leakEpochsB s.stB)
      (score := fun state => trackedFailureScore kem onoff
        (state, false || currentKEMFailure kem onoff hDet state))
      (c := trackedFailureScore kem onoff (s, false) + factorCorrectnessError kem onoff)
  · intro key msg epoch state coins hout
    exact sendBrleak_exposure kem onoff ecCt0 ecCt1 leak s.stB
      _ hout key msg epoch state coins rfl
  · intro state exposed
    rfl
  · simp [hf]
  · have h := tracked_sendB_score_le kem onoff hDet ecEk ecCt0 ecCt1 leak s hs hf
    change expectedPayoff (do
      let y ← (SCKAScheme.oracleSendB
        (scheme kem onoff hDet ecEk ecCt0 ecCt1 leak) ()).run s
      pure (y.1, (y.2, false || currentKEMFailure kem onoff hDet y.2))) _ ≤ _ at h
    simpa only [bind_pure_comp, expectedPayoff_map] using h

end oppUniKemCKA.Security
