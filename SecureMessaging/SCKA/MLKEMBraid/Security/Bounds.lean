/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.Security
import SecureMessaging.SCKA.MLKEMBraid.Security.Games

/-!
# The native exposure functions

`nativeExposure` states the exposure rules of the security game as the generic SCKA interface
expects them: from the state before a send and the coins of that send. With these functions the
generic security game is the same computation as the explicit-policy game, for either bit and
every query (`securityImpl_eq_native`, `fixed_eq_native`, `securityGame_equiv_native`).
-/

open OracleSpec OracleComp ENNReal

namespace MLKEMBraid.NoAuth

variable {P : Parameters ProbComp}

/-- Native state-corruption and send-coin exposure for the unit-authenticator instance. -/
def nativeExposure (P : Parameters ProbComp)
    (irl : P.kem.IncrementalRandLeak P.inc) :
    SCKAScheme.VulnerableEpochs (State P Unit)
      (SendRand irl.KeygenRand irl.Encaps1Rand) where
  corrupt := vuln
  rleak := fun st coins => sendExposure st st coins

/-- The explicit send policy ignores its poststate, on all inputs. -/
theorem nativeExposure_eq_exposure
    (P : Parameters ProbComp) (irl : P.kem.IncrementalRandLeak P.inc) :
    (nativeExposure P irl).corrupt = (exposure P irl).corrupt ∧
      (fun (st _st' : State P Unit)
        (coins : SendRand irl.KeygenRand irl.Encaps1Rand) =>
          (nativeExposure P irl).rleak st coins) = (exposure P irl).send := by
  exact ⟨rfl, rfl⟩

/-- Equality of the complete security interpreter for either bit and every query. -/
theorem securityImpl_eq_native
    (P : Parameters ProbComp)
    [SampleableType P.EpochKey] [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc) (b : Bool) :
    SCKAScheme.ExposurePolicy.sckaSecurityImpl b
        (exposure P irl) (exposure P irl) (scheme P hMac irl) =
      SCKAScheme.sckaSecurityImpl b
        (nativeExposure P irl) (nativeExposure P irl) (scheme P hMac irl) := by
  rfl

/-- Equality of the joint response and complete final-state computation from any initial state. -/
theorem security_run_eq_native
    (P : Parameters ProbComp)
    [SampleableType P.EpochKey] [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (b : Bool) (A : Adversary P irl) (s : MLKEMBraid.GameState P Unit) :
    (simulateQ (SCKAScheme.ExposurePolicy.sckaSecurityImpl b
      (exposure P irl) (exposure P irl) (scheme P hMac irl)) A).run s =
    (simulateQ (SCKAScheme.sckaSecurityImpl b
      (nativeExposure P irl) (nativeExposure P irl)
      (scheme P hMac irl)) A).run s := by
  rw [securityImpl_eq_native P hMac irl b]

/-- The initialized fixed-bit native experiment returns the adversary's raw guess. -/
theorem fixed_eq_native
    (P : Parameters ProbComp)
    [SampleableType P.EpochKey] [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (A : Adversary P irl) (b : Bool) :
    fixed P hMac irl A b =
      SCKAScheme.securityExpFixedBit (scheme P hMac irl) A b
        (nativeExposure P irl) (nativeExposure P irl) := by
  have h1 : (scheme P hMac irl).initKeyGen = pure () := rfl
  have h2 : ∀ ik, (scheme P hMac irl).initA ik = pure (MLKEMBraid.initA P (auth P hMac) ik) :=
    fun _ => rfl
  have h3 : ∀ ik, (scheme P hMac irl).initB ik = pure (MLKEMBraid.initB P (auth P hMac) ik) :=
    fun _ => rfl
  simp only [SCKAScheme.securityExpFixedBit, h1, h2, h3, pure_bind]
  rw [← security_run_eq_native P hMac irl b A _]
  simp only [fixed, StateT.run'_eq, map_eq_bind_pure_comp]
  rfl

/-- Initialized sampled-bit experiment and guessing-advantage transport. -/
theorem securityGame_equiv_native
    (P : Parameters ProbComp)
    [SampleableType P.EpochKey] [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (A : Adversary P irl) :
    SCKAScheme.ExposurePolicy.securityExp (scheme P hMac irl) A
        (exposure P irl) (exposure P irl) =ᵈ SCKAScheme.securityExp (scheme P hMac irl) A
        (nativeExposure P irl) (nativeExposure P irl) ∧
    SCKAScheme.ExposurePolicy.sckaGuessAdvantage (scheme P hMac irl) A
        (exposure P irl) (exposure P irl) =
      SCKAScheme.sckaGuessAdvantage (scheme P hMac irl) A
        (nativeExposure P irl) (nativeExposure P irl) := by
  have hexp : SCKAScheme.ExposurePolicy.securityExp (scheme P hMac irl) A
      (exposure P irl) (exposure P irl) =
      SCKAScheme.securityExp (scheme P hMac irl) A
        (nativeExposure P irl) (nativeExposure P irl) := by
    simp only [SCKAScheme.ExposurePolicy.securityExp, SCKAScheme.securityExp,
      securityImpl_eq_native P hMac irl]
  constructor
  · rw [hexp]
  · simp only [SCKAScheme.ExposurePolicy.sckaGuessAdvantage,
      SCKAScheme.sckaGuessAdvantage, hexp]

end MLKEMBraid.NoAuth
