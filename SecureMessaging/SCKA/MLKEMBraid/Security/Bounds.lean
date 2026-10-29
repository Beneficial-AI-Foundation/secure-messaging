/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.EvalDist.BoolDist
import SecureMessaging.SCKA.Security
import SecureMessaging.SCKA.MLKEMBraid.Security.Risk
import SecureMessaging.SCKA.MLKEMBraid.Security.Hybrids
import SecureMessaging.SCKA.MLKEMBraid.Security.Reduction.KEM
import SecureMessaging.SCKA.MLKEMBraid.Security.Reduction.KDF

/-!
# The no-authentication reduction bound

The hidden-bit guessing advantage is half the fixed-bit distinguishing advantage. Repaired
endpoint hybrids and adjacent KEM/KDF gaps give the reduction sum; the real/repaired comparison
adds the unchanged correctness-error loss. No primitive hardness or efficiency premise is added.
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

/-- **`security_le`**: the explicit-policy guessing advantage of a no-authentication Braid
adversary making at most `qS` sends is at most half the sum, over the epochs `1, …, qS`, of the
IND-CPA advantage of `kemReduction` and the uniform-input KDF advantage of `kdfReduction`, plus
`qS` times the KEM correctness error. -/
theorem security_le (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.K] [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct)
    (A : Adversary P irl) (qS : ℕ) (hqS : SendQueryBound A qS) :
    SCKAScheme.ExposurePolicy.sckaGuessAdvantage (scheme P hMac irl) A
      (exposure P irl) (exposure P irl) ≤
      (∑ i ∈ Finset.range qS,
        ((P.kem.IND_CPA_Advantage ProbCompRuntime.probComp
            (kemReduction P hMac irl A (i + 1))).toReal +
          (𝒟[kdfExp P (i + 1) (kdfReduction P hMac irl A (i + 1)) true].boolDist
              𝒟[kdfExp P (i + 1) (kdfReduction P hMac irl A (i + 1)) false]).toReal)) / 2 +
      (qS : ℝ) * (P.kem.correctnessError ProbCompRuntime.probComp).toReal := by
  have hcE : P.kem.correctnessError ProbCompRuntime.probComp ≠ ⊤ :=
    ENNReal.sub_ne_top ENNReal.one_ne_top
  have hbad : ∀ b : Bool, (𝒟[fixed P hMac irl A b].boolDist
      𝒟[Prod.fst <$> run P hMac irl true (fun _ => if b then .uniform else .real) A]).toReal ≤
        (qS : ℝ) * (P.kem.correctnessError ProbCompRuntime.probComp).toReal := by
    intro b
    refine (fixed_repaired_gap_le P hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct A
      b).trans ?_
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top qS) hcE)
      (badEvent_le P hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct A qS hqS b)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h
  have hend := hybrid_endpoints P hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct A qS
    hqS
  have h0 := hend.1.prEvent_eq (fun x => x = true)
  have hq := hend.2.prEvent_eq (fun x => x = true)
  have hstep : ∀ i, |(Pr{let x ← hybrid P hMac irl A (i + 1)}[x = true]).toReal -
      (Pr{let x ← hybrid P hMac irl A i}[x = true]).toReal| ≤
      (P.kem.IND_CPA_Advantage ProbCompRuntime.probComp
          (kemReduction P hMac irl A (i + 1))).toReal +
        (𝒟[kdfExp P (i + 1) (kdfReduction P hMac irl A (i + 1)) true].boolDist
            𝒟[kdfExp P (i + 1) (kdfReduction P hMac irl A (i + 1)) false]).toReal := by
    intro i
    have hk := kem_gap_eq P hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct A (i + 1)
      (Nat.succ_pos i)
    rw [Nat.add_sub_cancel] at hk
    rw [← hk, ← kdf_gap_eq P hMac irl A (i + 1) (Nat.succ_pos i), abs_sub_comm,
      ToVCVio.toReal_boolDist_evalDist, ToVCVio.toReal_boolDist_evalDist]
    exact abs_sub_le _ _ _
  have hs := Finset.sum_range_sub (fun i => (Pr{let x ← hybrid P hMac irl A i}[x = true]).toReal) qS
  have htel : |(Pr{let x ← hybrid P hMac irl A qS}[x = true]).toReal -
      (Pr{let x ← hybrid P hMac irl A 0}[x = true]).toReal| ≤
      ∑ i ∈ Finset.range qS,
        ((P.kem.IND_CPA_Advantage ProbCompRuntime.probComp
            (kemReduction P hMac irl A (i + 1))).toReal +
          (𝒟[kdfExp P (i + 1) (kdfReduction P hMac irl A (i + 1)) true].boolDist
              𝒟[kdfExp P (i + 1) (kdfReduction P hMac irl A (i + 1)) false]).toReal) := by
    rw [← hs]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hstep i)
  have h1 := hbad true
  have h2 := hbad false
  rw [ToVCVio.toReal_boolDist_evalDist] at h1 h2
  rw [← hq] at h1
  rw [← h0] at h2
  rw [(securityGame_equiv_native P hMac irl A).2,
    SCKAScheme.sckaGuessAdvantage_eq_sckaDistAdvantage_div_two]
  unfold SCKAScheme.sckaDistAdvantage
  rw [← fixed_eq_native P hMac irl A true, ← fixed_eq_native P hMac irl A false]
  have ha := abs_sub_le (Pr{let x ← fixed P hMac irl A true}[x = true]).toReal
    (Pr{let x ← hybrid P hMac irl A qS}[x = true]).toReal (Pr{let x ← fixed P hMac irl A false}[x =
        true]).toReal
  have hb := abs_sub_le (Pr{let x ← hybrid P hMac irl A qS}[x = true]).toReal
    (Pr{let x ← hybrid P hMac irl A 0}[x = true]).toReal (Pr{let x ← fixed P hMac irl A false}[x =
        true]).toReal
  rw [abs_sub_comm (Pr{let x ← hybrid P hMac irl A 0}[x = true]).toReal] at hb
  linarith

/-- The bound of `security_le` for the historical delta game, encoded by `deltaExposure`. -/
theorem security_le_delta (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.K] [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct)
    (A : Adversary P irl) (qS : ℕ) (hqS : SendQueryBound A qS) :
    SCKAScheme.ExposurePolicy.sckaGuessAdvantage (scheme P hMac irl) A
      (deltaExposure P irl) (deltaExposure P irl) ≤
      (∑ i ∈ Finset.range qS,
        ((P.kem.IND_CPA_Advantage ProbCompRuntime.probComp
            (kemReduction P hMac irl A (i + 1))).toReal +
          (𝒟[kdfExp P (i + 1) (kdfReduction P hMac irl A (i + 1)) true].boolDist
              𝒟[kdfExp P (i + 1) (kdfReduction P hMac irl A (i + 1)) false]).toReal)) / 2 +
      (qS : ℝ) * (P.kem.correctnessError ProbCompRuntime.probComp).toReal := by
  rw [← (securityGame_equiv_delta P hMac irl A).2]
  exact security_le P hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct A qS hqS

end MLKEMBraid.NoAuth
