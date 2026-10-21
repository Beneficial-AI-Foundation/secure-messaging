/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.Concrete
import SecureMessaging.SCKA.MLKEMBraid.Security.Bounded

/-!
# Native no-authentication security

The native callbacks depend on the presend state and the actual send coins. Their transport
from the explicit-policy game is an all-input computation identity, including refusal and the
complete final state. The accepted reduction bounds therefore apply without new assumptions.
The support-qualified comparison with the paper's delta convention remains separate.
-/

open OracleSpec OracleComp ENNReal

namespace MLKEMBraid.NoAuth

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

private theorem oracleSendArleak_eq_native
    (P : Parameters ProbComp)
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc) :
    SCKAScheme.ExposurePolicy.oracleSendArleak
        (exposure P irl).send (scheme P hMac irl) =
      SCKAScheme.oracleSendArleak
        (nativeExposure P irl).rleak (scheme P hMac irl) := by
  rw [← (nativeExposure_eq_exposure P irl).2]
  rfl

private theorem oracleSendBrleak_eq_native
    (P : Parameters ProbComp)
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc) :
    SCKAScheme.ExposurePolicy.oracleSendBrleak
        (exposure P irl).send (scheme P hMac irl) =
      SCKAScheme.oracleSendBrleak
        (nativeExposure P irl).rleak (scheme P hMac irl) := by
  rw [← (nativeExposure_eq_exposure P irl).2]
  rfl

/-- Equality of the complete security interpreter for either bit and every query. -/
theorem securityImpl_eq_native
    (P : Parameters ProbComp)
    [SampleableType P.EpochKey] [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc) (b : Bool) :
    SCKAScheme.ExposurePolicy.sckaSecurityImpl b
        (exposure P irl) (exposure P irl) (scheme P hMac irl) =
      SCKAScheme.sckaSecurityImpl b
        (nativeExposure P irl) (nativeExposure P irl) (scheme P hMac irl) := by
  unfold SCKAScheme.ExposurePolicy.sckaSecurityImpl SCKAScheme.sckaSecurityImpl
  rw [oracleSendArleak_eq_native P hMac irl, oracleSendBrleak_eq_native P hMac irl,
    ← (nativeExposure_eq_exposure P irl).1]

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
    𝒟[SCKAScheme.ExposurePolicy.securityExp (scheme P hMac irl) A
        (exposure P irl) (exposure P irl)] =
      𝒟[SCKAScheme.securityExp (scheme P hMac irl) A
        (nativeExposure P irl) (nativeExposure P irl)] ∧
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

/-- The local predicate counts exactly the native security interface's four send queries. -/
theorem isSendQuery_eq_native
    (P : Parameters ProbComp) (irl : P.kem.IncrementalRandLeak P.inc)
    (t : (Spec P irl).Domain) :
    isSendQuery (P := P) (irl := irl) t =
      SCKAScheme.sckaSecuritySpec.isSendQuery t := by
  rcases t with (((((((((n | ⟨⟩) | ⟨⟩) | n) | n) | ⟨⟩) | ⟨⟩) | n) | ⟨⟩) | ⟨⟩) <;> rfl

/-- The existing budget counts ordinary and leaking sends, including refused queries. -/
theorem sendQueryBound_iff_native
    (P : Parameters ProbComp) (irl : P.kem.IncrementalRandLeak P.inc)
    (A : Adversary P irl) (qS : ℕ) :
    SendQueryBound A qS ↔
      A.IsQueryBoundP
        (fun t => SCKAScheme.sckaSecuritySpec.isSendQuery t = true) qS := by
  simp only [SendQueryBound, isSendQuery_eq_native P irl]

/-- The accepted reduction bound for the native no-authentication guessing advantage. -/
theorem security_le_native (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.K] [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct)
    (A : Adversary P irl) (qS : ℕ) (hqS : SendQueryBound A qS) :
    SCKAScheme.sckaGuessAdvantage (scheme P hMac irl) A
      (nativeExposure P irl) (nativeExposure P irl) ≤
      (∑ i ∈ Finset.range qS,
        (P.kem.IND_CPA_Advantage ProbCompRuntime.probComp
            (kemReduction P hMac irl A (i + 1)) +
          (kdfExp P (i + 1) (kdfReduction P hMac irl A (i + 1)) true).boolDistAdvantage
            (kdfExp P (i + 1) (kdfReduction P hMac irl A (i + 1)) false))) / 2 +
      (qS : ℝ) * (P.kem.correctnessError ProbCompRuntime.probComp).toReal := by
  rw [← (securityGame_equiv_native P hMac irl A).2]
  exact security_le P hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct A qS hqS

end MLKEMBraid.NoAuth

namespace MLKEMBraid

noncomputable section

/-- Native no-authentication security with abstract unrestricted-payload codecs. -/
theorem mlkemBraidScheme_noAuth_security_le_native
    (p : MLKEM.ParameterSet) (ring : MLKEM.NTTRingOps)
    (prims : MLKEM.Primitives (MLKEM.ParameterSet.params p)
      (MLKEM.Concrete.concreteEncoding (MLKEM.ParameterSet.params p)))
    {EpochKey Sym : Type} [SampleableType EpochKey] [DecidableEq EpochKey] [DecidableEq Sym]
    (kdfOK : MLKEM.SharedSecret → ℕ → EpochKey)
    (ecpHdr : ErasureCodePayload ((MLKEM.mlkemIncremental p ring prims).PKheader × Unit) Sym)
    (ecpEk : ErasureCodePayload (MLKEM.mlkemIncremental p ring prims).PKvector Sym)
    (ecpCt1 : ErasureCodePayload (MLKEM.mlkemIncremental p ring prims).C₁ Sym)
    (ecpCt2 : ErasureCodePayload ((MLKEM.mlkemIncremental p ring prims).C₂ × Unit) Sym)
    (hHdrCorrect : ecpHdr.ec.Correct) (hEkCorrect : ecpEk.ec.Correct)
    (hCt1Correct : ecpCt1.ec.Correct) (hCt2Correct : ecpCt2.ec.Correct)
    (A : NoAuth.Adversary (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2)
      (MLKEM.mlkemIncrementalRandLeak p ring prims))
    (qS : ℕ) (hqS : NoAuth.SendQueryBound A qS) :
    letI : SampleableType
        (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2).K :=
      inferInstanceAs (SampleableType MLKEM.SharedSecret)
    letI : SampleableType
        (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2).EpochKey :=
      inferInstanceAs (SampleableType EpochKey)
    letI : DecidableEq
        (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2).EpochKey :=
      inferInstanceAs (DecidableEq EpochKey)
    letI : DecidableEq
        (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2).Sym :=
      inferInstanceAs (DecidableEq Sym)
    SCKAScheme.sckaGuessAdvantage
        (mlkemBraidScheme p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2
          (NoAuth.auth (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2)
            (Eq.refl Unit)) (pure ()))
        A
        (NoAuth.nativeExposure
          (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2)
          (MLKEM.mlkemIncrementalRandLeak p ring prims))
        (NoAuth.nativeExposure
          (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2)
          (MLKEM.mlkemIncrementalRandLeak p ring prims)) ≤
      (∑ i ∈ Finset.range qS,
        ((MLKEM.mlkemScheme p ring prims).IND_CPA_Advantage ProbCompRuntime.probComp
            (NoAuth.kemReduction
              (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2)
              (Eq.refl Unit) (MLKEM.mlkemIncrementalRandLeak p ring prims) A (i + 1)) +
          (NoAuth.kdfExp (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2)
              (i + 1)
              (NoAuth.kdfReduction
                (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2)
                (Eq.refl Unit) (MLKEM.mlkemIncrementalRandLeak p ring prims) A (i + 1))
              true).boolDistAdvantage
            (NoAuth.kdfExp (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2)
              (i + 1)
              (NoAuth.kdfReduction
                (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2)
                (Eq.refl Unit) (MLKEM.mlkemIncrementalRandLeak p ring prims) A (i + 1))
              false))) / 2 +
      (qS : ℝ) * ((MLKEM.mlkemScheme p ring prims).correctnessError
        ProbCompRuntime.probComp).toReal := by
  let : SampleableType (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2).K :=
    inferInstanceAs (SampleableType MLKEM.SharedSecret)
  let : SampleableType
      (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2).EpochKey :=
    inferInstanceAs (SampleableType EpochKey)
  let : DecidableEq (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2).EpochKey :=
    inferInstanceAs (DecidableEq EpochKey)
  let : DecidableEq (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2).Sym :=
    inferInstanceAs (DecidableEq Sym)
  exact (le_of_eq (NoAuth.securityGame_equiv_native
    (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2)
    (Eq.refl Unit) (MLKEM.mlkemIncrementalRandLeak p ring prims) A).2.symm).trans
      (mlkemBraidScheme_noAuth_security_le p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2
        hHdrCorrect hEkCorrect hCt1Correct hCt2Correct A qS hqS)

/-- Native finite-payload no-authentication security, with reductions to raw ML-KEM. -/
theorem mlkemBraidBounded_noAuth_security_le_native
    (p : MLKEM.ParameterSet) (ring : MLKEM.NTTRingOps)
    (prims : MLKEM.Primitives (MLKEM.ParameterSet.params p)
      (MLKEM.Concrete.concreteEncoding (MLKEM.ParameterSet.params p)))
    {EpochKey : Type} [SampleableType EpochKey] [DecidableEq EpochKey]
    (kdfOK : MLKEM.SharedSecret → ℕ → EpochKey) :
    let P := MLKEMBraid.Bounded.parameters p ring prims kdfOK
    letI : SampleableType (MLKEMBraid.Bounded.parameters p ring prims kdfOK).K :=
      inferInstanceAs (SampleableType MLKEM.SharedSecret)
    letI : SampleableType (MLKEMBraid.Bounded.parameters p ring prims kdfOK).EpochKey :=
      inferInstanceAs (SampleableType EpochKey)
    letI : DecidableEq (MLKEMBraid.Bounded.parameters p ring prims kdfOK).EpochKey :=
      inferInstanceAs (DecidableEq EpochKey)
    letI : DecidableEq (MLKEMBraid.Bounded.parameters p ring prims kdfOK).Sym :=
      inferInstanceAs (DecidableEq
        (ErasureCode.SPQRReedSolomon.Chunk ErasureCode.SPQRReedSolomon.GF16))
    let irl := MLKEM.incrementalRandLeak ring
      (MLKEM.Bounded.encoding (MLKEM.ParameterSet.params p))
      (MLKEM.Bounded.primitives (MLKEM.ParameterSet.params p) prims)
    ∀ (A : MLKEMBraid.NoAuth.Adversary P irl) (qS : ℕ),
      MLKEMBraid.NoAuth.SendQueryBound A qS →
      SCKAScheme.sckaGuessAdvantage
        (MLKEMBraid.NoAuth.scheme P (Eq.refl Unit) irl) A
        (MLKEMBraid.NoAuth.nativeExposure P irl)
        (MLKEMBraid.NoAuth.nativeExposure P irl) ≤
        (∑ i ∈ Finset.range qS,
          ((MLKEM.mlkemScheme p ring prims).IND_CPA_Advantage
              ProbCompRuntime.probComp
              (MLKEM.Bounded.liftAdversary p ring prims
                (MLKEMBraid.NoAuth.kemReduction P (Eq.refl Unit) irl A (i + 1))) +
            (MLKEMBraid.NoAuth.kdfExp P (i + 1)
              (MLKEMBraid.NoAuth.kdfReduction P (Eq.refl Unit) irl A
                (i + 1)) true).boolDistAdvantage
              (MLKEMBraid.NoAuth.kdfExp P (i + 1)
                (MLKEMBraid.NoAuth.kdfReduction P (Eq.refl Unit) irl A (i + 1)) false))) / 2 +
        (qS : ℝ) *
          ((MLKEM.mlkemScheme p ring prims).correctnessError
            ProbCompRuntime.probComp).toReal := by
  intro P irl A qS hqS
  let : SampleableType (MLKEMBraid.Bounded.parameters p ring prims kdfOK).K :=
    inferInstanceAs (SampleableType MLKEM.SharedSecret)
  let : SampleableType (MLKEMBraid.Bounded.parameters p ring prims kdfOK).EpochKey :=
    inferInstanceAs (SampleableType EpochKey)
  let : DecidableEq (MLKEMBraid.Bounded.parameters p ring prims kdfOK).EpochKey :=
    inferInstanceAs (DecidableEq EpochKey)
  let : DecidableEq (MLKEMBraid.Bounded.parameters p ring prims kdfOK).Sym :=
    inferInstanceAs (DecidableEq
      (ErasureCode.SPQRReedSolomon.Chunk ErasureCode.SPQRReedSolomon.GF16))
  exact (le_of_eq (NoAuth.securityGame_equiv_native P (Eq.refl Unit) irl A).2.symm).trans
    (mlkemBraidBounded_noAuth_security_le p ring prims kdfOK A qS hqS)

end

end MLKEMBraid
