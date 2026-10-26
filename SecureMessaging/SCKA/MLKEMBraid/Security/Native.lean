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
