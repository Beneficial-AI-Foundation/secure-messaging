/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.Bounds
import SecureMessaging.SCKA.MLKEMBraid.BoundedInstances

/-!
# Finite-payload security

Bounded bytes admit universally roundtripping finite-symbol codecs. They do not instantiate
the separate unrestricted-ByteArray theorem. Byte refinements connect bounded ML-KEM to the
existing raw algorithms and retain their joint randomness.

The supplied primitive convention hashes vector before seed; the Braid PDF writes seed before
vector. No hash-order equality is claimed. Supplied ring and primitive functions do not establish
SHA-3/SHAKE semantics for opaque externs. No C/FFI, implemented NTT-loop, entropy failure,
capped-sampler panic, constant-time or physical-erasure correspondence is proved. Numerical
FIPS bounds still require NTTRingLaws and CoefficientFailureBound. The abstract SPQR field
representation is not a runtime byte-layout or complexity theorem. No primitive/KDF hardness,
efficient/QPT adversary class, authenticated security or messaging composition is added.
-/

open OracleSpec OracleComp ENNReal

namespace MLKEMBraid

noncomputable section

-- The finite-symbol parameter transports make elaboration of this endpoint expensive.
/-- No-authentication security with finite payload codecs and reductions to raw ML-KEM. -/
theorem mlkemBraidBounded_noAuth_security_le
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
      SCKAScheme.ExposurePolicy.sckaGuessAdvantage
        (MLKEMBraid.NoAuth.scheme P (Eq.refl Unit) irl) A
        (MLKEMBraid.NoAuth.exposure P irl)
        (MLKEMBraid.NoAuth.exposure P irl) ≤
        (∑ i ∈ Finset.range qS,
          (((MLKEM.mlkemScheme p ring prims).IND_CPA_Advantage
              ProbCompRuntime.probComp
              (MLKEM.Bounded.liftAdversary p ring prims
                (MLKEMBraid.NoAuth.kemReduction P (Eq.refl Unit) irl A (i + 1)))).toReal +
            (𝒟[MLKEMBraid.NoAuth.kdfExp P (i + 1)
              (MLKEMBraid.NoAuth.kdfReduction P (Eq.refl Unit) irl A
                (i + 1)) true].boolDist 𝒟[MLKEMBraid.NoAuth.kdfExp P (i + 1)
                (MLKEMBraid.NoAuth.kdfReduction P (Eq.refl Unit) irl A (i + 1)) false]).toReal)) /
          2 +
        (qS : ℝ) *
          ((MLKEM.mlkemScheme p ring prims).correctnessError
            ProbCompRuntime.probComp).toReal := by
  intro P irl A qS hqS
  let : SampleableType (MLKEMBraid.Bounded.parameters p ring prims kdfOK).K :=
    inferInstanceAs (SampleableType MLKEM.SharedSecret)
  let : SampleableType (MLKEMBraid.Bounded.parameters p ring prims kdfOK).EpochKey :=
    inferInstanceAs (SampleableType EpochKey)
  let : DecidableEq (MLKEMBraid.Bounded.parameters p ring prims kdfOK).K :=
    inferInstanceAs (DecidableEq MLKEM.SharedSecret)
  let : DecidableEq (MLKEMBraid.Bounded.parameters p ring prims kdfOK).EpochKey :=
    inferInstanceAs (DecidableEq EpochKey)
  let : DecidableEq (MLKEMBraid.Bounded.parameters p ring prims kdfOK).Sym :=
    inferInstanceAs (DecidableEq
      (ErasureCode.SPQRReedSolomon.Chunk ErasureCode.SPQRReedSolomon.GF16))
  obtain ⟨hHdr, hEk, hCt1, hCt2⟩ := Bounded.payloads_correct p
  refine le_trans (NoAuth.security_le P (Eq.refl Unit) irl
    hHdr hEk hCt1 hCt2 A qS hqS) ?_
  apply add_le_add
  · apply div_le_div_of_nonneg_right _ (by norm_num)
    apply Finset.sum_le_sum
    intro i hi
    apply add_le_add
    · exact le_of_eq (congrArg ENNReal.toReal (MLKEM.Bounded.indCPAAdvantage_lift p ring prims
        (NoAuth.kemReduction P (Eq.refl Unit) irl A (i + 1)))).symm
    · exact le_rfl
  · exact le_of_eq (congrArg (fun x => (qS : ℝ) * x.toReal)
      (MLKEM.Bounded.correctnessError_eq p ring prims))

end

end MLKEMBraid
