/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.Bounds
import SecureMessaging.SCKA.MLKEMBraid.Instances

/-!
# The unrestricted-payload ML-KEM specialization

This abstract-symbol result leaves payload codecs and their correctness as caller parameters.
Finite symbols cannot provide its universal fixed-block roundtrip on unrestricted ByteArray
payloads. A bounded finite-domain endpoint is a distinct specialization, not an instantiation
retroactively supplied to this theorem.

The scheme quantifies over supplied ring and primitive functions. It preserves the concrete
adapter's vector-before-seed hash convention; the Braid PDF writes seed-before-vector. No
hash-order equality or game hop is asserted. Opaque external hashes do not establish SHA-3 or
SHAKE semantics. No C/FFI, implemented NTT-loop, entropy failure, capped-sampler panic,
constant-time or physical-erasure correspondence is proved. Numerical FIPS correctness bounds
still require NTTRingLaws and CoefficientFailureBound. Abstract codec field representations
are not runtime SPQR byte-layout or complexity results. No primitive/KDF hardness, efficient
or QPT adversary class, authenticated security or messaging composition is added.
-/

open OracleSpec OracleComp ENNReal

namespace MLKEMBraid

/-- **No-authentication security of concrete ML-KEM Braid**: `NoAuth.security_le` for
`mlkemBraidScheme` with incremental ML-KEM and its leaking randomness. Payload symbols and
universally roundtripping codecs remain abstract caller parameters. -/
theorem mlkemBraidScheme_noAuth_security_le (p : MLKEM.ParameterSet) (ring : MLKEM.NTTRingOps)
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
    SCKAScheme.ExposurePolicy.sckaGuessAdvantage
        (mlkemBraidScheme p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2
          (NoAuth.auth (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2)
            (Eq.refl Unit)) (pure ()))
        A
        (NoAuth.exposure (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2)
          (MLKEM.mlkemIncrementalRandLeak p ring prims))
        (NoAuth.exposure (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2)
          (MLKEM.mlkemIncrementalRandLeak p ring prims)) ≤
      (∑ i ∈ Finset.range qS,
        (((MLKEM.mlkemScheme p ring prims).IND_CPA_Advantage ProbCompRuntime.probComp
            (NoAuth.kemReduction
              (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2)
              (Eq.refl Unit) (MLKEM.mlkemIncrementalRandLeak p ring prims) A (i + 1))).toReal +
          (𝒟[NoAuth.kdfExp (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2)
              (i + 1)
              (NoAuth.kdfReduction
                (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2)
                (Eq.refl Unit) (MLKEM.mlkemIncrementalRandLeak p ring prims) A (i + 1))
              true].boolDist 𝒟[NoAuth.kdfExp
                  (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2)
              (i + 1)
              (NoAuth.kdfReduction
                (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2)
                (Eq.refl Unit) (MLKEM.mlkemIncrementalRandLeak p ring prims) A (i + 1))
              false]).toReal)) / 2 +
      (qS : ℝ) * ((MLKEM.mlkemScheme p ring prims).correctnessError
        ProbCompRuntime.probComp).toReal := by
  let : DecidableEq (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2).K :=
    inferInstanceAs (DecidableEq MLKEM.SharedSecret)
  let : SampleableType (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2).K :=
    inferInstanceAs (SampleableType MLKEM.SharedSecret)
  let : SampleableType
      (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2).EpochKey :=
    inferInstanceAs (SampleableType EpochKey)
  let : DecidableEq (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2).EpochKey :=
    inferInstanceAs (DecidableEq EpochKey)
  let : DecidableEq (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2).Sym :=
    inferInstanceAs (DecidableEq Sym)
  exact NoAuth.security_le (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2)
    (Eq.refl Unit) (MLKEM.mlkemIncrementalRandLeak p ring prims) hHdrCorrect hEkCorrect
    hCt1Correct hCt2Correct A qS hqS

end MLKEMBraid
