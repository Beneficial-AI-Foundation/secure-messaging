/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.MLKEM.Construction
import SecureMessaging.KEM.MLKEM.Correctness.ConcreteEncoding
import SecureMessaging.KEM.MLKEM.Correctness.FailureBounds
import SecureMessaging.KEM.MLKEM.Correctness.FailureCertificate
import SecureMessaging.KEM.MLKEM.Correctness.FailureRates
import SecureMessaging.KEM.MLKEM.Correctness.FIPS203Correctness
import SecureMessaging.KEM.MLKEM.Correctness.Noise
import SecureMessaging.KEM.MLKEM.Correctness.NoiseDistribution
import SecureMessaging.KEM.MLKEM.Correctness.NoiseIdentity
import SecureMessaging.KEM.MLKEM.Correctness.NoiseModel
import SecureMessaging.KEM.MLKEM.Correctness.Reduction

/-!
# ML-KEM δ-correctness

This module bundles the ML-KEM correctness development and states its headline
results. The correctness theorems bound the Section 3.2 decapsulation-failure
probability of each approved parameter set by the Table 1 rate `2 ^ (-e_p)`.
Beyond the construction itself, their only hypothesis is `FIPS203NoiseModel`,
the standard's heuristic assumption that hash functions and XOFs behave like
uniformly random functions.
-/

open OracleComp KEMScheme ENNReal

namespace MLKEM

/-- Under the FIPS 203 noise model, the correctness error of ML-KEM at
parameter set `p` is at most the Table 1 decapsulation-failure bound
`2 ^ (-e_p)`. -/
theorem correctnessError_le_fips203 (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p)))
    (hRing : NTTRingLaws ring) (hModel : FIPS203NoiseModel p ring prims) :
    (mlkemScheme p ring prims).correctnessError ProbCompRuntime.probComp ≤
      fips203DecapsulationFailureBound p :=
  le_trans (correctnessError_le_underlyingCorrectnessError ring _ prims)
    (underlyingCorrectnessError_le_fips203 p ring prims hRing hModel)

/-- Under the FIPS 203 noise model, ML-KEM at parameter set `p` is
`δ`-correct for the Table 1 bound `δ = 2 ^ (-e_p)`. -/
-- ANCHOR: deltaCorrectFips203
theorem deltaCorrect_fips203 (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p)))
    (hRing : NTTRingLaws ring) (hModel : FIPS203NoiseModel p ring prims) :
    (mlkemScheme p ring prims).deltaCorrect ProbCompRuntime.probComp
      (fips203DecapsulationFailureBound p) :=
  deltaCorrect_of_underlying ring _ prims
    (underlyingCorrectnessError_le_fips203 p ring prims hRing hModel)
-- ANCHOR_END: deltaCorrectFips203

/-- Under the FIPS 203 noise model, the probability that the Section 3.2
decapsulation-failure experiment reports a failure is at most the Table 1
bound. -/
theorem fips203DecapsulationFailureProb_le_bound (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p)))
    (hRing : NTTRingLaws ring) (hModel : FIPS203NoiseModel p ring prims) :
    Pr[= true | fips203DecapsulationFailureExp p ring
        (Concrete.concreteEncoding (ParameterSet.params p)) prims] ≤
      fips203DecapsulationFailureBound p := by
  rw [← correctnessError_eq_fips203DecapsulationFailureProb]
  exact correctnessError_le_fips203 p ring prims hRing hModel

/-- ML-KEM-512 is `2 ^ (-138.8)`-correct under the FIPS 203 noise model. -/
theorem deltaCorrect_mlkem512
    (hModel : FIPS203NoiseModel .MLKEM512 Concrete.concreteNTTRingOps
      Concrete.mlkem512Primitives) :
    mlkem512Scheme.deltaCorrect ProbCompRuntime.probComp
      (fips203DecapsulationFailureBound .MLKEM512) :=
  deltaCorrect_fips203 _ _ _ Concrete.concreteNTTRingLaws hModel

/-- ML-KEM-768 is `2 ^ (-164.8)`-correct under the FIPS 203 noise model. -/
theorem deltaCorrect_mlkem768
    (hModel : FIPS203NoiseModel .MLKEM768 Concrete.concreteNTTRingOps
      Concrete.mlkem768Primitives) :
    mlkem768Scheme.deltaCorrect ProbCompRuntime.probComp
      (fips203DecapsulationFailureBound .MLKEM768) :=
  deltaCorrect_fips203 _ _ _ Concrete.concreteNTTRingLaws hModel

/-- ML-KEM-1024 is `2 ^ (-174.8)`-correct under the FIPS 203 noise model. -/
theorem deltaCorrect_mlkem1024
    (hModel : FIPS203NoiseModel .MLKEM1024 Concrete.concreteNTTRingOps
      Concrete.mlkem1024Primitives) :
    mlkem1024Scheme.deltaCorrect ProbCompRuntime.probComp
      (fips203DecapsulationFailureBound .MLKEM1024) :=
  deltaCorrect_fips203 _ _ _ Concrete.concreteNTTRingLaws hModel

end MLKEM
