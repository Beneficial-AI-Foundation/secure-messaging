/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.IncrementalKEM.FromMLKEM

/-!
# EasyCrypt assumptions for ML-KEM-768 correctness

The theorem `mlkem_spec_correctness` in the pinned EasyCrypt development proves a symbolic
bound for its random-oracle ML-KEM-768 correctness experiment. We model this external result
as the axiom `EasyCryptMLKEM768.romCorrectnessError_le`. The separate axiom
`EasyCryptMLKEM768.correctnessError_le_romCorrectnessError` relates the EasyCrypt experiment
to this repository's concrete `mlkem768Scheme`. The local and staged bounds below are proved
from these two assumptions.

The source is `mlkem_spec_correctness`
(`formosa-mlkem@475b87434506280fdfa1a1ba5da0af3787e00579`, with the submodule
`crypto-specs@fb050598ed356c5c6604d92a1e198b2dd4543777`), at
`proof/spec/MLKEMSecurity768.ec:1708-1733`, the correctness clause of Theorem 6 of
"Formally verifying Kyber — Episode V". Under four upper-bound hypotheses, it bounds the
failure probability by `failprob + hsadv + 2 * prfadv`. No numerical failure probability is
assumed here.
-/

open OracleComp KEMScheme ENNReal

namespace MLKEM

namespace EasyCryptMLKEM768

/-! ## EasyCrypt quantities

The following opaque constants denote probabilities and advantages in the pinned EasyCrypt
development. Their declarations assert no bounds; the axioms below state all assumptions.
-/

/-- `δ_CB`, the probability that the ML-KEM-768 `CorrectnessBound` experiment returns `true`
(`MLWE_PKE_Hash.ec:782-796`, instantiated at `MLKEMSecurity768.ec:643-711`). The event is
that some centered coefficient of the decryption noise exceeds `727`. -/
opaque correctnessBoundError : ℝ≥0∞

/-- `ε_hs`: the distinguishing gap between the real and ideal `G_coins768` smoothing games
used by the EasyCrypt correctness reduction in key generation. -/
opaque smoothingAdvantage : ℝ≥0∞

/-- `ε_prf_kg`: the real-versus-random-function gap of the SHAKE-256 noise sampler used by
ML-KEM-768 key generation in the EasyCrypt correctness reduction. -/
opaque keygenPRFAdvantage : ℝ≥0∞

/-- `ε_prf_enc`: the real-versus-random-function gap of the SHAKE-256 noise sampler used by
ML-KEM-768 encapsulation in the EasyCrypt correctness reduction. -/
opaque encapsPRFAdvantage : ℝ≥0∞

/-- `P_ROM`: the failure probability of the EasyCrypt random-oracle-model ML-KEM-768
correctness experiment `SPEC_MODEL.Correctness(SPEC_MODEL.RO.RO, MLKEM_Op)`
(`KEM_ROM.ec:188-203`): generate keys, encapsulate, decapsulate, and return `true` exactly
when the decapsulated key differs from the encapsulated one. There is no adversary in this
game. -/
opaque romCorrectnessError : ℝ≥0∞

/-! ## Axioms -/

/-- **EC-1 (EasyCrypt bound).** Lean representation of the source theorem
`mlkem_spec_correctness`. Source:
`formosa-mlkem@475b87434506280fdfa1a1ba5da0af3787e00579`
(`crypto-specs@fb050598ed356c5c6604d92a1e198b2dd4543777`),
`proof/spec/MLKEMSecurity768.ec:1708-1733`. The common bound `prfadv` applies to both PRF
games. This axiom also assumes the ML-KEM-768 side conditions `qHC = 0` and plaintext
cardinality greater than one, and represents the source's real-valued quantities in
`ℝ≥0∞`. It concerns only the EasyCrypt model; EC-2 supplies the relation to the local
scheme. -/
axiom romCorrectnessError_le {failprob hsadv prfadv : ℝ≥0∞}
    (hcb : correctnessBoundError ≤ failprob)
    (hhs : smoothingAdvantage ≤ hsadv)
    (hkg : keygenPRFAdvantage ≤ prfadv)
    (henc : encapsPRFAdvantage ≤ prfadv) :
    romCorrectnessError ≤ failprob + hsadv + 2 * prfadv

/-- **EC-2 (model alignment).** Assumes that the correctness error of the concrete
`mlkem768Scheme` is at most the EasyCrypt ROM correctness error. The assumption subsumes the
correspondence of types and algorithms, the treatment of nontermination and opposite
Boolean conventions, and the interpretation of `SPEC_MODEL.RO.RO` by the concrete
SHA-3/SHAKE primitives. -/
axiom correctnessError_le_romCorrectnessError :
    mlkem768Scheme.correctnessError ProbCompRuntime.probComp ≤ romCorrectnessError

end EasyCryptMLKEM768

/-! ## Consequences -/

/-- Under the upper-bound hypotheses of `mlkem_spec_correctness`, the local ML-KEM-768
scheme is `(failprob + hsadv + 2 * prfadv)`-correct. -/
-- ANCHOR: deltaCorrect_mlkem768_easycrypt_of_le
theorem deltaCorrect_mlkem768_easycrypt_of_le {failprob hsadv prfadv : ℝ≥0∞}
    (hcb : EasyCryptMLKEM768.correctnessBoundError ≤ failprob)
    (hhs : EasyCryptMLKEM768.smoothingAdvantage ≤ hsadv)
    (hkg : EasyCryptMLKEM768.keygenPRFAdvantage ≤ prfadv)
    (henc : EasyCryptMLKEM768.encapsPRFAdvantage ≤ prfadv) :
    mlkem768Scheme.deltaCorrect ProbCompRuntime.probComp (failprob + hsadv + 2 * prfadv) :=
  le_trans EasyCryptMLKEM768.correctnessError_le_romCorrectnessError
    (EasyCryptMLKEM768.romCorrectnessError_le hcb hhs hkg henc)
-- ANCHOR_END: deltaCorrect_mlkem768_easycrypt_of_le

/-- The staged ML-KEM-768 correctness experiment returns `false` with probability at most
`failprob + hsadv + 2 * prfadv`. -/
theorem incrementalCorrectExp_failure_le_mlkem768_easycrypt {failprob hsadv prfadv : ℝ≥0∞}
    (hcb : EasyCryptMLKEM768.correctnessBoundError ≤ failprob)
    (hhs : EasyCryptMLKEM768.smoothingAdvantage ≤ hsadv)
    (hkg : EasyCryptMLKEM768.keygenPRFAdvantage ≤ prfadv)
    (henc : EasyCryptMLKEM768.encapsPRFAdvantage ≤ prfadv) :
    Pr[= false | ProbCompRuntime.probComp.evalDist
        (mlkemIncremental .MLKEM768 Concrete.concreteNTTRingOps
          Concrete.mlkem768Primitives).CorrectExp]
      ≤ failprob + hsadv + 2 * prfadv :=
  (mlkemIncremental .MLKEM768 Concrete.concreteNTTRingOps
    Concrete.mlkem768Primitives).probFailure_correctExp_le _
    (deltaCorrect_mlkem768_easycrypt_of_le hcb hhs hkg henc)

end MLKEM
