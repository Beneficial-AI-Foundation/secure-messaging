/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.SCKA.MLKEMBraid.Security.Auth.Scheduled
public import SecureMessaging.SCKA.MLKEMBraid.Security.Auth.Exposure
public import SecureMessaging.SCKA.MLKEMBraid.Security.Auth.Games
public import SecureMessaging.SCKA.MLKEMBraid.Security.Auth.Reductions
public import SecureMessaging.SCKA.MLKEMBraid.Security.KDFGame
public import SecureMessaging.SCKA.MLKEMBraid.Instances

/-!
# Security of ML-KEM Braid with a scheduled authenticator

`security` bounds the guessing advantage of a passive adversary against `scheme P S irl` under the
exposure policy `successorExposure` (E⁺). For an adversary `A` making at most `q` send queries,

`AdvGuess(A) ≤ 2q · (AdvINDCPA(ℬ) + AdvKDF(𝒞)) + q · (AdvInput(𝒟) + AdvRoot(ℰ)) + q · ε`,

where `ℬ`, `𝒞`, `𝒟` and `ℰ` are the four reductions of `Reductions`, `AdvKDF` is the advantage in
the key-derivation game `NoAuth.kdfContextExp`, `AdvInput` and `AdvRoot` are the advantages in
the two key-derivation experiments of the schedule (`inputExp`, `rootExp`), and `ε` is the KEM
correctness error. The four stream decoders are sound for their erasure codes.

`security_mlkem` states the same bound for Braid over ML-KEM (`mlkemBraidParameters`), with the
set-based decoders of four correct erasure codes.
-/

@[expose] public section

namespace MLKEMBraid.Auth

/-- Assume sound stream decoders for the four streams and an adversary `A` making at most `q`
send queries in total (`SendQueryBound A q`). Then the guessing advantage of `A` under E⁺ is at
most `2q` times the sum of an IND-CPA advantage and a key-derivation advantage, plus `q` times the
sum of the secret-input and the secret-root advantages, plus `q` times the KEM correctness
error. -/
theorem security (P : Parameters ProbComp) {Root MacKey : Type}
    [SampleableType P.K] [SampleableType P.EpochKey] [SampleableType Root] [SampleableType MacKey]
    [DecidableEq P.K] [DecidableEq P.EpochKey] [DecidableEq P.Mac]
    (S : ScheduledAuthenticator P Root MacKey) (irl : P.kem.IncrementalRandLeak P.inc)
    (hHdrSound : P.decHdr.Sound P.ecpHdr) (hEkSound : P.decEk.Sound P.ecpEk)
    (hCt1Sound : P.decCt1.Sound P.ecpCt1) (hCt2Sound : P.decCt2.Sound P.ecpCt2)
    (A : Adversary P S irl) (q : ℕ) (hq : SendQueryBound A q) :
    let ℬ := kemMixReduction P S irl A q
    let 𝒞 := kdfMixReduction P S irl A q
    let 𝒟 := inputMixReduction P S irl A q
    let ℰ := rootMixReduction P S irl A q
    let ε := (P.kem.correctnessError ProbCompRuntime.probComp).toReal
    SCKAScheme.sckaGuessAdvantage (scheme P S irl) A
        (successorExposure P irl Root MacKey) (successorExposure P irl Root MacKey) ≤
      (2 * q : ℝ) * ((P.kem.IND_CPA_Advantage ProbCompRuntime.probComp ℬ).toReal +
          NoAuth.kdfAdvantage P 𝒞) +
      (q : ℝ) * (inputAdvantage S 𝒟 + rootAdvantage S ℰ) + q * ε := sorry

/-- The bound of `security` for Braid over ML-KEM (`mlkemBraidParameters`) when the four erasure
codes are correct. The decoders of these parameters are the set-based decoders, which are sound
for correct codes (`setDecoder_sound`). The IND-CPA adversary attacks raw ML-KEM, and `ε` is the
correctness error of raw ML-KEM. -/
theorem security_mlkem
    (p : MLKEM.ParameterSet) (ring : MLKEM.NTTRingOps)
    (prims : MLKEM.Primitives (MLKEM.ParameterSet.params p)
      (MLKEM.Concrete.concreteEncoding (MLKEM.ParameterSet.params p)))
    {EpochKey Mac Sym Root MacKey : Type}
    [SampleableType EpochKey] [SampleableType Root] [SampleableType MacKey]
    [DecidableEq EpochKey] [DecidableEq Mac] [DecidableEq Sym]
    (kdfOK : MLKEM.SharedSecret → ℕ → EpochKey)
    (ecpHdr : ErasureCodePayload ((MLKEM.mlkemIncremental p ring prims).PKheader × Mac) Sym)
    (ecpEk : ErasureCodePayload (MLKEM.mlkemIncremental p ring prims).PKvector Sym)
    (ecpCt1 : ErasureCodePayload (MLKEM.mlkemIncremental p ring prims).C₁ Sym)
    (ecpCt2 : ErasureCodePayload ((MLKEM.mlkemIncremental p ring prims).C₂ × Mac) Sym)
    (hHdrCorrect : ecpHdr.ec.Correct) (hEkCorrect : ecpEk.ec.Correct)
    (hCt1Correct : ecpCt1.ec.Correct) (hCt2Correct : ecpCt2.ec.Correct)
    (S : ScheduledAuthenticator (mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2)
      Root MacKey) :
    let P := mlkemBraidParameters p ring prims kdfOK ecpHdr ecpEk ecpCt1 ecpCt2
    let irl := MLKEM.mlkemIncrementalRandLeak p ring prims
    letI : SampleableType P.K := by
      change SampleableType MLKEM.SharedSecret
      infer_instance
    letI : SampleableType P.EpochKey := by
      change SampleableType EpochKey
      infer_instance
    letI : DecidableEq P.K := by
      change DecidableEq MLKEM.SharedSecret
      infer_instance
    letI : DecidableEq P.EpochKey := by
      change DecidableEq EpochKey
      infer_instance
    letI : DecidableEq P.Mac := by
      change DecidableEq Mac
      infer_instance
    ∀ (A : Adversary P S irl) (q : ℕ), SendQueryBound A q →
      let ℬ := kemMixReduction P S irl A q
      let 𝒞 := kdfMixReduction P S irl A q
      let 𝒟 := inputMixReduction P S irl A q
      let ℰ := rootMixReduction P S irl A q
      let ε := ((MLKEM.mlkemScheme p ring prims).correctnessError ProbCompRuntime.probComp).toReal
      SCKAScheme.sckaGuessAdvantage (scheme P S irl) A
          (successorExposure P irl Root MacKey) (successorExposure P irl Root MacKey) ≤
        (2 * q : ℝ) *
          (((MLKEM.mlkemScheme p ring prims).IND_CPA_Advantage ProbCompRuntime.probComp ℬ).toReal +
            NoAuth.kdfAdvantage P 𝒞) +
        (q : ℝ) * (inputAdvantage S 𝒟 + rootAdvantage S ℰ) + q * ε := sorry

end MLKEMBraid.Auth
