/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Instances
import SecureMessaging.SCKA.MLKEMBraid.Security.Reduction

/-!
# No-authentication security of ML-KEM Braid

The guessing advantage of an adversary against Braid without authentication, under the explicit
exposure policy, is bounded by the IND-CPA advantages of `kemReduction` and the uniform-input KDF
advantages of `kdfReduction` over the numerical epochs `1, …, qS`, plus `qS` times the KEM
correctness error, where `qS` bounds the adversary's sends.

The hidden-bit game is half the distinguishing advantage between its two fixed-bit games
(`securityExp_eq`). Each fixed-bit game is within the bad-event probability of its repaired game
(`fixed_repaired_gap_le`, `badEvent_le`). The repaired games are the endpoint hybrids
(`hybrid_endpoints`), and adjacent hybrids differ by a KEM gap and a KDF gap (`kem_gap_eq`,
`kdf_gap_eq`).

* `security_le`: the bound for the explicit-policy game.
* `security_le_delta`: the same bound for the baseline delta game.
* `MLKEMBraid.mlkemBraidScheme_noAuth_security_le`: the bound for concrete incremental ML-KEM.

The bound is an explicit reduction: it assumes no hardness of ML-KEM or of the key derivation,
and it does not bound the ML-KEM correctness error numerically. `MLKEM.correctnessError_le_fips203`
bounds that error under `NTTRingLaws ring` and `CoefficientFailureBound p ring prims`.
-/

open OracleSpec OracleComp ENNReal

namespace MLKEMBraid.NoAuth

variable {P : Parameters ProbComp}

section Final

variable [SampleableType P.EpochKey] [DecidableEq P.EpochKey] [DecidableEq P.Sym]
  (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)

/-- The sampled-bit experiment accepts as often as the hidden-bit game over the two fixed-bit
games. -/
theorem securityExp_eq (A : Adversary P irl) :
    Pr[= true | SCKAScheme.ExposurePolicy.securityExp (scheme P hMac irl) A (exposure P irl)
        (exposure P irl)] =
      Pr[= true | do
        let b ← ($ᵗ Bool)
        let z ← if b then fixed P hMac irl A true else fixed P hMac irl A false
        pure (b == z)] := by
  have h1 : (scheme P hMac irl).initKeyGen = pure () := rfl
  have h2 : ∀ ik, (scheme P hMac irl).initA ik = pure (MLKEMBraid.initA P (auth P hMac) ik) :=
    fun _ => rfl
  have h3 : ∀ ik, (scheme P hMac irl).initB ik = pure (MLKEMBraid.initB P (auth P hMac) ik) :=
    fun _ => rfl
  simp only [SCKAScheme.ExposurePolicy.securityExp, h1, h2, h3, pure_bind]
  refine probOutput_bind_congr fun b _ => ?_
  calc _ = Pr[= true | (simulateQ (SCKAScheme.ExposurePolicy.sckaSecurityImpl b (exposure P irl)
          (exposure P irl) (scheme P hMac irl)) A).run (SCKAScheme.initGameState
            (MLKEMBraid.initA P (auth P hMac) ()) (MLKEMBraid.initB P (auth P hMac) ())) >>=
          fun x => pure (b == x.1)] :=
        probOutput_bind_congr fun x _ => by
          obtain ⟨b', s'⟩ := x
          rfl
    _ = _ := by
      cases b
      · rw [if_neg Bool.false_ne_true, fixed, StateT.run'_eq, bind_map_left]
      · rw [if_pos rfl, fixed, StateT.run'_eq, bind_map_left]

end Final

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
        (P.kem.IND_CPA_Advantage ProbCompRuntime.probComp
            (kemReduction P hMac irl A (i + 1)) +
          (kdfExp P (i + 1) (kdfReduction P hMac irl A (i + 1)) true).boolDistAdvantage
            (kdfExp P (i + 1) (kdfReduction P hMac irl A (i + 1)) false))) / 2 +
      (qS : ℝ) * (P.kem.correctnessError ProbCompRuntime.probComp).toReal := by
  have hcE : P.kem.correctnessError ProbCompRuntime.probComp ≠ ⊤ :=
    ENNReal.sub_ne_top ENNReal.one_ne_top
  have hbad : ∀ b : Bool, (fixed P hMac irl A b).boolDistAdvantage
      (Prod.fst <$> run P hMac irl true (fun _ => if b then .uniform else .real) A) ≤
        (qS : ℝ) * (P.kem.correctnessError ProbCompRuntime.probComp).toReal := by
    intro b
    refine (fixed_repaired_gap_le P hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct A
      b).trans ?_
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top qS) hcE)
      (badEvent_le P hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct A qS hqS b)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h
  have hend := hybrid_endpoints P hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct A qS
    hqS
  have h0 := evalDist_ext_iff.mp hend.1 true
  have hq := evalDist_ext_iff.mp hend.2 true
  have hstep : ∀ i, |(Pr[= true | hybrid P hMac irl A (i + 1)]).toReal -
      (Pr[= true | hybrid P hMac irl A i]).toReal| ≤
      P.kem.IND_CPA_Advantage ProbCompRuntime.probComp (kemReduction P hMac irl A (i + 1)) +
        (kdfExp P (i + 1) (kdfReduction P hMac irl A (i + 1)) true).boolDistAdvantage
          (kdfExp P (i + 1) (kdfReduction P hMac irl A (i + 1)) false) := by
    intro i
    have hk := kem_gap_eq P hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct A (i + 1)
      (Nat.succ_pos i)
    rw [Nat.add_sub_cancel] at hk
    rw [← hk, ← kdf_gap_eq P hMac irl A (i + 1) (Nat.succ_pos i), abs_sub_comm]
    exact ProbComp.boolDistAdvantage_triangle _ _ _
  have hs := Finset.sum_range_sub (fun i => (Pr[= true | hybrid P hMac irl A i]).toReal) qS
  have htel : |(Pr[= true | hybrid P hMac irl A qS]).toReal -
      (Pr[= true | hybrid P hMac irl A 0]).toReal| ≤
      ∑ i ∈ Finset.range qS,
        (P.kem.IND_CPA_Advantage ProbCompRuntime.probComp (kemReduction P hMac irl A (i + 1)) +
          (kdfExp P (i + 1) (kdfReduction P hMac irl A (i + 1)) true).boolDistAdvantage
            (kdfExp P (i + 1) (kdfReduction P hMac irl A (i + 1)) false)) := by
    rw [← hs]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hstep i)
  have h1 := hbad true
  have h2 := hbad false
  unfold ProbComp.boolDistAdvantage at h1 h2
  rw [← hq] at h1
  rw [← h0] at h2
  unfold SCKAScheme.ExposurePolicy.sckaGuessAdvantage
  rw [securityExp_eq hMac irl A, probOutput_uniformBool_branch_toReal_sub_half, abs_div,
    abs_two]
  have ha := abs_sub_le (Pr[= true | fixed P hMac irl A true]).toReal
    (Pr[= true | hybrid P hMac irl A qS]).toReal (Pr[= true | fixed P hMac irl A false]).toReal
  have hb := abs_sub_le (Pr[= true | hybrid P hMac irl A qS]).toReal
    (Pr[= true | hybrid P hMac irl A 0]).toReal (Pr[= true | fixed P hMac irl A false]).toReal
  rw [abs_sub_comm (Pr[= true | hybrid P hMac irl A 0]).toReal] at hb
  linarith

/-- **`security_le_delta`**: the bound of `security_le` for the baseline delta security game. -/
theorem security_le_delta (P : Parameters ProbComp)
    [SampleableType P.K] [SampleableType P.EpochKey]
    [DecidableEq P.K] [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    (hMac : P.Mac = Unit) (irl : P.kem.IncrementalRandLeak P.inc)
    (hHdrCorrect : P.ecpHdr.ec.Correct)
    (hEkCorrect : P.ecpEk.ec.Correct)
    (hCt1Correct : P.ecpCt1.ec.Correct)
    (hCt2Correct : P.ecpCt2.ec.Correct)
    (A : Adversary P irl) (qS : ℕ) (hqS : SendQueryBound A qS) :
    SCKAScheme.sckaGuessAdvantage (scheme P hMac irl) A vuln vuln ≤
      (∑ i ∈ Finset.range qS,
        (P.kem.IND_CPA_Advantage ProbCompRuntime.probComp
            (kemReduction P hMac irl A (i + 1)) +
          (kdfExp P (i + 1) (kdfReduction P hMac irl A (i + 1)) true).boolDistAdvantage
            (kdfExp P (i + 1) (kdfReduction P hMac irl A (i + 1)) false))) / 2 +
      (qS : ℝ) * (P.kem.correctnessError ProbCompRuntime.probComp).toReal := by
  rw [← (securityGame_equiv_delta P hMac irl A).2]
  exact security_le P hMac irl hHdrCorrect hEkCorrect hCt1Correct hCt2Correct A qS hqS

end MLKEMBraid.NoAuth

namespace MLKEMBraid

/-- **No-authentication security of concrete ML-KEM Braid**: `NoAuth.security_le` for
`mlkemBraidScheme` with incremental ML-KEM and its leaking randomness. -/
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
