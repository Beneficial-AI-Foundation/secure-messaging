/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.IncrementalKEM.FromMLKEM
import SecureMessaging.KEM.MLKEM.Correctness

/-!
# Distributional equivalence of the two ML-KEM sampling interfaces

Splitting a uniformly sampled 64-byte key-generation seed gives two independent uniform
32-byte seeds. Consequently the KEM induced by `mlkemIncrementalDet` has the same key-generation
distribution, encapsulation, and decapsulation as `mlkemScheme`. Their correctness errors and
IND-CPA and IND-CCA advantages agree for every adversary with the same algorithms.
-/

open OracleComp KEMScheme SampleableType

namespace MLKEM

/-- Split the implementation's 64-byte seed into the FIPS 203 seeds `(d, z)`. -/
def splitKeygenRand : Bytes 64 ≃ Seed32 × Seed32 where
  toFun r := (r.take 32, r.drop 32)
  invFun r := r.1 ++ r.2
  left_inv r := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_append, Vector.getElem_take, Vector.getElem_drop]
    split_ifs with h
    · rfl
    · congr 1
      omega
  right_inv r := by
    apply Prod.ext
    · apply Vector.ext
      intro i hi
      change ((r.1 ++ r.2).take 32)[i] = r.1[i]
      rw [Vector.getElem_take, Vector.getElem_append, dite_eq_left hi]
    · apply Vector.ext
      intro i hi
      change ((r.1 ++ r.2).drop 32)[i] = r.2[i]
      rw [Vector.getElem_drop, Vector.getElem_append,
        dite_eq_right (show ¬32 + i < 32 by omega)]
      congr 1
      omega

/-- Splitting one uniform 64-byte seed has the distribution of two independent uniform seeds. -/
theorem splitKeygenRand_uniform :
    splitKeygenRand <$> ($ᵗ Bytes 64) =ᵈ
      (do let d ← $ᵗ Seed32; let z ← $ᵗ Seed32; pure (d, z)) := by
  apply EvalDistEq.of_forall_prEvent_eq
  intro event
  rw [prEvent_map]
  have h := prEvent_uniformSample_pair_of_bijective
    (g := fun d z : Seed32 => splitKeygenRand.symm (d, z))
    splitKeygenRand.symm.bijective (fun r => event (splitKeygenRand r))
  simpa only [Equiv.apply_symm_apply, prEvent_norm] using h.symm

variable (p : ParameterSet) (ring : NTTRingOps)
  (prims : Primitives (ParameterSet.params p)
    (Concrete.concreteEncoding (ParameterSet.params p)))

/-- First-stage encapsulation is the existing incremental ML-KEM computation. -/
theorem mlkemIncrementalDet_encaps1 :
    (mlkemIncrementalDet p ring prims).toIncremental.encaps1 =
      (mlkemIncremental p ring prims).encaps1 := by
  funext hdr
  simp only [mlkemIncrementalDet, IncrementalKEMDet.toIncremental, mlkemIncremental,
    map_eq_pure_bind]

/-- First-stage leakage returns the same message and deterministic output as the existing
witness. -/
theorem mlkemIncrementalDet_encaps1Rleak :
    (mlkemIncrementalDet p ring prims).toRandLeak.encaps1Rleak =
      (mlkemIncrementalRandLeak p ring prims).encaps1Rleak := rfl

/-- Encapsulation through the deterministic blocks is the existing ML-KEM computation. -/
theorem mlkemIncrementalDet_encaps :
    (mlkemIncrementalDet p ring prims).toKEM.encaps = (mlkemScheme p ring prims).encaps := by
  funext pk
  rw [(mlkemIncremental p ring prims).factor]
  simp only [IncrementalKEMDet.toKEM, mlkemIncrementalDet, mlkemIncremental,
    map_eq_pure_bind, bind_assoc, pure_bind]
  rfl

/-- Both interfaces use ML-KEM's deterministic decapsulation with implicit rejection. -/
theorem mlkemIncrementalDet_decaps :
    (mlkemIncrementalDet p ring prims).toKEM.decaps = (mlkemScheme p ring prims).decaps := rfl

/-- The implementation's key-generation sampling has the existing ML-KEM output distribution. -/
theorem mlkemIncrementalDet_keygen :
    (mlkemIncrementalDet p ring prims).toKEM.keygen =ᵈ (mlkemScheme p ring prims).keygen := by
  have h := splitKeygenRand_uniform.map
    (fun dz => keygenInternal ring (Concrete.concreteEncoding (ParameterSet.params p))
      prims dz.1 dz.2)
  change (fun r : Bytes 64 => keygenInternal ring
    (Concrete.concreteEncoding (ParameterSet.params p)) prims (r.take 32) (r.drop 32)) <$>
      ($ᵗ Bytes 64) =ᵈ _
  simpa only [map_eq_pure_bind, bind_assoc, pure_bind, splitKeygenRand, Equiv.coe_fn_mk,
    mlkemScheme, asKEMScheme, keygen] using h

/-- The honest correctness experiments have the same distribution. -/
theorem mlkemIncrementalDet_correctnessExperiment :
    (mlkemIncrementalDet p ring prims).toKEM.correctnessExperiment =ᵈ
      (mlkemScheme p ring prims).correctnessExperiment := by
  unfold KEMScheme.correctnessExperiment
  rw [mlkemIncrementalDet_encaps, mlkemIncrementalDet_decaps]
  exact (mlkemIncrementalDet_keygen p ring prims).bind_left _

/-- The two interfaces have the same missing success mass in the correctness experiment. -/
theorem mlkemIncrementalDet_correctnessError :
    (mlkemIncrementalDet p ring prims).toKEM.correctnessError ProbCompRuntime.probComp =
      (mlkemScheme p ring prims).correctnessError ProbCompRuntime.probComp := by
  unfold KEMScheme.correctnessError
  rw [ProbCompRuntime.probComp_evalDist, ProbCompRuntime.probComp_evalDist,
    (mlkemIncrementalDet_correctnessExperiment p ring prims).evalDist_eq]

/-- Under the existing coefficient-distribution comparison, the implementation's sampling
interface satisfies the ML-KEM-768 correctness bound. -/
theorem deltaCorrect_mlkemIncrementalDet768
    (hModel : CoefficientFailureBound .MLKEM768 Concrete.concreteNTTRingOps
      Concrete.mlkem768Primitives) :
    (mlkemIncrementalDet .MLKEM768 Concrete.concreteNTTRingOps
      Concrete.mlkem768Primitives).toKEM.deltaCorrect ProbCompRuntime.probComp
        (fips203DecapsulationFailureBound .MLKEM768) := by
  rw [KEMScheme.deltaCorrect, mlkemIncrementalDet_correctnessError .MLKEM768
    Concrete.concreteNTTRingOps Concrete.mlkem768Primitives]
  exact deltaCorrect_mlkem768 hModel

/-- An adversary with unchanged IND-CPA algorithms against the existing ML-KEM interface. -/
def indCPAAdversaryOfDet
    (adv : (mlkemIncrementalDet p ring prims).toKEM.IND_CPA_Adversary) :
    (mlkemScheme p ring prims).IND_CPA_Adversary :=
  ⟨adv.State, adv.preChallenge, adv.postChallenge⟩

/-- For each challenge bit, the IND-CPA experiments have the same distribution. -/
theorem mlkemIncrementalDet_indCPAExperiment
    (adv : (mlkemIncrementalDet p ring prims).toKEM.IND_CPA_Adversary) (b : Bool) :
    KEMScheme.IND_CPA_Experiment ProbCompRuntime.probComp adv b =ᵈ
      KEMScheme.IND_CPA_Experiment ProbCompRuntime.probComp
        (indCPAAdversaryOfDet p ring prims adv) b := by
  unfold KEMScheme.IND_CPA_Experiment
  simp only [indCPAAdversaryOfDet, mlkemIncrementalDet_encaps]
  exact (mlkemIncrementalDet_keygen p ring prims).bind_left _

/-- The IND-CPA guessing games have the same distribution. -/
theorem mlkemIncrementalDet_indCPAGame
    (adv : (mlkemIncrementalDet p ring prims).toKEM.IND_CPA_Adversary) :
    KEMScheme.IND_CPA_Game ProbCompRuntime.probComp adv =ᵈ
      KEMScheme.IND_CPA_Game ProbCompRuntime.probComp
        (indCPAAdversaryOfDet p ring prims adv) := by
  unfold KEMScheme.IND_CPA_Game
  simp only [indCPAAdversaryOfDet, mlkemIncrementalDet_encaps]
  exact (mlkemIncrementalDet_keygen p ring prims).bind_left _

/-- Changing the key-generation sampling interface preserves every IND-CPA advantage. -/
theorem mlkemIncrementalDet_indCPAAdvantage
    (adv : (mlkemIncrementalDet p ring prims).toKEM.IND_CPA_Adversary) :
    KEMScheme.IND_CPA_Advantage ProbCompRuntime.probComp adv =
      KEMScheme.IND_CPA_Advantage ProbCompRuntime.probComp
        (indCPAAdversaryOfDet p ring prims adv) := by
  unfold KEMScheme.IND_CPA_Advantage
  rw [ProbCompRuntime.probComp_evalDist, ProbCompRuntime.probComp_evalDist,
    (mlkemIncrementalDet_indCPAGame p ring prims adv).evalDist_eq]

/-- Reuse the algorithms of an IND-CCA adversary for a KEM on the same spaces. -/
private def sameCCAAdversary {K PK SK C : Type} {kem kem' : KEMScheme ProbComp K PK SK C}
    (adv : kem.IND_CCA_Adversary) : kem'.IND_CCA_Adversary where
  State := adv.State
  preChallenge := adv.preChallenge
  postChallenge := adv.postChallenge

/-- Equal key-generation distributions and identical encapsulation and decapsulation preserve
an IND-CCA game's distribution. -/
private theorem indCCAGame_congr {K PK SK C : Type} [DecidableEq C] [SampleableType K]
    {kem kem' : KEMScheme ProbComp K PK SK C}
    (hkg : kem.keygen =ᵈ kem'.keygen) (henc : kem.encaps = kem'.encaps)
    (hdec : kem.decaps = kem'.decaps) (adv : kem.IND_CCA_Adversary) :
    KEMScheme.IND_CCA_Game ProbCompRuntime.probComp adv =ᵈ
      KEMScheme.IND_CCA_Game ProbCompRuntime.probComp (sameCCAAdversary (kem' := kem') adv) := by
  unfold KEMScheme.IND_CCA_Game
  simp only [sameCCAAdversary, KEMScheme.IND_CCA_preChallengeImpl,
    KEMScheme.IND_CCA_postChallengeImpl, henc, hdec]
  exact hkg.bind_left _

/-- An adversary with unchanged IND-CCA algorithms against the existing ML-KEM interface. -/
def indCCAAdversaryOfDet
    (adv : (mlkemIncrementalDet p ring prims).toKEM.IND_CCA_Adversary) :
    (mlkemScheme p ring prims).IND_CCA_Adversary := sameCCAAdversary adv

/-- The IND-CCA guessing games, including their decapsulation oracles, have the same
distribution. -/
theorem mlkemIncrementalDet_indCCAGame
    (adv : (mlkemIncrementalDet p ring prims).toKEM.IND_CCA_Adversary) :
    KEMScheme.IND_CCA_Game ProbCompRuntime.probComp adv =ᵈ
      KEMScheme.IND_CCA_Game ProbCompRuntime.probComp
        (indCCAAdversaryOfDet p ring prims adv) := by
  exact indCCAGame_congr (mlkemIncrementalDet_keygen p ring prims)
    (mlkemIncrementalDet_encaps p ring prims) (mlkemIncrementalDet_decaps p ring prims) adv

/-- Changing the key-generation sampling interface preserves every IND-CCA advantage. -/
theorem mlkemIncrementalDet_indCCAAdvantage
    (adv : (mlkemIncrementalDet p ring prims).toKEM.IND_CCA_Adversary) :
    KEMScheme.IND_CCA_Advantage ProbCompRuntime.probComp adv =
      KEMScheme.IND_CCA_Advantage ProbCompRuntime.probComp
        (indCCAAdversaryOfDet p ring prims adv) := by
  unfold KEMScheme.IND_CCA_Advantage
  rw [ProbCompRuntime.probComp_evalDist, ProbCompRuntime.probComp_evalDist,
    (mlkemIncrementalDet_indCCAGame p ring prims adv).evalDist_eq]

end MLKEM
