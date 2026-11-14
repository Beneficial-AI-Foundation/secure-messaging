/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.KEM.IncrementalKEM.FromMLKEM
public import SecureMessaging.KEM.MLKEM.Construction
public import ToVCVio.Data.Vector.Split

/-!
# Correctness error of ML-KEM with explicit coins

This module relates two descriptions of the key encapsulation mechanism (KEM) ML-KEM:

* `mlkemScheme` is ML-KEM as in FIPS 203. Key generation draws two 32-byte seeds `d` and `z`, and
  encapsulation draws a 32-byte message.
* `mlkemIncrementalDet` is ML-KEM with explicit coins. Its algorithms are deterministic functions
  of random bytes, which `toKEM` draws first. Key generation takes one 64-byte seed. Its first
  32 bytes play the role of `d`, and its last 32 bytes play the role of `z`. Encapsulation takes
  one 32-byte message.

## Main result

`mlkemIncrementalDet_correctnessError`: the two KEMs have the same correctness error. The
correctness error of a KEM is the probability that decapsulation of an honestly generated
encapsulation does not return the encapsulated key.
-/

@[expose] public section

open OracleComp KEMScheme SampleableType

namespace MLKEM

/-- Split the 64-byte key-generation seed into the FIPS 203 seeds `(d, z)`. -/
private abbrev splitKeygenRand : Bytes 64 ≃ Seed32 × Seed32 := Vector.splitAtEquiv 32 32

/-- The split is the pair of the first and the last 32 bytes. -/
private theorem splitKeygenRand_apply (r : Bytes 64) :
    splitKeygenRand r = (r.take 32, r.drop 32) := by
  apply Prod.ext <;> apply Vector.ext <;> intro i hi <;>
    simp only [splitKeygenRand, Vector.splitAtEquiv, Equiv.coe_fn_mk, Vector.getElem_splitAt_fst,
      Vector.getElem_splitAt_snd]
  · exact (Vector.getElem_take (by omega)).symm
  · exact (Vector.getElem_drop (by omega)).symm

/-- A uniform 64-byte seed, split in two, has the distribution of two independent uniform seeds. -/
private theorem splitKeygenRand_uniform :
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

/-- Encapsulation through the explicit-coin stages is the ML-KEM encapsulation. -/
private theorem mlkemIncrementalDet_encaps :
    (mlkemIncrementalDet p ring prims).toKEM.encaps = (mlkemScheme p ring prims).encaps := by
  funext pk
  rw [(mlkemIncremental p ring prims).factor]
  simp only [IncrementalKEMDet.toKEM, mlkemIncrementalDet, mlkemIncremental,
    incrementalStructure, map_eq_pure_bind, bind_assoc, pure_bind]
  rfl

/-- Key generation from one 64-byte seed has the distribution of ML-KEM key generation. -/
private theorem mlkemIncrementalDet_keygen :
    (mlkemIncrementalDet p ring prims).toKEM.keygen =ᵈ (mlkemScheme p ring prims).keygen := by
  have h := splitKeygenRand_uniform.map
    (fun dz => keygenInternal ring (Concrete.concreteEncoding (ParameterSet.params p))
      prims dz.1 dz.2)
  change (fun r : Bytes 64 => keygenInternal ring
    (Concrete.concreteEncoding (ParameterSet.params p)) prims (r.take 32) (r.drop 32)) <$>
      ($ᵗ Bytes 64) =ᵈ _
  simpa only [map_eq_pure_bind, bind_assoc, pure_bind, splitKeygenRand_apply,
    mlkemScheme, asKEMScheme, keygen] using h

/-- ML-KEM with explicit coins and ML-KEM have the same correctness error. -/
theorem mlkemIncrementalDet_correctnessError :
    (mlkemIncrementalDet p ring prims).toKEM.correctnessError ProbCompRuntime.probComp =
      (mlkemScheme p ring prims).correctnessError ProbCompRuntime.probComp := by
  have hexp : (mlkemIncrementalDet p ring prims).toKEM.correctnessExperiment =ᵈ
      (mlkemScheme p ring prims).correctnessExperiment := by
    unfold KEMScheme.correctnessExperiment
    rw [mlkemIncrementalDet_encaps,
      show (mlkemIncrementalDet p ring prims).toKEM.decaps = (mlkemScheme p ring prims).decaps
        from rfl]
    exact (mlkemIncrementalDet_keygen p ring prims).bind_left _
  unfold KEMScheme.correctnessError
  rw [ProbCompRuntime.probComp_evalDist, ProbCompRuntime.probComp_evalDist, hexp.evalDist_eq]

end MLKEM
