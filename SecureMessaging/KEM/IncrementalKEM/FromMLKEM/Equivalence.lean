/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.KEM.IncrementalKEM.FromMLKEM
public import SecureMessaging.KEM.MLKEM.Construction

/-!
# Correctness error of ML-KEM with explicit coins

`mlkemIncrementalDet` runs ML-KEM with explicit coins: its algorithms are deterministic functions
of random bytes that are drawn first. Key generation draws one 64-byte seed, and encapsulation draws
one 32-byte message. `mlkemScheme` follows FIPS 203, where key generation draws
two 32-byte seeds `d` and `z`. The first 32 bytes of the 64-byte seed take the role of `d`, and the
last 32 bytes take the role of `z`.

A uniform 64-byte seed, split in two, has the distribution of two independent uniform 32-byte seeds.
Encapsulation and decapsulation are the same computations in both KEMs. So the two KEMs have the
same correctness error (`mlkemIncrementalDet_correctnessError`). This module compares only the
correctness error.
-/

@[expose] public section

open OracleComp KEMScheme SampleableType

namespace MLKEM

/-- Split the 64-byte key-generation seed into the FIPS 203 seeds `(d, z)`. -/
private def splitKeygenRand : Bytes 64 ≃ Seed32 × Seed32 where
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
  simpa only [map_eq_pure_bind, bind_assoc, pure_bind, splitKeygenRand, Equiv.coe_fn_mk,
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
