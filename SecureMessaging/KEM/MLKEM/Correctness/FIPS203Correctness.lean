/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.MLKEM.Correctness.FailureBounds

/-!
# ML-KEM FIPS 203 decapsulation-failure experiment

FIPS 203 Section 3.2 defines the decapsulation-failure probability of ML-KEM:
the probability, over an honest key pair and an honest encapsulation `(c, K)`,
that decapsulation returns a shared secret different from `K`.

This file defines the failure experiment `fips203DecapsulationFailureExp`, which
samples `(d, z, m)` and reports whether decapsulation disagrees with the
encapsulated key, and proves that its failure probability equals the generic
`KEMScheme.correctnessError` of VCV-io's packaged `MLKEM.asKEMScheme`.
-/

open OracleComp KEMScheme ENNReal

namespace MLKEM

/-- The FIPS 203 Section 3.2 decapsulation-failure experiment: sample the key
seeds `(d, z)` and message `m`, then report whether honest decapsulation
disagrees with the encapsulated shared secret. -/
def fips203DecapsulationFailureExp (p : ParameterSet) (ring : NTTRingOps)
    (encoding : Encoding (ParameterSet.params p))
    [DecidableEq encoding.EncodedU] [DecidableEq encoding.EncodedV]
    (prims : Primitives (ParameterSet.params p) encoding) : ProbComp Bool := do
  let d ← $ᵗ Seed32
  let z ← $ᵗ Seed32
  let m ← $ᵗ Message
  let (ek, dk) := keygenInternal ring encoding prims d z
  let (k, c) := encapsInternal ring encoding prims ek m
  let k' := decapsInternal ring encoding prims dk c
  pure (decide (k' ≠ k))

/-- The decapsulation-failure probability of the FIPS 203 experiment equals the
generic correctness error of VCV-io's packaged ML-KEM `KEMScheme`. -/
theorem correctnessError_eq_fips203DecapsulationFailureProb (p : ParameterSet)
    (ring : NTTRingOps) (encoding : Encoding (ParameterSet.params p))
    [DecidableEq encoding.EncodedTHat] [DecidableEq encoding.EncodedU]
    [DecidableEq encoding.EncodedV]
    (prims : Primitives (ParameterSet.params p) encoding) :
    (asKEMScheme ring encoding prims).correctnessError ProbCompRuntime.probComp =
      Pr[= true | fips203DecapsulationFailureExp p ring encoding prims] := by
  have hbridge : (asKEMScheme ring encoding prims).correctnessError ProbCompRuntime.probComp
      = Pr[= false | (asKEMScheme ring encoding prims).CorrectExp] := by
    rw [KEMScheme.correctnessError,
      show ProbCompRuntime.probComp.evalDist (asKEMScheme ring encoding prims).CorrectExp
        = evalDist (asKEMScheme ring encoding prims).CorrectExp from rfl,
      SPMF.probOutput_eq_apply, probOutput_def]
  have halign : (asKEMScheme ring encoding prims).CorrectExp =
      (! ·) <$> fips203DecapsulationFailureExp p ring encoding prims := by
    simp only [KEMScheme.CorrectExp, asKEMScheme, keygen, fips203DecapsulationFailureExp,
      monad_norm, Option.some.injEq, decide_not, ne_eq, Function.comp_apply, Bool.not_not]
  rw [hbridge, halign, probOutput_not_map']

end MLKEM
