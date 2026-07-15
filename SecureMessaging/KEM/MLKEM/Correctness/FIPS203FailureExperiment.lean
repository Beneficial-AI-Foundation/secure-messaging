/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.MLKEM.Correctness.FailureBounds

/-!
# The FIPS 203 honest decapsulation-failure experiment

Fix a parameter set, NTT implementation, encoding, and primitive operations.
On the finite uniform sample space

`Ω = Seed32 × Seed32 × Message`,

an outcome `ω=(d,z,m)` determines

```
(ek,dk) = keygenInternal(d,z),
(K,c)   = encapsInternal(ek,m),
K'      = decapsInternal(dk,c).
```

`fips203DecapsulationFailureExp` returns the indicator of the event

`E = {ω∈Ω | K'(ω) ≠ K(ω)}`.                              (1)

Because `ProbComp` is total, the generic correctness definition satisfies

`correctnessError = 1-Pr[K'=K] = Pr[E]`.

`correctnessError_eq_fips203DecapsulationFailureProb` proves this equality by
unfolding the packaged ML-KEM scheme and identifying its success Boolean with
the complement of (1).

This file identifies the generic KEM correctness error with the probability
of the Section 3.2 event.  The numerical threshold is defined in
`FailureRates.lean`, and `NoiseModel.lean` states the coefficient-distribution
hypothesis used to derive the conditional inequality.
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
    rw [KEMScheme.correctnessError]
    change 1 - Pr[= true | (asKEMScheme ring encoding prims).CorrectExp] =
      Pr[= false | (asKEMScheme ring encoding prims).CorrectExp]
    rw [probOutput_false_eq_sub, probFailure_eq_zero, tsub_zero]
  have halign : (asKEMScheme ring encoding prims).CorrectExp =
      (! ·) <$> fips203DecapsulationFailureExp p ring encoding prims := by
    simp only [KEMScheme.CorrectExp, asKEMScheme, keygen, fips203DecapsulationFailureExp,
      monad_norm, Option.some.injEq, decide_not, ne_eq, Function.comp_apply, Bool.not_not]
  rw [hbridge, halign, probOutput_not_map']

end MLKEM
