/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.IncrementalKEM.MLKEM
import SecureMessaging.KEM.MLKEM.Construction

/-!
# Incremental ML-KEM

This module instantiates `KEMScheme.IncrementalStructure` for `mlkemScheme`. The ML-KEM
algorithm is specified in [NIST FIPS 203](https://csrc.nist.gov/pubs/fips/203/final), and the
staged interface follows [Signal's ML-KEM Braid specification,
§§1.2–1.2.1](https://signal.org/docs/specifications/mlkembraid/).

The encapsulation key splits into the header `(ρ, H(ek))` and encoded `t̂`. In the code,
`rho` / `ρ` is the 32-byte public-matrix seed, `H(ek)` is the hash of the complete
encapsulation key, and `tHat` / `tHatEncoded` / `t̂` is the encoded NTT-domain public-key
vector. A hat denotes an NTT-domain value, so `yHat` is the NTT of the ephemeral vector `y`.
The ciphertext splits into encoded `u` and `v` components. The first stage also computes
`e2`, the second noise polynomial, and retains `message`, the sampled 32-byte ML-KEM message.
The `factor` field of `mlkemIncremental` identifies the staged computation with ML-KEM
encapsulation. `mlkemIncrementalRandLeak` exposes the FIPS 203 coins of key
generation and first-stage encapsulation for security games.
-/

open OracleComp KEMScheme LatticeCrypto

namespace MLKEM

/-- The incremental ML-KEM structure. Stage 1 produces an `EncapsulationState` containing
`yHat`, `e2`, and `message`; stage 2 consumes that state without retaining raw coins. `validPK`
reconstructs `ek` from the received vector and `ρ`, then compares its hash with the hash in the
header. -/
-- ANCHOR: mlkemIncremental
def mlkemIncremental (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p))) :
    (mlkemScheme p ring prims).IncrementalStructure :=
  incrementalStructure ring (Concrete.concreteEncoding (ParameterSet.params p)) prims
-- ANCHOR_END: mlkemIncremental

/-- Incremental ML-KEM's second stage as a pure function. Stage 1 has already sampled all
encapsulation randomness; `mlkemIncremental.encaps2` only wraps `incrementalEncaps2` in
`ProbComp`. -/
-- ANCHOR: mlkemDeterministicEncaps2
def mlkemDeterministicEncaps2 (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p))) :
    (mlkemIncremental p ring prims).DeterministicEncaps2
-- ANCHOR_END: mlkemDeterministicEncaps2
    := incrementalDeterministicEncaps2 ring
      (Concrete.concreteEncoding (ParameterSet.params p)) prims

/-- ML-KEM decapsulation as a pure function. `mlkemScheme.decaps` wraps
`some (decapsInternal …)` in `ProbComp`; implicit rejection makes `decapsInternal` total. -/
-- ANCHOR: mlkemDeterministicDecaps
def mlkemDeterministicDecaps (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p))) :
    DeterministicDecaps (mlkemScheme p ring prims)
-- ANCHOR_END: mlkemDeterministicDecaps
    := incrementalDeterministicDecaps ring
      (Concrete.concreteEncoding (ParameterSet.params p)) prims

/-- Randomness-leakage package for `mlkemIncremental`. Key generation leaks the
FIPS 203 seeds `(d, z)`; first-stage encapsulation leaks the sampled `Message`;
second-stage encapsulation samples nothing, so its leak type is `Unit`. -/
-- ANCHOR: mlkemIncrementalRandLeak
def mlkemIncrementalRandLeak (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p))) :
    (mlkemScheme p ring prims).IncrementalRandLeak (mlkemIncremental p ring prims) :=
  incrementalRandLeak ring (Concrete.concreteEncoding (ParameterSet.params p)) prims
-- ANCHOR_END: mlkemIncrementalRandLeak

end MLKEM
