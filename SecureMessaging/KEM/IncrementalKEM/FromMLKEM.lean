/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import SecureMessaging.KEM.IncrementalKEM.MLKEM
public import SecureMessaging.KEM.IncrementalKEM.Derandomized
public import SecureMessaging.KEM.MLKEM.Construction

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

`mlkemIncrementalDet` is the incremental KEM with explicit coins built from the same
deterministic algorithms: key generation takes one 64-byte seed, whose first and last 32 bytes are
`d` and `z`, and first-stage encapsulation takes one 32-byte message.
-/

@[expose] public section

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

/-- Incremental ML-KEM with the implementation's coin spaces: one 64-byte key-generation
seed, split into `d` and `z`, and one 32-byte first-stage message. -/
-- ANCHOR: mlkemIncrementalDet
def mlkemIncrementalDet (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p))) :
    IncrementalKEMDet ProbComp SharedSecret
      (EncapsulationKey (ParameterSet.params p)
        (Concrete.concreteEncoding (ParameterSet.params p)))
      (DecapsulationKey (ParameterSet.params p)
        (Concrete.concreteEncoding (ParameterSet.params p)))
      (Ciphertext (ParameterSet.params p)
        (Concrete.concreteEncoding (ParameterSet.params p))) :=
  let inc := mlkemIncremental p ring prims
  { PKheader := inc.PKheader
    PKvector := inc.PKvector
    C₁ := inc.C₁
    C₂ := inc.C₂
    St := inc.St
    KeygenRand := Bytes 64
    Encaps1Rand := Message
    validPK := inc.validPK
    splitPK := inc.splitPK
    splitC := inc.splitC
    keygenDet := fun r => keygenInternal ring
      (Concrete.concreteEncoding (ParameterSet.params p)) prims (r.take 32) (r.drop 32)
    encaps1Det := incrementalEncaps1 ring prims
    encaps2Det := fun st _hdr vec => incrementalEncaps2 ring st vec
    decapsDet := fun sk c => some (decapsInternal ring
      (Concrete.concreteEncoding (ParameterSet.params p)) prims sk c)
    sampleKeygen := $ᵗ Bytes 64
    sampleEncaps1 := $ᵗ Message }
-- ANCHOR_END: mlkemIncrementalDet

end MLKEM
