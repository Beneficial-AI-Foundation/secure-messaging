/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import LatticeCrypto.MLKEM.Concrete.Instance
import LatticeCrypto.MLKEM.KEM

/-!
# ML-KEM as a key-encapsulation mechanism

FIPS 203 specifies ML-KEM by three algorithms — `ML-KEM.KeyGen` (Algorithm 19),
`ML-KEM.Encaps` (Algorithm 20), and `ML-KEM.Decaps` (Algorithm 21) — together
with three approved parameter sets ML-KEM-512, ML-KEM-768, and ML-KEM-1024
(Section 8, Table 2). This file packages VCV-io's ML-KEM algorithms as one
`KEMScheme` for each approved parameter set.

`mlkemScheme p ring prims` is the scheme at parameter set `p`: key generation
samples the seeds `(d, z)` and runs `ML-KEM.KeyGen_internal`, encapsulation
samples the message `m` and runs `ML-KEM.Encaps_internal`, and decapsulation
runs `ML-KEM.Decaps_internal` with implicit rejection. Byte encoding and
compression are the executable FIPS 203 codec; the NTT and the SHA-3 family
primitives are the two supplied slots. `mlkem512Scheme`, `mlkem768Scheme`, and
`mlkem1024Scheme` fix those slots to the concrete NTT and the FFI-backed
SHA-3/SHAKE primitives.

The δ-correctness of these schemes under the FIPS 203 noise model is stated in
`SecureMessaging.KEM.MLKEM.Correctness`.
-/

open OracleComp KEMScheme ENNReal

namespace MLKEM

instance decidableEqEncodedTHat (params : Params) :
    DecidableEq (Concrete.concreteEncoding params).EncodedTHat :=
  inferInstanceAs (DecidableEq ByteArray)

instance decidableEqEncodedU (params : Params) :
    DecidableEq (Concrete.concreteEncoding params).EncodedU :=
  inferInstanceAs (DecidableEq ByteArray)

instance decidableEqEncodedV (params : Params) :
    DecidableEq (Concrete.concreteEncoding params).EncodedV :=
  inferInstanceAs (DecidableEq ByteArray)

/-- The ML-KEM key-encapsulation mechanism at the approved parameter set `p`
(FIPS 203 Section 7). Key generation samples the seeds `(d, z)` and runs
`ML-KEM.KeyGen_internal` (Algorithm 19); encapsulation samples the message `m`
and runs `ML-KEM.Encaps_internal` (Algorithm 20); decapsulation runs
`ML-KEM.Decaps_internal` with implicit rejection (Algorithm 21). Byte encoding
and compression are the executable FIPS 203 codec; the NTT `ring` and the
SHA-3 family `prims` are the supplied slots. Input validation lives in the
checked interface `MLKEM.encaps` / `MLKEM.decaps`. -/
def mlkemScheme (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p))) :
    KEMScheme ProbComp SharedSecret
      (EncapsulationKey (ParameterSet.params p)
        (Concrete.concreteEncoding (ParameterSet.params p)))
      (DecapsulationKey (ParameterSet.params p)
        (Concrete.concreteEncoding (ParameterSet.params p)))
      (Ciphertext (ParameterSet.params p)
        (Concrete.concreteEncoding (ParameterSet.params p))) :=
  asKEMScheme ring (Concrete.concreteEncoding (ParameterSet.params p)) prims

/-- ML-KEM-512: `k = 2`, `η₁ = 3`, `η₂ = 2`, `d_u = 10`, `d_v = 4` (FIPS 203
Table 2), with the concrete NTT and the FFI-backed SHA-3/SHAKE primitives. -/
def mlkem512Scheme :
    KEMScheme ProbComp SharedSecret
      (EncapsulationKey mlkem512 Concrete.mlkem512Encoding)
      (DecapsulationKey mlkem512 Concrete.mlkem512Encoding)
      (Ciphertext mlkem512 Concrete.mlkem512Encoding) :=
  mlkemScheme .MLKEM512 Concrete.concreteNTTRingOps Concrete.mlkem512Primitives

/-- ML-KEM-768: `k = 3`, `η₁ = 2`, `η₂ = 2`, `d_u = 10`, `d_v = 4` (FIPS 203
Table 2), with the concrete NTT and the FFI-backed SHA-3/SHAKE primitives. -/
def mlkem768Scheme :
    KEMScheme ProbComp SharedSecret
      (EncapsulationKey mlkem768 Concrete.mlkem768Encoding)
      (DecapsulationKey mlkem768 Concrete.mlkem768Encoding)
      (Ciphertext mlkem768 Concrete.mlkem768Encoding) :=
  mlkemScheme .MLKEM768 Concrete.concreteNTTRingOps Concrete.mlkem768Primitives

/-- ML-KEM-1024: `k = 4`, `η₁ = 2`, `η₂ = 2`, `d_u = 11`, `d_v = 5` (FIPS 203
Table 2), with the concrete NTT and the FFI-backed SHA-3/SHAKE primitives. -/
def mlkem1024Scheme :
    KEMScheme ProbComp SharedSecret
      (EncapsulationKey mlkem1024 Concrete.mlkem1024Encoding)
      (DecapsulationKey mlkem1024 Concrete.mlkem1024Encoding)
      (Ciphertext mlkem1024 Concrete.mlkem1024Encoding) :=
  mlkemScheme .MLKEM1024 Concrete.concreteNTTRingOps Concrete.mlkem1024Primitives

end MLKEM
