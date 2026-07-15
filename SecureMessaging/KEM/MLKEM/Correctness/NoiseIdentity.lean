/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.MLKEM.Correctness.Noise
import ToVCVio.LatticeCrypto.TransformOps

/-!
# The K-PKE decryption-noise identity

Fix `q=3329`, `n=256`, and `R_q=(ℤ/qℤ)[X]/(X^n+1)`.  Fix an honest key seed
`d`, implicit-rejection seed `z`, and message `m`.  The following elements of
`R_q` (or vectors/matrices over it) are defined in this file:

Every element of `R_q` has a representative of degree less than `n`.  Thus
`w-μ` is called a decryption-noise polynomial because it is an element of this
polynomial quotient ring; the matrix `A` is a matrix over the same ring.

* `A`, `s`, and `e`: the public matrix, secret vector, and error vector from
  K-PKE key generation;
* `y`, `e₁`, and `e₂`: the secret vector and errors from K-PKE encryption;
* `μ = Decompress₁(ByteDecode₁(m))`: the message polynomial;
* `u = Aᵀy+e₁` and `v = (As+e)ᵀy+e₂+μ`: the uncompressed ciphertext;
* `ε_u = Decompress_{d_u}(Compress_{d_u}(u))-u` and
  `ε_v = Decompress_{d_v}(Compress_{d_v}(v))-v`: compression errors;
* `w = v' - sᵀu'`: the representative recomputed by decryption from the
  decompressed ciphertext `(u',v')`.

All products in the implementation are transported through the NTT.  Under
`NTTRingLaws ring`, `TransformOps.dot_matTransposeVecMul` gives

`sᵀ(Aᵀy) = (As)ᵀy`.

Consequently the public-matrix terms cancel and the main theorem
`kpkeDecryptDifference_eq_noise` proves the equality in `R_q`

`w - μ = eᵀy + e₂ + ε_v - sᵀe₁ - sᵀε_u`.                (1)

The right side is `kpkeNoiseExpression ring prims d m`.  It contains no `z`:
the implicit-rejection seed affects the fallback key, not the honest K-PKE
ciphertext arithmetic.  The generic transform identities used here live in
`ToVCVio.LatticeCrypto.TransformOps`.
-/

open LatticeCrypto

namespace MLKEM

/-- The secret vector `s` sampled by honest K-PKE key generation from seed `d`
(FIPS 203, Algorithm 13). -/
def kpkeSecret {params : Params} {encoding : Encoding params}
    (prims : Primitives params encoding) (d : Seed32) : RqVec params.k :=
  prims.sampleVecEta1 (prims.gKeygen d).2 0

/-- The error vector `e` sampled by honest K-PKE key generation from seed `d`
(FIPS 203, Algorithm 13). -/
def kpkeKeygenError {params : Params} {encoding : Encoding params}
    (prims : Primitives params encoding) (d : Seed32) : RqVec params.k :=
  prims.sampleVecEta1 (prims.gKeygen d).2 params.k

/-- The public matrix `Â` expanded from the honest key-generation seed `d`
(FIPS 203, Algorithm 13). -/
def kpkeMatrix {params : Params} {encoding : Encoding params}
    (prims : Primitives params encoding) (d : Seed32) : TqMatrix params.k params.k :=
  prims.publicMatrix (prims.gKeygen d).1

/-- The encryption randomness `r` derived by honest encapsulation of message `m`
under the key generated from seed `d` (FIPS 203, Algorithm 17). -/
def kpkeCoins {params : Params} {encoding : Encoding params} (ring : NTTRingOps)
    (prims : Primitives params encoding) (d : Seed32) (m : Message) : Coins :=
  (prims.gEncaps m (encapsulationKeyHash encoding prims
    (KPKE.keygenFromSeed ring encoding prims d).1)).2

/-- The encryption secret vector `y` sampled from the honest encryption
randomness (FIPS 203, Algorithm 14). -/
def kpkeEncryptionSecret {params : Params} {encoding : Encoding params} (ring : NTTRingOps)
    (prims : Primitives params encoding) (d : Seed32) (m : Message) : RqVec params.k :=
  prims.sampleVecEta1 (kpkeCoins ring prims d m) 0

/-- The encryption error vector `e₁` sampled from the honest encryption
randomness (FIPS 203, Algorithm 14). -/
def kpkeEncryptionError1 {params : Params} {encoding : Encoding params} (ring : NTTRingOps)
    (prims : Primitives params encoding) (d : Seed32) (m : Message) : RqVec params.k :=
  prims.sampleVecEta2 (kpkeCoins ring prims d m) params.k

/-- The encryption error polynomial `e₂` sampled from the honest encryption
randomness (FIPS 203, Algorithm 14). -/
def kpkeEncryptionError2 {params : Params} {encoding : Encoding params} (ring : NTTRingOps)
    (prims : Primitives params encoding) (d : Seed32) (m : Message) : Rq :=
  prims.prfEta2 (kpkeCoins ring prims d m) (2 * params.k)

/-- The ciphertext component `u = NTT⁻¹(Âᵀ ∘ ŷ) + e₁` computed by honest
encryption, before compression (FIPS 203, Algorithm 14). -/
def kpkeU {params : Params} {encoding : Encoding params} (ring : NTTRingOps)
    (prims : Primitives params encoding) (d : Seed32) (m : Message) : RqVec params.k :=
  ring.invNTTVec (ring.matTransposeVecMul (kpkeMatrix prims d)
    (ring.nttVec (kpkeEncryptionSecret ring prims d m))) +
    kpkeEncryptionError1 ring prims d m

/-- The ciphertext component `v = NTT⁻¹(t̂ᵀ ∘ ŷ) + e₂ + μ` computed by honest
encryption, before compression, with the decoded public value `t̂ = Â ∘ ŝ + ê`
written out (FIPS 203, Algorithm 14). -/
def kpkeV {params : Params} {encoding : Encoding params} (ring : NTTRingOps)
    (prims : Primitives params encoding) (d : Seed32) (m : Message) : Rq :=
  ring.invNTT (ring.dot
    (ring.matVecMul (kpkeMatrix prims d) (ring.nttVec (kpkeSecret prims d)) +
      ring.nttVec (kpkeKeygenError prims d))
    (ring.nttVec (kpkeEncryptionSecret ring prims d m))) +
    kpkeEncryptionError2 ring prims d m +
    encoding.decompress1 (encoding.byteDecode1 m)

/-- The `u`-compression error `ε_u`: the decoded ciphertext vector
`Decompress_du(Compress_du(u))` minus the original `u`. -/
def kpkeCompressionErrorU {params : Params} {encoding : Encoding params} (ring : NTTRingOps)
    (prims : Primitives params encoding) (d : Seed32) (m : Message) : RqVec params.k :=
  encoding.decompressDU (encoding.compressDU (kpkeU ring prims d m)) -
    kpkeU ring prims d m

/-- The `v`-compression error `ε_v`: the decoded ciphertext polynomial
`Decompress_dv(Compress_dv(v))` minus the original `v`. -/
def kpkeCompressionErrorV {params : Params} {encoding : Encoding params} (ring : NTTRingOps)
    (prims : Primitives params encoding) (d : Seed32) (m : Message) : Rq :=
  encoding.decompressDV (encoding.compressDV (kpkeV ring prims d m)) -
    kpkeV ring prims d m

/-- The deterministic decryption-noise expression

`eᵀy + e₂ + ε_v − sᵀe₁ − sᵀε_u`

for the honest run from key seed `d` and message `m`. The argument `z` is absent
because this expression expands the K-PKE algebra; the implicit-rejection seed
does not appear in the ciphertext arithmetic. -/
def kpkeNoiseExpression {params : Params} {encoding : Encoding params} (ring : NTTRingOps)
    (prims : Primitives params encoding) (d : Seed32) (m : Message) : Rq :=
  ring.invNTT (ring.dot (ring.nttVec (kpkeKeygenError prims d))
      (ring.nttVec (kpkeEncryptionSecret ring prims d m))) +
    kpkeEncryptionError2 ring prims d m +
    kpkeCompressionErrorV ring prims d m -
    ring.invNTT (ring.dot (ring.nttVec (kpkeSecret prims d))
      (ring.nttVec (kpkeEncryptionError1 ring prims d m))) -
    ring.invNTT (ring.dot (ring.nttVec (kpkeSecret prims d))
      (ring.nttVec (kpkeCompressionErrorU ring prims d m)))

/-- Let `u = kpkeU ring prims d m`, `v = kpkeV ring prims d m`, and let

`u' = Decompress_{d_u}(Compress_{d_u}(u))`,
`v' = Decompress_{d_v}(Compress_{d_v}(v))`.

If serialization followed by deserialization, i.e. a roundtrip, recovers the encoded values, the
representative computed by
decryption of the serialized honest ciphertext is exactly

`w = v' - NTT⁻¹(NTT(s)ᵀ ∘ NTT(u'))`,

where `s = kpkeSecret prims d`.  This theorem is the precise bridge from the
serialization-level definition `kpkeDecryptRepresentative` to the algebraic
ciphertext components used in the noise identity. -/
theorem kpkeDecryptRepresentative_eq {params : Params} {encoding : Encoding params}
    (ring : NTTRingOps) (prims : Primitives params encoding) (hEnc : encoding.Laws)
    (d z : Seed32) (m : Message) :
    kpkeDecryptRepresentative ring encoding prims d z m =
      encoding.decompressDV (encoding.compressDV (kpkeV ring prims d m)) -
        ring.invNTT (ring.dot (ring.nttVec (kpkeSecret prims d))
          (ring.nttVec (encoding.decompressDU (encoding.compressDU
            (kpkeU ring prims d m))))) := by
  have hs : encoding.byteDecode12Vec
      ((keygenInternal ring encoding prims d z).2.dkPKE.sHatEncoded) =
      ring.nttVec (kpkeSecret prims d) := by
    change encoding.byteDecode12Vec (encoding.byteEncode12Vec
      (ring.nttVec (kpkeSecret prims d))) = ring.nttVec (kpkeSecret prims d)
    exact encoding.byteDecode12Vec_byteEncode12Vec _
  have hu : encoding.byteDecodeDUVec
      ((encapsInternal ring encoding prims
        (keygenInternal ring encoding prims d z).1 m).2.uEncoded) =
      encoding.compressDU (kpkeU ring prims d m) := by
    change encoding.byteDecodeDUVec (encoding.byteEncodeDUVec
      (encoding.compressDU (kpkeU ring prims d m))) = _
    exact hEnc.byteDecodeDUVec_byteEncodeDUVec_compressDU _
  have hv : encoding.byteDecodeDV
      ((encapsInternal ring encoding prims
        (keygenInternal ring encoding prims d z).1 m).2.vEncoded) =
      encoding.compressDV (kpkeV ring prims d m) := by
    change encoding.byteDecodeDV (encoding.byteEncodeDV (encoding.compressDV
      (ring.invNTT (ring.dot
        (encoding.byteDecode12Vec (encoding.byteEncode12Vec
          (ring.matVecMul (kpkeMatrix prims d) (ring.nttVec (kpkeSecret prims d)) +
            ring.nttVec (kpkeKeygenError prims d))))
        (ring.nttVec (kpkeEncryptionSecret ring prims d m))) +
        kpkeEncryptionError2 ring prims d m +
        encoding.decompress1 (encoding.byteDecode1 m)))) = _
    rw [encoding.byteDecode12Vec_byteEncode12Vec]
    exact hEnc.byteDecodeDV_byteEncodeDV_compressDV _
  change encoding.decompressDV (encoding.byteDecodeDV
      ((encapsInternal ring encoding prims
        (keygenInternal ring encoding prims d z).1 m).2.vEncoded)) -
    ring.invNTT (ring.dot
      (encoding.byteDecode12Vec ((keygenInternal ring encoding prims d z).2.dkPKE.sHatEncoded))
      (ring.nttVec (encoding.decompressDU (encoding.byteDecodeDUVec
        ((encapsInternal ring encoding prims
          (keygenInternal ring encoding prims d z).1 m).2.uEncoded))))) = _
  rw [hs, hu, hv]

/-- The decryption-noise identity: over the honest run from `(d, z, m)`,

  `w − μ = eᵀy + e₂ + ε_v − sᵀe₁ − sᵀε_u`,

with every product computed through the NTT isomorphism. Here `s` is the secret
key vector, `e` is the key-generation error vector, `y` is the encapsulation
secret vector, `e₁` and `e₂` are the encapsulation error terms, and `ε_u`, `ε_v`
are the compression round-trip errors for the ciphertext components. The
right-hand side does not depend on the implicit-rejection seed `z`. -/
theorem kpkeDecryptDifference_eq_noise {params : Params} {encoding : Encoding params}
    (ring : NTTRingOps) (prims : Primitives params encoding)
    (hEnc : encoding.Laws) (hRing : NTTRingLaws ring) (d z : Seed32) (m : Message) :
    kpkeDecryptDifference ring encoding prims d z m = kpkeNoiseExpression ring prims d m := by
  haveI : LatticeCrypto.TransformOps.Laws ring := hRing
  have hv : encoding.decompressDV (encoding.compressDV (kpkeV ring prims d m)) =
      kpkeV ring prims d m + kpkeCompressionErrorV ring prims d m := by
    unfold kpkeCompressionErrorV
    abel
  have hu : encoding.decompressDU (encoding.compressDU (kpkeU ring prims d m)) =
      kpkeU ring prims d m + kpkeCompressionErrorU ring prims d m := by
    unfold kpkeCompressionErrorU
    refine Vector.ext fun i hi => ?_
    simp only [Vector.getElem_add, Vector.getElem_sub]
    abel
  unfold kpkeDecryptDifference
  rw [kpkeDecryptRepresentative_eq ring prims hEnc d z m, hv, hu]
  unfold kpkeU kpkeV kpkeNoiseExpression
  simp only [TransformOps.hatVec_add, TransformOps.hatVec_unhatVec,
    TransformOps.dot_add_right, TransformOps.dot_add_left,
    TransformOps.dot_matTransposeVecMul, TransformOps.fromHat_addHat]
  abel

end MLKEM
