/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.MLKEM.Correctness.Noise

/-!
# The K-PKE decryption-noise identity

K-PKE decryption recomputes a representative `w` of the encoded message, and the
decryption noise of an honest run is `w - μ` (`kpkeDecryptDifference`). This file
expands that noise over the honest run from key seed `d` and message `m`.
Writing `s`, `e` for the key-generation secret and error, `y`, `e₁`, `e₂` for
the encryption secret and errors, and `ε_u`, `ε_v` for the ciphertext
compression errors (decoded minus original), the right-hand side named
`kpkeNoiseExpression` is

  `eᵀy + e₂ + ε_v − sᵀe₁ − sᵀε_u`.

The main theorem proves `w − μ = kpkeNoiseExpression ring prims d m`, an
equation in `R_q`, with every product computed through the NTT isomorphism as in
FIPS 203 (eq. (4.9); Algorithms 13–15). The public-key term `sᵀÂᵀy` cancels
against the ciphertext term by the transpose exchange, and `μ` enters `v`
additively and is subtracted intact. The right-hand side is deterministic in
`(d, m)`: the decryption noise does not depend on the implicit-rejection seed
`z`.

The first section proves the transform-domain algebra this expansion needs — the
dot product as a finite sum, distributivity of `mulHat` over finite sums, and the
transpose exchange — for any `TransformOps` satisfying `TransformOps.Laws`.
-/

open LatticeCrypto

universe u v

namespace LatticeCrypto.TransformOps

variable {Coeff : Type u} [CommRing Coeff] {ring : NegacyclicRing Coeff} {Hat : Type v}
  [AddCommGroup Hat] (ops : TransformOps ring Hat)

/-- Folding addition over a vector equals the finite sum of its entries. -/
private theorem foldl_add_eq_sum {k : Nat} (w : PolyVec Hat k) :
    w.foldl (· + ·) (0 : Hat) = ∑ i : Fin k, w.get i := by
  induction k with
  | zero =>
    have hw : w = #v[] := Vector.eq_empty
    subst hw
    simp
  | succ n ih =>
    haveI : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
    obtain ⟨w', x, rfl⟩ : ∃ (w' : Vector Hat n) (x : Hat), w = w'.push x :=
      ⟨w.pop, w.back, (Vector.push_pop_back w).symm⟩
    rw [Vector.foldl_push, ih w', Fin.sum_univ_castSucc]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      change w'[i.val] = (w'.push x)[i.val]
      exact (Vector.getElem_push_lt i.isLt).symm
    · change x = (w'.push x)[n]
      exact Vector.getElem_push_eq.symm

/-- The transform-domain dot product as a finite sum of pointwise products. -/
theorem dot_eq_sum {k : Nat} (u v : PolyVec Hat k) :
    ops.dot u v = ∑ i : Fin k, ops.mulHat (u.get i) (v.get i) := by
  change (Vector.zipWith ops.mulHat u v).foldl (· + ·) (0 : Hat) = _
  rw [foldl_add_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change (Vector.zipWith ops.mulHat u v)[i.val] = ops.mulHat u[i.val] v[i.val]
  exact Vector.getElem_zipWith i.isLt

/-- Entry `i` of a matrix-vector product is the dot product of row `i` with the
vector. -/
theorem matVecMul_get {rows cols : Nat} (A : PolyMatrix Hat rows cols)
    (v : PolyVec Hat cols) (i : Fin rows) :
    (ops.matVecMul A v).get i = ops.dot (A.get i) v :=
  Vector.get_map A _ i

/-- Entry `j` of a transposed matrix-vector product is the dot product of column
`j` with the vector. -/
theorem matTransposeVecMul_get {rows cols : Nat} (A : PolyMatrix Hat rows cols)
    (v : PolyVec Hat rows) (j : Fin cols) :
    (ops.matTransposeVecMul A v).get j =
      ops.dot (Vector.ofFn fun i => (A.get i).get j) v := by
  change ((transpose A).map fun row => ops.dot row v).get j = _
  rw [Vector.get_map]
  change ops.dot ((Vector.ofFn fun j => Vector.ofFn fun i => (A.get i).get j).get j) v = _
  rw [Vector.get_ofFn]

variable [laws : Laws ops]

/-- Transform-domain multiplication distributes over a finite sum on the right. -/
theorem mulHat_sum {ι : Type*} (a : Hat) (t : Finset ι) (f : ι → Hat) :
    ops.mulHat a (∑ i ∈ t, f i) = ∑ i ∈ t, ops.mulHat a (f i) :=
  map_sum (AddMonoidHom.mk' (ops.mulHat a) (laws.mul_add a)) f t

/-- Transform-domain multiplication distributes over a finite sum on the left. -/
theorem sum_mulHat {ι : Type*} (t : Finset ι) (f : ι → Hat) (b : Hat) :
    ops.mulHat (∑ i ∈ t, f i) b = ∑ i ∈ t, ops.mulHat (f i) b := by
  rw [mulHat_comm ops, mulHat_sum ops]
  exact Finset.sum_congr rfl fun i _ => mulHat_comm ops b (f i)

/-- The transform-domain dot product is commutative. -/
theorem dot_comm {k : Nat} (u v : PolyVec Hat k) : ops.dot u v = ops.dot v u := by
  rw [dot_eq_sum ops, dot_eq_sum ops]
  exact Finset.sum_congr rfl fun i _ => mulHat_comm ops _ _

/-- The transform-domain dot product is additive in its first argument. -/
theorem dot_add_left {k : Nat} (u v w : PolyVec Hat k) :
    ops.dot (u + v) w = ops.dot u w + ops.dot v w := by
  rw [dot_comm ops (u + v) w, dot_add_right ops w u v, dot_comm ops w u, dot_comm ops w v]

/-- Applying the transform coordinate-wise after the inverse transform is the
identity on transform-domain vectors. -/
theorem hatVec_unhatVec {k : Nat} (vHat : PolyVec Hat k) :
    ops.hatVec (ops.unhatVec vHat) = vHat := by
  refine Vector.ext fun i hi => ?_
  simp only [hatVec, unhatVec, Vector.getElem_map]
  exact laws.toHat_fromHat vHat[i]

/-- Transpose exchange: dotting `s` with `Âᵀ ∘ y` equals dotting `Â ∘ s` with `y`.
This cancels the shared `sᵀÂᵀy` term between K-PKE encryption and decryption. -/
theorem dot_matTransposeVecMul {rows cols : Nat} (A : PolyMatrix Hat rows cols)
    (s : PolyVec Hat cols) (y : PolyVec Hat rows) :
    ops.dot s (ops.matTransposeVecMul A y) = ops.dot (ops.matVecMul A s) y := by
  rw [dot_eq_sum ops, dot_eq_sum ops]
  simp only [matTransposeVecMul_get, matVecMul_get, dot_eq_sum, Vector.get_ofFn,
    mulHat_sum, sum_mulHat]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← mulHat_assoc ops, mulHat_comm ops (s.get j) ((A.get i).get j)]

end LatticeCrypto.TransformOps

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

/-- The representative recomputed by K-PKE decryption of the honest ciphertext,
with the serialization round trips removed: `w = v′ − NTT⁻¹(ŝᵀ ∘ NTT(u′))`, where
`u′` and `v′` are the decompressed decodings of the compressed `u` and `v`. -/
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
