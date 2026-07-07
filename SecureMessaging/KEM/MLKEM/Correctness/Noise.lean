/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import LatticeCrypto.MLKEM.KEM
import LatticeCrypto.Ring.Norms

/-!
# ML-KEM K-PKE decryption noise

ML-KEM encryption hides the message `m` by adding it to a noisy mask; K-PKE
decryption recomputes a representative `w` of the message and reads each bit
back with the rounding map `Compress₁`. Decryption is correct exactly when this
recomputed representative is close enough to the encoded message.

Closeness is measured coefficient by coefficient. Each coefficient lives in
`ZMod q` with `q = 3329`. Its *centered representative* is the unique integer in
`[-(q-1)/2, (q-1)/2]` congruent to it — the representative nearest `0`, which may
be negative (`LatticeCrypto.centeredRepr`). The *decryption noise* is the
polynomial `w - μ`, where `μ = Decompress₁(ByteDecode₁ m)` is the encoded
message. Its size is the largest absolute centered representative over all `256`
coefficients (`LatticeCrypto.cInfNorm`, the ℓ∞ norm).

Decryption recovers `m` whenever the decryption noise has size at most the
*recovery radius*. For the ML-KEM message encoding that radius is `831`: one
below `⌊q/4⌋ = 832`, because `Decompress₁(1) = ⌈q/2⌉ = 1665` is not exactly
`q/2`, so a bit-`1` coordinate already decodes to `0` once its noise reaches
`+832`.

This file defines the decryption noise of an honest run, the recovery radius,
and two views of recovery. The radius is a coarse sufficient condition: noise
within it forces K-PKE decryption to return the message. The exact condition is
coordinatewise — decryption recomputes `Compress₁` of a representative and reads
it against the decoded message, so recovery fails exactly when some one of the
`256` coefficients disagrees.
-/

open LatticeCrypto

namespace MLKEM

instance : NeZero modulus := by unfold modulus; exact ⟨by decide⟩

variable {params : Params}
variable (ring : NTTRingOps) (encoding : Encoding params)
  (prims : Primitives params encoding)

/-- The message-recovery radius `831` (see the module comment for its value). -/
def messageRecoveryRadius : ℕ := 831

/-- FIPS 203 message-encoding laws used by the decryption reduction: the abstract
round-trip laws together with `Compress₁ / Decompress₁` message recovery within
`messageRecoveryRadius`. -/
structure FIPS203EncodingLaws (encoding : Encoding params) : Prop where
  /-- The abstract encoding round-trip laws of `encoding`. -/
  laws : encoding.Laws
  /-- `Compress₁` recovers the encoded message from any noisy representative whose
  decryption noise is within `messageRecoveryRadius`. -/
  compress1_recovery : ∀ (w : Rq) (m : Message),
    cInfNorm (w - encoding.decompress1 (encoding.byteDecode1 m)) ≤ messageRecoveryRadius →
    encoding.compress1 w = encoding.byteDecode1 m

/-- The representative `w` that K-PKE decryption recomputes from the honest run
of key seeds `(d, z)` and message `m`, immediately before reading the message
back with `Compress₁`. -/
def kpkeDecryptRepresentative (d z : Seed32) (m : Message) : Rq :=
  let dk := (keygenInternal ring encoding prims d z).2
  let c := (encapsInternal ring encoding prims
    (keygenInternal ring encoding prims d z).1 m).2
  let (u', v') := encoding.decodeCiphertext c.uEncoded c.vEncoded
  let sHat := encoding.byteDecode12Vec dk.dkPKE.sHatEncoded
  v' - ring.invNTT (ring.dot sHat (ring.nttVec u'))

/-- The decryption noise `w - μ` of the honest run from key seeds `(d, z)` and
message `m`, where `w` is the recomputed representative and `μ = Decompress₁(ByteDecode₁ m)`
is the encoded message. -/
def kpkeDecryptDifference (d z : Seed32) (m : Message) : Rq :=
  kpkeDecryptRepresentative ring encoding prims d z m -
    encoding.decompress1 (encoding.byteDecode1 m)

/-- The honest run from `(d, z, m)` has decryption noise within the recovery radius. -/
def kpkeNoiseWithinRecoveryRadius (d z : Seed32) (m : Message) : Prop :=
  cInfNorm (kpkeDecryptDifference ring encoding prims d z m) ≤ messageRecoveryRadius

/-- The honest run from `(d, z, m)` has decryption noise exceeding the recovery
radius; the complement of `kpkeNoiseWithinRecoveryRadius`. -/
def kpkeBadNoise (d z : Seed32) (m : Message) : Prop :=
  messageRecoveryRadius < cInfNorm (kpkeDecryptDifference ring encoding prims d z m)

instance (d z : Seed32) (m : Message) :
    Decidable (kpkeBadNoise ring encoding prims d z m) :=
  Nat.decLt _ _

theorem kpkeBadNoise_iff_not_within (d z : Seed32) (m : Message) :
    kpkeBadNoise ring encoding prims d z m ↔
      ¬ kpkeNoiseWithinRecoveryRadius ring encoding prims d z m := by
  rw [kpkeBadNoise, kpkeNoiseWithinRecoveryRadius, not_le]

/-- Noise within the recovery radius forces K-PKE decryption of the honest
encapsulation ciphertext to return the original message. -/
theorem kpke_decrypt_eq_of_noiseWithinRecoveryRadius
    (hEnc : FIPS203EncodingLaws encoding) (d z : Seed32) (m : Message)
    (hWithin : kpkeNoiseWithinRecoveryRadius ring encoding prims d z m) :
    KPKE.decrypt ring encoding prims (keygenInternal ring encoding prims d z).2.dkPKE
        (encapsInternal ring encoding prims
          (keygenInternal ring encoding prims d z).1 m).2 = m := by
  simp only [kpkeNoiseWithinRecoveryRadius, kpkeDecryptDifference,
    kpkeDecryptRepresentative, Encoding.decodeCiphertext] at hWithin
  simp only [KPKE.decrypt, Encoding.decodeCiphertext]
  rw [hEnc.compress1_recovery _ m hWithin]
  exact hEnc.laws.byteEncode1_byteDecode1 m

/-- Coordinate `i` of K-PKE decryption fails: `Compress₁` of the recomputed
representative disagrees with the decoded message at `i`. This is the exact,
message-dependent decoding event, not the symmetric norm condition. -/
def kpkeCoordinateDecodeFailure (d z : Seed32) (m : Message) (i : Fin ringDegree) : Prop :=
  (encoding.compress1 (kpkeDecryptRepresentative ring encoding prims d z m)).get i ≠
    (encoding.byteDecode1 m).get i

/-- K-PKE decryption of the honest encapsulation ciphertext fails to recover `m`
exactly when some one of the `256` coefficients of `Compress₁` of the recomputed
representative disagrees with the decoded message. Both directions hold under the
encoding round-trip laws. -/
theorem kpke_decrypt_ne_iff_exists_coordinateDecodeFailure
    (hEnc : encoding.Laws) (d z : Seed32) (m : Message) :
    KPKE.decrypt ring encoding prims (keygenInternal ring encoding prims d z).2.dkPKE
        (encapsInternal ring encoding prims
          (keygenInternal ring encoding prims d z).1 m).2 ≠ m ↔
      ∃ i : Fin ringDegree, kpkeCoordinateDecodeFailure ring encoding prims d z m i := by
  have hdec : KPKE.decrypt ring encoding prims (keygenInternal ring encoding prims d z).2.dkPKE
        (encapsInternal ring encoding prims
          (keygenInternal ring encoding prims d z).1 m).2 =
      encoding.byteEncode1 (encoding.compress1
        (kpkeDecryptRepresentative ring encoding prims d z m)) := rfl
  have hrecover : encoding.byteEncode1 (encoding.compress1
        (kpkeDecryptRepresentative ring encoding prims d z m)) = m ↔
      encoding.compress1 (kpkeDecryptRepresentative ring encoding prims d z m) =
        encoding.byteDecode1 m := by
    constructor
    · intro h
      have h' := congrArg encoding.byteDecode1 h
      rwa [hEnc.byteDecode1_byteEncode1_compress1] at h'
    · intro h
      have h' := congrArg encoding.byteEncode1 h
      rwa [hEnc.byteEncode1_byteDecode1] at h'
  rw [hdec, ne_eq, hrecover]
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    exact h (Poly.ext_get_eq fun i => not_not.mp (hcon i))
  · rintro ⟨i, hi⟩ heq
    exact hi (by rw [heq])

end MLKEM
