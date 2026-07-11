/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import LatticeCrypto.MLKEM.KEM
import LatticeCrypto.Ring.Norms

/-!
# ML-KEM K-PKE decryption noise

Let `q = 3329` and let

`R_q = (ℤ/qℤ)[X] / (X^256 + 1)`.

In Lean this ring is the type `Rq`. Its coefficients are residues modulo `q`;
when an integer representative is needed we use the centered representative in
`[-(q-1)/2, (q-1)/2]`.

Fix an honest run from key-generation seeds `(d, z)` and encapsulated message
`m`. Key generation gives a decapsulation key, encapsulation gives a ciphertext,
and K-PKE decryption recomputes the polynomial

`w = v′ - ŝᵀ NTT(u′)`.

Here `(u′, v′)` are the decompressed ciphertext components decoded from the
compressed ciphertext, `ŝ` is the secret vector stored in the decapsulation key,
and `NTT` is the number-theoretic transform used by ML-KEM to multiply
polynomials in transform representation. Thus `w ∈ R_q` is the representative
from which decryption reads the message by applying `Compress₁` coefficientwise.

The encoded message polynomial is

`μ = Decompress₁(ByteDecode₁ m)`.

The decryption noise is the polynomial `w - μ ∈ R_q`. Coefficientwise, each
entry lies in `ZMod q`; its size is measured by applying
`LatticeCrypto.centeredRepr` to each coefficient and then taking the
coefficientwise `ℓ∞` norm (`LatticeCrypto.cInfNorm`).

There are two recovery statements in this file. The norm statement is a simple
sufficient condition: if every centered coefficient of `w - μ` has absolute
value at most `⌊q/4⌋ - 1 = 831`, then `Compress₁ w` reads back the original
message bits. The exact statement is coordinatewise: coefficient `i` fails
precisely when

`(Compress₁ w)_i ≠ (ByteDecode₁ m)_i`.

The later failure-bound proof uses this exact coordinate event, not the coarser
symmetric-radius condition.
-/

open LatticeCrypto

namespace MLKEM

instance : NeZero modulus := by unfold modulus; exact ⟨by decide⟩

variable {params : Params}
variable (ring : NTTRingOps) (encoding : Encoding params)
  (prims : Primitives params encoding)

/-- The message-recovery radius `⌊q/4⌋ - 1` for the ML-KEM modulus `q = 3329`
(see the module comment for why this is the safe symmetric radius). -/
def messageRecoveryRadius : ℕ := modulus / 4 - 1

@[simp] theorem messageRecoveryRadius_eq : messageRecoveryRadius = 831 := by
  norm_num [messageRecoveryRadius, modulus]

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

/-- Coordinate `i` of K-PKE decryption fails: if `w` is the recomputed
representative, then `(Compress₁ w)_i` disagrees with the decoded message bit
`(ByteDecode₁ m)_i`. This is the exact, message-dependent decoding event, not
the symmetric norm condition. -/
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
