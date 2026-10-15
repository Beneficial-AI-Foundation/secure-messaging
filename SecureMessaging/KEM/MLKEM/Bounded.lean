/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.MLKEM.Encoding
import SecureMessaging.KEM.MLKEM.Construction

/-!
# Fixed-length byte representations of ML-KEM

Encoding outputs are packaged as the existing array-backed byte vectors, and decoding first
forgets that length evidence without altering bytes. Primitive functions are the supplied raw
functions composed only with this forgetting map. Raw admissibility checks exact lengths, not
canonicality, hashes or membership in the key-generation image.
-/

open OracleComp KEMScheme

namespace MLKEM.Bounded

/-- The concrete encoder with fixed-length public-vector and ciphertext representations. -/
def encoding (params : Params) : Encoding params where
  EncodedTHat := Bytes (384 * params.k)
  EncodedU := Bytes (32 * params.du * params.k)
  EncodedV := Bytes (32 * params.dv)
  byteEncode12Vec v :=
    ⟨((Concrete.concreteEncoding params).byteEncode12Vec v).data,
      ByteArray.size_data.trans (Concrete.concreteEncoding_tHat_size params v)⟩
  byteEncodeDUVec v :=
    ⟨((Concrete.concreteEncoding params).byteEncodeDUVec v).data,
      ByteArray.size_data.trans (Concrete.concreteEncoding_u_size params v)⟩
  byteEncodeDV v :=
    ⟨((Concrete.concreteEncoding params).byteEncodeDV v).data,
      ByteArray.size_data.trans (Concrete.concreteEncoding_v_size params v)⟩
  byteDecode12Vec v := (Concrete.concreteEncoding params).byteDecode12Vec
    (Concrete.vectorToByteArray v)
  byteDecodeDUVec v := (Concrete.concreteEncoding params).byteDecodeDUVec
    (Concrete.vectorToByteArray v)
  byteDecodeDV v := (Concrete.concreteEncoding params).byteDecodeDV
    (Concrete.vectorToByteArray v)
  byteDecode12Vec_byteEncode12Vec v := by
    have h : ByteArray.mk (((Concrete.concreteEncoding params).byteEncode12Vec v).data) =
        (Concrete.concreteEncoding params).byteEncode12Vec v := ByteArray.ext_iff.2 rfl
    change (Concrete.concreteEncoding params).byteDecode12Vec
      (ByteArray.mk (((Concrete.concreteEncoding params).byteEncode12Vec v).data)) = v
    rw [h]
    exact (Concrete.concreteEncoding params).byteDecode12Vec_byteEncode12Vec v
  compressDU := (Concrete.concreteEncoding params).compressDU
  decompressDU := (Concrete.concreteEncoding params).decompressDU
  compressDV := (Concrete.concreteEncoding params).compressDV
  decompressDV := (Concrete.concreteEncoding params).decompressDV
  compress1 := (Concrete.concreteEncoding params).compress1
  decompress1 := (Concrete.concreteEncoding params).decompress1
  byteEncode1 := (Concrete.concreteEncoding params).byteEncode1
  byteDecode1 := (Concrete.concreteEncoding params).byteDecode1

instance decidableEqEncodedTHat (params : Params) :
    DecidableEq (encoding params).EncodedTHat :=
  inferInstanceAs (DecidableEq (Bytes (384 * params.k)))

instance decidableEqEncodedU (params : Params) :
    DecidableEq (encoding params).EncodedU :=
  inferInstanceAs (DecidableEq (Bytes (32 * params.du * params.k)))

instance decidableEqEncodedV (params : Params) :
    DecidableEq (encoding params).EncodedV :=
  inferInstanceAs (DecidableEq (Bytes (32 * params.dv)))

/-- The supplied raw primitives, with exact forgetting at their encoded-byte inputs. -/
def primitives (params : Params)
    (prims : Primitives params (Concrete.concreteEncoding params)) :
    Primitives params (encoding params) where
  gKeygen := prims.gKeygen
  sampleNTT := prims.sampleNTT
  prfEta1 := prims.prfEta1
  prfEta2 := prims.prfEta2
  gEncaps := prims.gEncaps
  hEncapsulationKey v r := prims.hEncapsulationKey (Concrete.vectorToByteArray v) r
  jReject z u v := prims.jReject z (Concrete.vectorToByteArray u) (Concrete.vectorToByteArray v)

/-- The unchanged internal ML-KEM algorithms using the bounded representation adapter. -/
def scheme (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p))) :
    KEMScheme ProbComp SharedSecret
      (EncapsulationKey (ParameterSet.params p) (encoding (ParameterSet.params p)))
      (DecapsulationKey (ParameterSet.params p) (encoding (ParameterSet.params p)))
      (Ciphertext (ParameterSet.params p) (encoding (ParameterSet.params p))) :=
  asKEMScheme ring (encoding (ParameterSet.params p))
    (primitives (ParameterSet.params p) prims)

/-- Read every byte string of exactly the requested length, rejecting every other length. -/
def readBytes (n : ℕ) (b : ByteArray) : Option (Bytes n) :=
  if h : b.size = n then some ⟨b.data, h⟩ else none

/-- Successful parsing is exactly inverse to the existing byte-array forgetting map. -/
theorem readBytes_eq_some_iff {n : ℕ} {b : ByteArray} {v : Bytes n} :
    readBytes n b = some v ↔ Concrete.vectorToByteArray v = b := by
  constructor
  · intro h
    unfold readBytes at h
    split_ifs at h with hb
    have hv := Option.some.inj h
    rw [← hv]
    change ByteArray.mk b.data = b
    exact ByteArray.ext_iff.2 rfl
  · intro h
    rw [← h]
    rcases v with ⟨a, ha⟩
    simp [readBytes, Concrete.vectorToByteArray, ByteArray.size, ha]

/-- Forget only the public-vector length evidence, preserving the public seed. -/
def toRawPK (params : Params) :
    EncapsulationKey params (encoding params) →
      EncapsulationKey params (Concrete.concreteEncoding params) :=
  fun pk => { tHatEncoded := Concrete.vectorToByteArray pk.tHatEncoded, rho := pk.rho }

/-- Forget the two encoded secret/public vectors, preserving hash and rejection seed. -/
def toRawSK (params : Params) :
    DecapsulationKey params (encoding params) →
      DecapsulationKey params (Concrete.concreteEncoding params) :=
  fun sk =>
    { dkPKE := { sHatEncoded := Concrete.vectorToByteArray sk.dkPKE.sHatEncoded }
      ekPKE := toRawPK params sk.ekPKE
      ekHash := sk.ekHash
      z := sk.z }

/-- Forget both ciphertext component lengths without re-encoding their bytes. -/
def toRawC (params : Params) :
    Ciphertext params (encoding params) →
      Ciphertext params (Concrete.concreteEncoding params) :=
  fun c =>
    { uEncoded := Concrete.vectorToByteArray c.uEncoded
      vEncoded := Concrete.vectorToByteArray c.vEncoded }

/-- Check only the exact raw public-vector length, preserving the public seed. -/
def readPK (params : Params) :
    EncapsulationKey params (Concrete.concreteEncoding params) →
      Option (EncapsulationKey params (encoding params)) :=
  fun pk => do
    let v ← readBytes (384 * params.k) pk.tHatEncoded
    pure { tHatEncoded := v, rho := pk.rho }

/-- Check both exact raw ciphertext component lengths; reject either mismatch. -/
def readC (params : Params) :
    Ciphertext params (Concrete.concreteEncoding params) →
      Option (Ciphertext params (encoding params)) :=
  fun c => do
    let u ← readBytes (32 * params.du * params.k) c.uEncoded
    let v ← readBytes (32 * params.dv) c.vEncoded
    pure { uEncoded := u, vEncoded := v }

/-- Raw public-key parsing succeeds exactly on the image of byte forgetting. -/
theorem readPK_eq_some_iff (params : Params)
    (raw : EncapsulationKey params (Concrete.concreteEncoding params))
    (bounded : EncapsulationKey params (encoding params)) :
    readPK params raw = some bounded ↔ toRawPK params bounded = raw := by
  rcases raw with ⟨rawBytes, rho⟩
  rcases bounded with ⟨vec, rho'⟩
  constructor
  · intro h
    obtain ⟨v, hv, heq⟩ := Option.bind_eq_some_iff.mp h
    have heq' := Option.some.inj heq
    have hvec := congrArg KPKE.PublicKey.tHatEncoded heq'
    have hrho : rho = rho' := congrArg KPKE.PublicKey.rho heq'
    have hbytes : Concrete.vectorToByteArray vec = rawBytes :=
      (congrArg Concrete.vectorToByteArray hvec).symm.trans (readBytes_eq_some_iff.mp hv)
    change (KPKE.PublicKey.mk (Concrete.vectorToByteArray vec) rho' :
      EncapsulationKey params (Concrete.concreteEncoding params)) = KPKE.PublicKey.mk rawBytes rho
    rw [hbytes, hrho]
  · intro h
    have hbytes := congrArg KPKE.PublicKey.tHatEncoded h
    have hrho : rho' = rho := congrArg KPKE.PublicKey.rho h
    apply Option.bind_eq_some_iff.mpr
    refine ⟨vec, readBytes_eq_some_iff.mpr hbytes, ?_⟩
    change some (KPKE.PublicKey.mk vec rho : EncapsulationKey params (encoding params)) =
      some (KPKE.PublicKey.mk vec rho')
    rw [hrho]

/-- Raw ciphertext parsing succeeds exactly on the image of byte forgetting. -/
theorem readC_eq_some_iff (params : Params)
    (raw : Ciphertext params (Concrete.concreteEncoding params))
    (bounded : Ciphertext params (encoding params)) :
    readC params raw = some bounded ↔ toRawC params bounded = raw := by
  rcases raw with ⟨rawU, rawV⟩
  rcases bounded with ⟨boundedU, boundedV⟩
  constructor
  · intro h
    obtain ⟨u, hu, heq⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, hv, heq⟩ := Option.bind_eq_some_iff.mp heq
    have heq' := Option.some.inj heq
    have hue := congrArg KPKE.Ciphertext.uEncoded heq'
    have hve := congrArg KPKE.Ciphertext.vEncoded heq'
    have hU : Concrete.vectorToByteArray boundedU = rawU :=
      (congrArg Concrete.vectorToByteArray hue).symm.trans (readBytes_eq_some_iff.mp hu)
    have hV : Concrete.vectorToByteArray boundedV = rawV :=
      (congrArg Concrete.vectorToByteArray hve).symm.trans (readBytes_eq_some_iff.mp hv)
    change (KPKE.Ciphertext.mk (Concrete.vectorToByteArray boundedU)
      (Concrete.vectorToByteArray boundedV) :
      Ciphertext params (Concrete.concreteEncoding params)) = KPKE.Ciphertext.mk rawU rawV
    rw [hU, hV]
  · intro h
    have hu := congrArg KPKE.Ciphertext.uEncoded h
    have hv := congrArg KPKE.Ciphertext.vEncoded h
    apply Option.bind_eq_some_iff.mpr
    refine ⟨boundedU, readBytes_eq_some_iff.mpr hu, ?_⟩
    apply Option.bind_eq_some_iff.mpr
    exact ⟨boundedV, readBytes_eq_some_iff.mpr hv, rfl⟩

end MLKEM.Bounded
