/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.MLKEM.Encoding
import SecureMessaging.KEM.MLKEM.Construction
import ToVCVio.CryptoFoundations.KeyEncapMech.Advantage

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

private theorem encrypt_refines (params : Params) (ring : NTTRingOps)
    (prims : Primitives params (Concrete.concreteEncoding params))
    (pk : EncapsulationKey params (encoding params)) (m : Message) (r : Coins) :
    toRawC params (KPKE.encrypt ring (encoding params) (primitives params prims) pk m r) =
      KPKE.encrypt ring (Concrete.concreteEncoding params) prims (toRawPK params pk) m r := by
  dsimp only [KPKE.encrypt, toRawC, toRawPK, encoding, primitives,
    Primitives.publicMatrix, Primitives.sampleVecEta1, Primitives.sampleVecEta2,
    Concrete.vectorToByteArray]
  apply congrArg₂ KPKE.Ciphertext.mk <;> exact ByteArray.ext_iff.2 rfl

variable (p : ParameterSet) (ring : NTTRingOps)
    (prims : Primitives (ParameterSet.params p)
      (Concrete.concreteEncoding (ParameterSet.params p)))

/-- Key generation preserves the complete public/secret pair and its original samplers. -/
theorem keygen_refines :
    Prod.map (toRawPK (ParameterSet.params p)) (toRawSK (ParameterSet.params p)) <$>
      (scheme p ring prims).keygen = (mlkemScheme p ring prims).keygen := by
  simp only [scheme, mlkemScheme, asKEMScheme, keygen, map_bind, map_pure]
  congr 1

/-- Encapsulation preserves ciphertext bytes, shared secret and the message sampler. -/
theorem encaps_refines
    (pk : EncapsulationKey (ParameterSet.params p) (encoding (ParameterSet.params p))) :
    Prod.map (toRawC (ParameterSet.params p)) id <$> (scheme p ring prims).encaps pk =
      (mlkemScheme p ring prims).encaps (toRawPK (ParameterSet.params p) pk) := by
  simp only [scheme, mlkemScheme, asKEMScheme, map_bind, map_pure]
  congr 1

/-- Decapsulation preserves ciphertext comparison and both implicit-rejection branches. -/
theorem decaps_refines
    (sk : DecapsulationKey (ParameterSet.params p) (encoding (ParameterSet.params p)))
    (c : Ciphertext (ParameterSet.params p) (encoding (ParameterSet.params p))) :
    (scheme p ring prims).decaps sk c =
      (mlkemScheme p ring prims).decaps (toRawSK (ParameterSet.params p) sk)
        (toRawC (ParameterSet.params p) c) := by
  let q := ParameterSet.params p
  have hparse (a : Ciphertext q (encoding q)) : readC q (toRawC q a) = some a :=
    (readC_eq_some_iff q _ a).mpr rfl
  have hinj : Function.Injective (toRawC q) := by
    intro a b h
    apply Option.some.inj
    rw [← hparse a, ← hparse b, h]
  let m := KPKE.decrypt ring (encoding q) (primitives q prims) sk.dkPKE c
  let kr := prims.gEncaps m sk.ekHash
  let c' := KPKE.encrypt ring (encoding q) (primitives q prims) sk.ekPKE m kr.2
  change pure (some (if c = c' then kr.1 else
    prims.jReject sk.z (Concrete.vectorToByteArray c.uEncoded)
      (Concrete.vectorToByteArray c.vEncoded))) =
    pure (some (if toRawC q c =
      KPKE.encrypt ring (Concrete.concreteEncoding q) prims (toRawPK q sk.ekPKE) m kr.2
      then kr.1 else prims.jReject sk.z (Concrete.vectorToByteArray c.uEncoded)
        (Concrete.vectorToByteArray c.vEncoded)))
  rw [← encrypt_refines]
  simp only [hinj.eq_iff]
  rfl

/-- The honest correctness experiments agree as terms, without a correctness premise. -/
theorem correctExp_eq :
    (scheme p ring prims).correctnessExperiment =
      (mlkemScheme p ring prims).correctnessExperiment := by
  unfold KEMScheme.correctnessExperiment
  rw [← keygen_refines p ring prims]
  simp only [bind_map_left, Prod.map]
  apply congrArg (fun f => (scheme p ring prims).keygen >>= f)
  funext pair
  rw [← encaps_refines p ring prims pair.1]
  simp only [bind_map_left, Prod.map, id_eq]
  apply congrArg (fun f => (scheme p ring prims).encaps pair.1 >>= f)
  funext out
  rw [decaps_refines]

/-- Missing success mass is unchanged by the byte representation. -/
theorem correctnessError_eq :
    (scheme p ring prims).correctnessError ProbCompRuntime.probComp =
      (mlkemScheme p ring prims).correctnessError ProbCompRuntime.probComp := by
  unfold KEMScheme.correctnessError
  rw [correctExp_eq]

/-- Run a bounded adversary on raw inputs, rejecting only inadmissible raw lengths. -/
def liftAdversary (A : (scheme p ring prims).IND_CPA_Adversary) :
    (mlkemScheme p ring prims).IND_CPA_Adversary where
  State := Option A.State
  preChallenge rawPK :=
    match readPK (ParameterSet.params p) rawPK with
    | none => pure none
    | some pk => some <$> A.preChallenge pk
  postChallenge st rawC key :=
    match st, readC (ParameterSet.params p) rawC with
    | some s, some c => A.postChallenge s c key
    | _, _ => pure false

/-- Generated raw keys and ciphertexts always parse; both fixed-bit experiments agree. -/
theorem indCPAExp_lift (A : (scheme p ring prims).IND_CPA_Adversary) (b : Bool) :
    IND_CPA_Experiment (kem := mlkemScheme p ring prims) ProbCompRuntime.probComp
      (liftAdversary p ring prims A) b =
        IND_CPA_Experiment (kem := scheme p ring prims) ProbCompRuntime.probComp A b := by
  have hpk (pk : EncapsulationKey (ParameterSet.params p) (encoding (ParameterSet.params p))) :
      readPK (ParameterSet.params p) (toRawPK (ParameterSet.params p) pk) = some pk :=
    (readPK_eq_some_iff _ _ pk).mpr rfl
  have hc (c : Ciphertext (ParameterSet.params p) (encoding (ParameterSet.params p))) :
      readC (ParameterSet.params p) (toRawC (ParameterSet.params p) c) = some c :=
    (readC_eq_some_iff _ _ c).mpr rfl
  unfold IND_CPA_Experiment
  rw [← keygen_refines p ring prims]
  simp only [bind_map_left, Prod.map]
  apply congrArg (fun f => (scheme p ring prims).keygen >>= f)
  funext pair
  simp only [liftAdversary, hpk, bind_map_left]
  apply congrArg (fun f => A.preChallenge pair.1 >>= f)
  funext st
  rw [← encaps_refines p ring prims pair.1]
  simp only [bind_map_left, Prod.map, id_eq, hc]

/-- The raw reduction has exactly the bounded adversary's canonical IND-CPA advantage. -/
theorem indCPAAdvantage_lift (A : (scheme p ring prims).IND_CPA_Adversary) :
    (mlkemScheme p ring prims).IND_CPA_Advantage ProbCompRuntime.probComp
      (liftAdversary p ring prims A) =
        (scheme p ring prims).IND_CPA_Advantage ProbCompRuntime.probComp A := by
  rw [IND_CPA_Advantage_eq_fixed_branch_dist, IND_CPA_Advantage_eq_fixed_branch_dist,
    indCPAExp_lift, indCPAExp_lift]

end MLKEM.Bounded
