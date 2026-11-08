/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Basic

/-!
# Correctness of the FrodoPKE and FrodoKEM constructions

This file connects the FrodoPKE and FrodoKEM algorithms to the decoding result of `Basic.lean`.
If the noise matrix is small, decryption returns the message. The file also gives key generation
and encapsulation as functions of their random inputs (`KEM.keygenFromCoins`,
`KEM.encapsFromCoins`). Thus the correctness statements can name each choice of those inputs.
-/

@[expose] public section

namespace FrodoKEM

open OracleComp LatticeCrypto

/-- Every entry `e` of `E`, taken as an integer between `-q / 2` and `q / 2`, satisfies the
decoding condition `-q ≤ 2 ^ (B + 1) * e < q` of `dc_ec_add`. -/
def NoiseBound (p : Params) (E : FrodoMatrix p mbar nbar) : Prop :=
  (∀ i j, -(p.q : ℤ) ≤
    2 ^ (p.B + 1) * centeredRepr (E i j)) ∧
  (∀ i j, 2 ^ (p.B + 1) * centeredRepr (E i j) <
    (p.q : ℤ))

namespace PKE

/-- The secret and error matrices determined by a key-generation sampling seed. -/
def keygenSamples {ps : ParameterSet} (ops : Operations ps)
    (seedSE : SeedSEBits ps) :
    PKESecretKey ps × FrodoMatrix ps.params ps.params.n nbar :=
  let p := ps.params
  let stream := ops.shake
    (keygenPrefix.toList ++ seedSE.toList)
    (nbar * p.n * lenChi + p.n * nbar * lenChi)
  let samples := splitBits
    (a := nbar * p.n * lenChi)
    (b := p.n * nbar * lenChi) stream
  let st := (SampleMatrix ps.errorTable nbar p.n samples.1).map
    (fun x : ℤ => (x : ZMod p.q))
  let e := (SampleMatrix ps.errorTable p.n nbar samples.2).map
    (fun x : ℤ => (x : ZMod p.q))
  (st, e)

/-- The three error-sampling matrices determined by an encryption sampling seed. -/
def encryptionSamples {ps : ParameterSet} (ops : Operations ps)
    (seedSE : SeedSEBits ps) :
    FrodoMatrix ps.params mbar ps.params.n ×
      FrodoMatrix ps.params mbar ps.params.n ×
      FrodoMatrix ps.params mbar nbar :=
  let p := ps.params
  let stream := ops.shake
    (encryptionPrefix.toList ++ seedSE.toList)
    (mbar * p.n * lenChi +
      (mbar * p.n * lenChi + mbar * nbar * lenChi))
  let first := splitBits
    (a := mbar * p.n * lenChi)
    (b := mbar * p.n * lenChi + mbar * nbar * lenChi) stream
  let rest := splitBits
    (a := mbar * p.n * lenChi)
    (b := mbar * nbar * lenChi) first.2
  let sp := (SampleMatrix ps.errorTable mbar p.n first.1).map
    (fun x : ℤ => (x : ZMod p.q))
  let ep := (SampleMatrix ps.errorTable mbar p.n rest.1).map
    (fun x : ℤ => (x : ZMod p.q))
  let epp := (SampleMatrix ps.errorTable mbar nbar rest.2).map
    (fun x : ℤ => (x : ZMod p.q))
  (sp, (ep, epp))

/-- The noise matrix, mod `q`, that remains in the PKE decryption matrix. -/
def decryptionNoise {ps : ParameterSet} (ops : Operations ps)
    (keySeed encSeed : SeedSEBits ps) :
    FrodoMatrix ps.params mbar nbar :=
  let kg := keygenSamples ops keySeed
  let enc := encryptionSamples ops encSeed
  enc.1 * kg.2 + enc.2.2 - enc.2.1 * kg.1.transpose

/-- The matrix decrypted by FrodoPKE is the encoded message plus the noise matrix. -/
theorem decryptionMatrix_eq {ps : ParameterSet} (ops : Operations ps)
    (seedA : SeedABits) (keySeed encSeed : SeedSEBits ps)
    (message : MessageBits ps) :
    let keys := keygenFromSeeds ops seedA keySeed
    let ciphertext := encryptFromSeed ops keys.1 message encSeed
    ciphertext.c2 - ciphertext.c1 * keys.2.transpose =
      Encode ps.params (message.cast (messageBits_length ps)) +
        decryptionNoise ops keySeed encSeed := by
  dsimp only [keygenFromSeeds, encryptFromSeed, keygenSamples, encryptionSamples,
    decryptionNoise]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  abel

/-- FrodoPKE decrypts an honestly generated ciphertext when the noise matrix is small. -/
theorem decrypt_encryptFromSeed_of_noiseBound
    {ps : ParameterSet} (ops : Operations ps)
    (seedA : SeedABits) (keySeed encSeed : SeedSEBits ps)
    (message : MessageBits ps)
    (hnoise : NoiseBound ps.params
      (decryptionNoise ops keySeed encSeed)) :
    decrypt (keygenFromSeeds ops seedA keySeed).2
      (encryptFromSeed ops
        (keygenFromSeeds ops seedA keySeed).1 message encSeed) =
      message := by
  rw [decrypt, decryptionMatrix_eq]
  rw [Decode_Encode_add ps.params ps.params_wellFormed _ _ hnoise.1 hnoise.2]
  simp

end PKE

namespace KEM

/-- Deterministic FrodoKEM key generation from the three sampled bit strings. -/
def keygenFromCoins {ps : ParameterSet} (ops : Operations ps)
    (fallback : SharedSecretBits ps) (seedSE : SeedSEBits ps)
    (z : Bits lenZ) : PublicKey ps × SecretKey ps :=
  let p := ps.params
  let seedA := ops.shake z.toList lenSeedA
  let pkeKeys := PKE.keygenFromSeeds ops seedA seedSE
  let pk : PublicKey ps :=
    { seedA := pkeKeys.1.seedA
      b := packBits ps p.n nbar (publicKeyBits_mod_eight ps)
        pkeKeys.1.matrixB }
  (pk,
    { fallback := fallback
      publicKey := pk
      secretTranspose := pkeKeys.2
      publicKeyHash := hashPublicKey ops pk })

/-- Deterministic FrodoKEM encapsulation from the sampled message and salt. -/
def encapsFromCoins {ps : ParameterSet} (ops : Operations ps)
    (pk : PublicKey ps) (message : MessageBits ps)
    (salt : SaltBits ps) : Ciphertext ps × SharedSecretBits ps :=
  let p := ps.params
  let derived := deriveSeedAndKey ops (hashPublicKey ops pk) message salt
  let pkePK : PKEPublicKey ps :=
    { seedA := pk.seedA
      matrixB := unpackBits ps p.n nbar
        (publicKeyBits_mod_eight ps) pk.b }
  let encrypted := PKE.encryptFromSeed ops pkePK message derived.1
  let ciphertext : Ciphertext ps :=
    { c1 := packBits ps mbar p.n
        (ciphertext1Bits_mod_eight ps) encrypted.c1
      c2 := packBits ps mbar nbar
        (ciphertext2Bits_mod_eight ps) encrypted.c2
      salt := salt }
  (ciphertext,
    ops.shake
      (ciphertext.c1.toList ++ ciphertext.c2.toList ++
        ciphertext.salt.toList ++ derived.2.toList)
      p.ell)

/-- `keygen` samples the three inputs of `keygenFromCoins` uniformly and runs it. -/
theorem keygen_eq {ps : ParameterSet} (ops : Operations ps) :
    keygen ops =
      (do
        let fallback ← $ᵗ (SharedSecretBits ps)
        let seedSE ← $ᵗ (SeedSEBits ps)
        let z ← $ᵗ (Bits lenZ)
        return keygenFromCoins ops fallback seedSE z) := by
  rfl

/-- `encaps` samples the message and salt uniformly and runs `encapsFromCoins`. -/
theorem encaps_eq {ps : ParameterSet} (ops : Operations ps)
    (pk : PublicKey ps) :
    encaps ops pk =
      (do
        let message ← $ᵗ (MessageBits ps)
        let salt ← $ᵗ (SaltBits ps)
        return encapsFromCoins ops pk message salt) := by
  rfl

/-- Decapsulation agrees with deterministic honest encapsulation when the noise matrix is small. -/
theorem decaps_encapsFromCoins_of_noiseBound
    {ps : ParameterSet} (ops : Operations ps)
    (fallback : SharedSecretBits ps) (keySeed : SeedSEBits ps)
    (z : Bits lenZ) (message : MessageBits ps)
    (salt : SaltBits ps)
    (hnoise : NoiseBound ps.params
      (PKE.decryptionNoise ops keySeed
        (deriveSeedAndKey ops
          (hashPublicKey ops
            (keygenFromCoins ops fallback keySeed z).1)
          message salt).1)) :
    decaps ops (keygenFromCoins ops fallback keySeed z).2
      (encapsFromCoins ops
        (keygenFromCoins ops fallback keySeed z).1 message salt).1 =
      (encapsFromCoins ops
        (keygenFromCoins ops fallback keySeed z).1 message salt).2 := by
  let seedA := ops.shake z.toList lenSeedA
  let pkeKeys := PKE.keygenFromSeeds ops seedA keySeed
  let pk : PublicKey ps :=
    { seedA := pkeKeys.1.seedA
      b := packBits ps ps.params.n nbar (publicKeyBits_mod_eight ps)
        pkeKeys.1.matrixB }
  let sk : SecretKey ps :=
    { fallback := fallback
      publicKey := pk
      secretTranspose := pkeKeys.2
      publicKeyHash := hashPublicKey ops pk }
  let derived := deriveSeedAndKey ops (hashPublicKey ops pk) message salt
  let pkePK : PKEPublicKey ps :=
    { seedA := pk.seedA
      matrixB := unpackBits ps ps.params.n nbar
        (publicKeyBits_mod_eight ps) pk.b }
  let encrypted := PKE.encryptFromSeed ops pkePK message derived.1
  let ciphertext : Ciphertext ps :=
    { c1 := packBits ps mbar ps.params.n
        (ciphertext1Bits_mod_eight ps) encrypted.c1
      c2 := packBits ps mbar nbar
        (ciphertext2Bits_mod_eight ps) encrypted.c2
      salt := salt }
  let shared := ops.shake
    (ciphertext.c1.toList ++ ciphertext.c2.toList ++
      ciphertext.salt.toList ++ derived.2.toList)
    ps.params.ell
  have hkeygen : keygenFromCoins ops fallback keySeed z = (pk, sk) := rfl
  have hencap : encapsFromCoins ops pk message salt = (ciphertext, shared) := rfl
  rw [hkeygen] at hnoise ⊢
  rw [hencap]
  have hpkePK : pkePK = pkeKeys.1 := by
    dsimp only [pkePK, pk]
    rw [unpackBits_packBits]
  have hdecrypt : PKE.decrypt pkeKeys.2 encrypted = message := by
    dsimp only [encrypted]
    rw [hpkePK]
    exact PKE.decrypt_encryptFromSeed_of_noiseBound ops seedA keySeed derived.1 message hnoise
  dsimp only [decaps, ciphertext, sk, shared]
  rw [unpackBits_packBits, unpackBits_packBits]
  change (let recovered := PKE.decrypt pkeKeys.2 encrypted
    let regenerated := deriveSeedAndKey ops (hashPublicKey ops pk) recovered salt
    let reencryption := PKE.encryptFromSeed ops pkePK recovered regenerated.1
    let selected := if encrypted.c1 = reencryption.c1 ∧ encrypted.c2 = reencryption.c2 then
      regenerated.2 else fallback
    ops.shake
      ((packBits ps mbar ps.params.n (ciphertext1Bits_mod_eight ps) encrypted.c1).toList ++
        (packBits ps mbar nbar (ciphertext2Bits_mod_eight ps) encrypted.c2).toList ++
        salt.toList ++ selected.toList)
      ps.params.ell) = shared
  rw [hdecrypt]
  change ops.shake
    ((packBits ps mbar ps.params.n (ciphertext1Bits_mod_eight ps) encrypted.c1).toList ++
      (packBits ps mbar nbar (ciphertext2Bits_mod_eight ps) encrypted.c2).toList ++
      salt.toList ++
      (if encrypted.c1 = encrypted.c1 ∧ encrypted.c2 = encrypted.c2 then
        derived.2 else fallback).toList)
    ps.params.ell = shared
  rw [ite_eq_left ⟨rfl, rfl⟩]

end KEM

end FrodoKEM
