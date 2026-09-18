/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import ToVCVio.LatticeCrypto.FrodoKEM.Encoding
import ToVCVio.LatticeCrypto.FrodoKEM.Packing
import ToVCVio.LatticeCrypto.FrodoKEM.Sampling
import VCVio.CryptoFoundations.AsymmEncAlg.Defs
import VCVio.CryptoFoundations.KeyEncapMech

/-!
# FrodoPKE and FrodoKEM constructions

References are as in `Parameters.lean`. `[LBES26]` draft03 is primary. FrodoPKE key
generation, encryption and decryption follow `[CiC25]` Algorithms 5, 6 and 7, using
the corresponding arithmetic in draft03 Sections 7.1.1, 7.2 and 7.3; draft03 has no
standalone PKE interfaces. KEM key generation, encapsulation and decapsulation follow
draft03 Sections 7.1, 7.2 and 7.3, corresponding to Algorithms 8, 9 and 10.

`Operations` supplies deterministic Gen and SHAKE functions; their types assert no
primitive conformance or security. Sections 6.7 and 9.1 of `[LBES26]` select SHAKE128
for level 640 and SHAKE256 for levels 976 and 1344. GenSHAKE uses SHAKE128 for all
levels (Section 6.7.2). Concrete AES/SHAKE implementations are outside this module.

Ordinary bit strings list each octet least-significant bit first. Raw `Pack` lists
each coefficient most-significant bit first; `packBits` and `unpackBits` reverse each
complete octet to bridge raw packing to ordinary strings representing packed bytes.
Integer samples are explicitly reduced into `ZMod q`. The secret is stored as a
modular transposed matrix; signed 16-bit secret serialization is deferred.

Inputs have fixed typed lengths. Decapsulation compares both reconstructed matrices,
uses the stored public-key hash, and hashes the received ciphertext with the selected
key, including on implicit rejection. This specification makes no constant-time claim.
Ephemeral parameters use empty salt and shorter seeds; `[LBES26]` Section 8 limits
each ephemeral public key to fewer than 256 ciphertexts. Usage accounting is external.
No perfect correctness, primitive conformance or cryptographic security claim is made.
-/

namespace FrodoKEM

open OracleComp

/-- Ordinary bits of the seed for the public matrix. -/
abbrev SeedABits := Bits lenSeedA

/-- Ordinary bits of the seed for error sampling. -/
abbrev SeedSEBits (ps : ParameterSet) := Bits ps.params.lenSeedSE

/-- Ordinary message bits. -/
abbrev MessageBits (ps : ParameterSet) := Bits ps.params.ell

/-- Ordinary shared-secret bits. -/
abbrev SharedSecretBits (ps : ParameterSet) := Bits ps.params.ell

/-- Ordinary bits of a public-key hash. -/
abbrev PublicKeyHashBits (ps : ParameterSet) := Bits ps.params.ell

/-- Ordinary salt bits, empty for ephemeral parameter sets. -/
abbrev SaltBits (ps : ParameterSet) := Bits ps.params.lenSalt

/-- Supplied deterministic operations, without conformance or security assumptions. -/
structure Operations (ps : ParameterSet) where
  /-- Public-matrix generation; the caller supplies the chosen Gen implementation. -/
  gen : SeedABits →
    FrodoMatrix ps.params ps.params.n ps.params.n
  /-- SHAKE at a requested bit length; draft03 selects SHAKE128/256 by parameter level. -/
  shake : List Bool → (outBits : ℕ) → Bits outBits

/-- Ordinary bits of the key-generation domain separator 0x5F. -/
def keygenPrefix : Bits 8 :=
  #v[true, true, true, true, true, false, true, false]

/-- Ordinary bits of the encryption domain separator 0x96. -/
def encryptionPrefix : Bits 8 :=
  #v[false, true, true, false, true, false, false, true]

/-- A message fills all encoded matrix entries. -/
theorem messageBits_length (ps : ParameterSet) :
    ps.params.ell = mbar * nbar * ps.params.B := by
  rw [ps.ell_eq_mul]
  ac_rfl

/-- The packed public matrix consists of complete octets. -/
theorem publicKeyBits_mod_eight (ps : ParameterSet) :
    (ps.params.n * nbar * ps.params.D) % 8 = 0 := by
  simp [nbar, Nat.mul_mod]

/-- The first packed ciphertext matrix consists of complete octets. -/
theorem ciphertext1Bits_mod_eight (ps : ParameterSet) :
    (mbar * ps.params.n * ps.params.D) % 8 = 0 := by
  simp [mbar, Nat.mul_mod]

/-- The second packed ciphertext matrix consists of complete octets. -/
theorem ciphertext2Bits_mod_eight (ps : ParameterSet) :
    (mbar * nbar * ps.params.D) % 8 = 0 := by
  simp [mbar, Nat.mul_mod]

/-- Convert raw `Pack` output into ordinary bits representing draft03 packed bytes. -/
def packBits (ps : ParameterSet) (r c : ℕ)
    (h : (r * c * ps.params.D) % 8 = 0)
    (M : FrodoMatrix ps.params r c) :
    Bits (r * c * ps.params.D) :=
  reverseOctets (Pack ps.params M) h

/-- Read ordinary packed-byte bits through the octet bridge before raw `Unpack`. -/
def unpackBits (ps : ParameterSet) (r c : ℕ)
    (h : (r * c * ps.params.D) % 8 = 0)
    (b : Bits (r * c * ps.params.D)) :
    FrodoMatrix ps.params r c :=
  Unpack ps.params r c (reverseOctets b h)

/-- The public seed and modular matrix used by FrodoPKE. -/
structure PKEPublicKey (ps : ParameterSet) where
  /-- Seed used to regenerate the public matrix A. -/
  seedA : SeedABits
  /-- Modular matrix B = A S + E. -/
  matrixB : FrodoMatrix ps.params ps.params.n nbar

/-- The modular transpose of the PKE secret matrix, before signed serialization. -/
abbrev PKESecretKey (ps : ParameterSet) :=
  FrodoMatrix ps.params nbar ps.params.n

/-- The two modular matrices output by FrodoPKE encryption. -/
structure PKECiphertext (ps : ParameterSet) where
  /-- First encrypted matrix. -/
  c1 : FrodoMatrix ps.params mbar ps.params.n
  /-- Second encrypted matrix, containing the encoded message. -/
  c2 : FrodoMatrix ps.params mbar nbar

/-- The KEM public key with its matrix in ordinary packed-byte bits. -/
structure PublicKey (ps : ParameterSet) where
  /-- Seed used to regenerate A. -/
  seedA : SeedABits
  /-- Ordinary bits of packed B. -/
  b : Bits (ps.params.n * nbar * ps.params.D)

/-- Stored decapsulation data, without a consistency proof for the cached hash. -/
structure SecretKey (ps : ParameterSet) where
  /-- Secret selected when matrix validation fails. -/
  fallback : SharedSecretBits ps
  /-- Public key used in reencryption. -/
  publicKey : PublicKey ps
  /-- Modular transpose of the PKE secret matrix. -/
  secretTranspose : PKESecretKey ps
  /-- Stored hash used directly in seed derivation. -/
  publicKeyHash : PublicKeyHashBits ps

/-- A typed KEM ciphertext, including empty salt in the ephemeral variant. -/
structure Ciphertext (ps : ParameterSet) where
  /-- Ordinary bits of the first packed ciphertext matrix. -/
  c1 : Bits (mbar * ps.params.n * ps.params.D)
  /-- Ordinary bits of the second packed ciphertext matrix. -/
  c2 : Bits (mbar * nbar * ps.params.D)
  /-- Salt included in seed derivation and final hashing. -/
  salt : SaltBits ps

namespace PKE

/-- PKE key generation from direct public and error seeds (paper Algorithm 5). -/
def keygenFromSeeds {ps : ParameterSet} (ops : Operations ps)
    (seedA : SeedABits) (seedSE : SeedSEBits ps) :
    PKEPublicKey ps × PKESecretKey ps :=
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
  ({ seedA := seedA, matrixB := ops.gen seedA * st.transpose + e }, st)

/-- PKE encryption from an explicit error seed (paper Algorithm 6). -/
def encryptFromSeed {ps : ParameterSet} (ops : Operations ps)
    (pk : PKEPublicKey ps) (message : MessageBits ps)
    (seedSE : SeedSEBits ps) : PKECiphertext ps :=
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
  { c1 := sp * ops.gen pk.seedA + ep
    c2 := sp * pk.matrixB + epp +
      Encode p (message.cast (messageBits_length ps)) }

/-- PKE decryption by subtracting the secret product (paper Algorithm 7). -/
def decrypt {ps : ParameterSet} (sk : PKESecretKey ps)
    (c : PKECiphertext ps) : MessageBits ps :=
  (Decode ps.params (c.c2 - c.c1 * sk.transpose)).cast
    (messageBits_length ps).symm

end PKE

/-- Hash the ordinary bits of the public seed followed by the packed public matrix. -/
def hashPublicKey {ps : ParameterSet} (ops : Operations ps)
    (pk : PublicKey ps) : PublicKeyHashBits ps :=
  ops.shake (pk.seedA.toList ++ pk.b.toList) ps.params.ell

/-- Derive the encryption seed followed by the intermediate key from hash/message/salt. -/
def deriveSeedAndKey {ps : ParameterSet} (ops : Operations ps)
    (pkh : PublicKeyHashBits ps) (message : MessageBits ps)
    (salt : SaltBits ps) : SeedSEBits ps × SharedSecretBits ps :=
  splitBits (a := ps.params.lenSeedSE) (b := ps.params.ell)
    (ops.shake (pkh.toList ++ message.toList ++ salt.toList)
      (ps.params.lenSeedSE + ps.params.ell))

/-- KEM key generation from explicit coins (draft03 Section 7.1, paper Algorithm 8). -/
def keygenFromSeeds {ps : ParameterSet} (ops : Operations ps)
    (fallback : SharedSecretBits ps) (seedSE : SeedSEBits ps)
    (z : Bits lenZ) : PublicKey ps × SecretKey ps :=
  let seedA := ops.shake z.toList lenSeedA
  let keys := PKE.keygenFromSeeds ops seedA seedSE
  let pk : PublicKey ps :=
    { seedA := seedA
      b := packBits ps ps.params.n nbar
        (publicKeyBits_mod_eight ps) keys.1.matrixB }
  (pk,
    { fallback := fallback
      publicKey := pk
      secretTranspose := keys.2
      publicKeyHash := hashPublicKey ops pk })

/-- KEM encapsulation from explicit coins (draft03 Section 7.2, paper Algorithm 9). -/
def encapsFromCoins {ps : ParameterSet} (ops : Operations ps)
    (pk : PublicKey ps) (message : MessageBits ps)
    (salt : SaltBits ps) : Ciphertext ps × SharedSecretBits ps :=
  let derived := deriveSeedAndKey ops (hashPublicKey ops pk) message salt
  let pkePK : PKEPublicKey ps :=
    { seedA := pk.seedA
      matrixB := unpackBits ps ps.params.n nbar
        (publicKeyBits_mod_eight ps) pk.b }
  let encrypted := PKE.encryptFromSeed ops pkePK message derived.1
  let c : Ciphertext ps :=
    { c1 := packBits ps mbar ps.params.n
        (ciphertext1Bits_mod_eight ps) encrypted.c1
      c2 := packBits ps mbar nbar
        (ciphertext2Bits_mod_eight ps) encrypted.c2
      salt := salt }
  (c, ops.shake
    (c.c1.toList ++ c.c2.toList ++ c.salt.toList ++ derived.2.toList)
    ps.params.ell)

/-- KEM decapsulation with implicit rejection (draft03 Section 7.3, paper Algorithm 10). -/
def decaps {ps : ParameterSet} (ops : Operations ps)
    (sk : SecretKey ps) (c : Ciphertext ps) : SharedSecretBits ps :=
  let received : PKECiphertext ps :=
    { c1 := unpackBits ps mbar ps.params.n
        (ciphertext1Bits_mod_eight ps) c.c1
      c2 := unpackBits ps mbar nbar
        (ciphertext2Bits_mod_eight ps) c.c2 }
  let message := PKE.decrypt sk.secretTranspose received
  let derived := deriveSeedAndKey ops sk.publicKeyHash message c.salt
  let pkePK : PKEPublicKey ps :=
    { seedA := sk.publicKey.seedA
      matrixB := unpackBits ps ps.params.n nbar
        (publicKeyBits_mod_eight ps) sk.publicKey.b }
  let regenerated := PKE.encryptFromSeed ops pkePK message derived.1
  let selected :=
    if received.c1 = regenerated.c1 ∧ received.c2 = regenerated.c2
    then derived.2
    else sk.fallback
  ops.shake
    (c.c1.toList ++ c.c2.toList ++ c.salt.toList ++ selected.toList)
    ps.params.ell

/-- PKE key generation samples its two seeds independently and uniformly. -/
def PKE.keygen {ps : ParameterSet} (ops : Operations ps) :
    ProbComp (PKEPublicKey ps × PKESecretKey ps) := do
  let seedA ← $ᵗ SeedABits
  let seedSE ← $ᵗ (SeedSEBits ps)
  return PKE.keygenFromSeeds ops seedA seedSE

/-- FrodoPKE packaged with its explicit encryption coins and total decryption. -/
def PKE.asExplicitCoins {ps : ParameterSet} (ops : Operations ps) :
    AsymmEncAlg.ExplicitCoins ProbComp
      (MessageBits ps) (PKEPublicKey ps) (PKESecretKey ps)
      (SeedSEBits ps) (PKECiphertext ps) where
  keygen := PKE.keygen ops
  encrypt := PKE.encryptFromSeed ops
  decrypt := fun sk c => some (PKE.decrypt sk c)

/-- FrodoPKE using the installed probability runtime to sample encryption coins. -/
noncomputable def PKE.asAsymmEncAlg {ps : ParameterSet}
    (ops : Operations ps) :
    AsymmEncAlg ProbComp (MessageBits ps)
      (PKEPublicKey ps) (PKESecretKey ps) (PKECiphertext ps) :=
  (PKE.asExplicitCoins ops).toAsymmEncAlg ProbCompRuntime.probComp

/-- KEM key generation with independent uniform fallback, error seed and pre-seed z. -/
def keygen {ps : ParameterSet} (ops : Operations ps) :
    ProbComp (PublicKey ps × SecretKey ps) := do
  let fallback ← $ᵗ (SharedSecretBits ps)
  let seedSE ← $ᵗ (SeedSEBits ps)
  let z ← $ᵗ (Bits lenZ)
  return keygenFromSeeds ops fallback seedSE z

/-- KEM encapsulation with uniform message and salt, including zero-length salt. -/
def encaps {ps : ParameterSet} (ops : Operations ps)
    (pk : PublicKey ps) :
    ProbComp (Ciphertext ps × SharedSecretBits ps) := do
  let message ← $ᵗ (MessageBits ps)
  let salt ← $ᵗ (SaltBits ps)
  return encapsFromCoins ops pk message salt

/-- Package the FrodoKEM algorithms in the installed KEM interface.
Implicit rejection returns a shared secret, so decapsulation always returns `some`.

For ephemeral parameter sets, draft03 Section 8 requires fewer than 256 ciphertexts
per public key. This stateless adapter does not enforce that bound; the surrounding
protocol must ensure it, and security results must account for it.

This adapter alone asserts no correctness or security guarantee. -/
def asKEMScheme {ps : ParameterSet} (ops : Operations ps) :
    KEMScheme ProbComp (SharedSecretBits ps)
      (PublicKey ps) (SecretKey ps) (Ciphertext ps) where
  keygen := keygen ops
  encaps := encaps ops
  decaps := fun sk c => return some (decaps ops sk c)

end FrodoKEM
