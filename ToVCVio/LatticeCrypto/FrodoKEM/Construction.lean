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

Full citations are listed in the References section below; `[LBES26]` is the primary reference.
FrodoPKE key generation, encryption and decryption follow Algorithms 5–7 of `[CiC25]`,
using the corresponding arithmetic in Sections 7.1.1, 7.2 and 7.3 of `[LBES26]`,
which does not define standalone PKE interfaces. FrodoKEM key generation,
encapsulation and decapsulation follow Sections 7.1–7.3 of `[LBES26]`,
corresponding to Algorithms 8–10 of `[CiC25]`.

## Parameters and representation

`Parameters.lean` defines the supported parameter sets. Their numerical values are
recorded in `ParameterSet.params` and summarized below; relations between these
values are stated as theorems in that file.

`Operations ps` supplies deterministic Gen and SHAKE functions for a parameter set
`ps`. Given `ops : Operations ps`, the descriptions below use the following notation:

| Notation                  | Meaning                                                      |
|---------------------------|--------------------------------------------------------------|
| `ps`                      | The chosen parameter set, such as FrodoKEM-640               |
| `n = ps.params.n`         | Large matrix dimension: 640, 976, or 1344                    |
| `q = ps.params.q`         | Modulus for matrix arithmetic                                |
| `D = ps.params.D`         | Exponent of the modulus: `q = 2 ^ D`                         |
| `B = ps.params.B`         | Bits encoded in each matrix entry by `Frodo.Encode`          |
| `ℓ = ps.params.ell`       | Message and shared-secret length: 128, 192, or 256 bits      |
| `lenSeedSE`               | Bit length of the seed used for error sampling               |
| `lenSalt`                 | Bit length of the salt; zero for the ephemeral variant       |
| `mbar = nbar = 8`         | Small matrix dimensions; encoded messages are 8 × 8 matrices |
| `A = ops.gen seedA`       | Public n × n matrix generated from its seed                  |
| `H(x, L) = ops.shake x L` | SHAKE applied to input x, requesting L output bits           |

`ℓ` also determines the lengths of the intermediate key, public-key hash, and
fallback secret. The identity `ℓ = B * mbar * nbar` ensures that the message fills
the encoding matrix.

The constants `mbar = nbar = 8`, `lenSeedA = lenZ = 128` and `lenChi = 16` are
shared by every parameter set; the per-set entries `Params` carries are:

| parameter set   |  D |     q |    n | B |   ℓ | lenSeedSE | lenSalt |
| --------------- | --:| -----:| ----:| -:| ---:| ---------:| -------:|
| FrodoKEM-640    | 15 | 32768 |  640 | 2 | 128 |       256 |     256 |
| FrodoKEM-976    | 16 | 65536 |  976 | 3 | 192 |       384 |     384 |
| FrodoKEM-1344   | 16 | 65536 | 1344 | 4 | 256 |       512 |     512 |
| eFrodoKEM-640   | 15 | 32768 |  640 | 2 | 128 |       128 |       0 |
| eFrodoKEM-976   | 16 | 65536 |  976 | 3 | 192 |       192 |       0 |
| eFrodoKEM-1344  | 16 | 65536 | 1344 | 4 | 256 |       256 |       0 |

The `χ` and SHAKE rows in Table 1 of `[CiC25]` are not fields of `Params`,
nor is the `-AES` or `-SHAKE` choice of generator for `A` that doubles these
six sets to twelve.

The intended SHAKE is SHAKE128
at level 640 and SHAKE256 at levels 976/1344; GenSHAKE always uses SHAKE128
(Sections 6.7 and 9.1 of `[LBES26]`).

Matrix arithmetic is over `ZMod q`, with integer samples reduced modulo `q`.
The symbol `||` denotes concatenation of ordinary bit
strings, whose octets are least-significant-bit first. Raw `Pack` emits coefficient
bits most-significant first; `packBits` and `unpackBits` reverse each octet to bridge
these conventions. The secret matrix is stored transposed over `ZMod q`.

## Building blocks

* **Message encoding** (`Encoding.lean`): `Encode` divides the message into `B`-bit
  chunks and maps them to evenly spaced values modulo `q` in an 8 × 8 matrix.
  `Decode` rounds back to these values, recovering the message when the added
  error is sufficiently small.
* **Matrix packing** (`Packing.lean`): `Pack` writes each matrix entry as `D` bits,
  row by row; `Unpack` reads the entries back. Packing preserves the matrix entries,
  whereas message encoding spaces out the possible values to tolerate errors.
  The `packBits` and `unpackBits` wrappers below adapt the packed bit order to the
  octet convention described above.
* **Error sampling** (`Sampling.lean`): `Sample` converts 16 supplied bits into a
  small signed integer using the parameter set's error table. `SampleMatrix`
  applies it to consecutive blocks of bits to fill a matrix row by row. These
  functions consume bits; the construction supplies them from SHAKE output.

## FrodoPKE

The maps in namespace `PKE` take any required randomness as explicit inputs:

* `PKE.keygenFromSeeds ops : SeedABits → SeedSEBits ps →
  PKEPublicKey ps × PKESecretKey ps`,
  `(seedA, seedSE) ↦ ((seedA, A * S + E), Sᵀ)`.
  Split `H(0x5F || seedSE, 16 * (nbar * n + n * nbar))` into consecutive
  blocks for `SampleMatrix ps.errorTable nbar n` and
  `SampleMatrix ps.errorTable n nbar`, obtaining `Sᵀ` and `E` respectively.
  The first sample is the transpose itself; `S = (Sᵀ)ᵀ`.
* `PKE.encryptFromSeed ops : PKEPublicKey ps → MessageBits ps → SeedSEBits ps →
  PKECiphertext ps`,
  `((seedA, B), μ, seedSE) ↦ (S′ * A + E′, S′ * B + E″ + Encode(μ))`.
  Split `H(0x96 || seedSE, 16 * (mbar * n + mbar * n + mbar * nbar))`
  into consecutive sampling blocks for `S′`, `E′`, and `E″`, of shapes
  `mbar × n`, `mbar × n`, and `mbar × nbar`. Each uses `ps.errorTable`.
* `PKE.decrypt : PKESecretKey ps → PKECiphertext ps → MessageBits ps`,
  `(Sᵀ, (C₁, C₂)) ↦ Decode(C₂ - C₁ * S)`.

These are Algorithms 5–7 of `[CiC25]`. The message length identity
`ℓ = mbar * nbar * ps.params.B` supplies the casts for `Encode` and `Decode`.

## FrodoKEM

The following shorthands are used in the algorithm descriptions below:
`P(M) = packBits ps r c h M` and `U(b) = unpackBits ps r c h b`.
In each use, the matrix dimensions `r`, `c` and complete-octet proof `h` are
determined by the component being packed or unpacked.

The public key is `(seedA, b)`, the secret key is `(s, pk, Sᵀ, pkh)`, and the
ciphertext is `(c₁, c₂, salt)`.

The two derivation maps in namespace `KEM` are:

* `KEM.hashPublicKey ops : PublicKey ps → PublicKeyHashBits ps`,
  `(seedA, b) ↦ H(seedA || b, ℓ)`;
* `KEM.deriveSeedAndKey ops : PublicKeyHashBits ps → MessageBits ps → SaltBits ps →
  SeedSEBits ps × SharedSecretBits ps`,
  `(pkh, μ, salt) ↦ (seedSE, k)`, splitting
  `H(pkh || μ || salt, ps.params.lenSeedSE + ℓ)` after `ps.params.lenSeedSE` bits.

The construction maps are:

* `KEM.keygenFromSeeds ops : SharedSecretBits ps → SeedSEBits ps → Bits lenZ →
  PublicKey ps × SecretKey ps`.
  For coins `(s, seedSE, z)`, set `seedA = H(z, lenSeedA)` and obtain
  `((seedA, B), Sᵀ)` from `PKE.keygenFromSeeds ops seedA seedSE`.
  Return `pk = (seedA, P(B))` and `sk = (s, pk, Sᵀ, KEM.hashPublicKey ops pk)`.
* `KEM.encapsFromCoins ops : PublicKey ps → MessageBits ps → SaltBits ps →
  Ciphertext ps × SharedSecretBits ps`.
  For `pk = (seedA, b)` and coins `(μ, salt)`, derive `(seedSE, k)` from
  `(KEM.hashPublicKey ops pk, μ, salt)`. Encrypt `μ` under `(seedA, U(b))`
  with `seedSE`, obtaining `(B′, C)`. Set `c = (P(B′), P(C), salt)` and
  return `(c, H(c₁ || c₂ || salt || k, ℓ))`.
* `KEM.decaps ops : SecretKey ps → Ciphertext ps → SharedSecretBits ps`.
  For `sk = (s, (seedA, b), Sᵀ, pkh)` and `c = (c₁, c₂, salt)`, recover
  `μ′ = PKE.decrypt Sᵀ (U(c₁), U(c₂))`. Derive `(seedSE′, k′)` from the
  stored `(pkh, μ′, salt)` and reencrypt under `(seedA, U(b))`, obtaining
  `(B″, C′)`. Select `kHat = k′` if both `U(c₁) = B″` and `U(c₂) = C′`,
  and `kHat = s` otherwise. Return `H(c₁ || c₂ || salt || kHat, ℓ)`.

These follow Algorithms 8–10 of `[CiC25]` and Sections 7.1.1, 7.2 and 7.3 of `[LBES26]`.

## Randomness sampling and PKE/KEM interfaces

`PKE.keygen` samples `seedA` and `seedSE` independently and uniformly;
`PKE.asExplicitCoins` exposes the encryption seed, and `PKE.asAsymmEncAlg`
samples it through the installed probability runtime. `KEM.keygen` samples
`s`, `seedSE` and `z` independently and uniformly; `KEM.encaps` samples `μ`
and `salt` independently and uniformly. `KEM.asKEMScheme` packages these maps.

## Scope and limitations of this formalization

This module defines the PKE and KEM algorithms using caller-supplied Gen and SHAKE
functions. Input lengths and matrix dimensions are specified by the Lean types.
Concrete primitive implementations, byte parsing,
signed secret-key serialization, constant-time execution, decryption-failure bounds
and cryptographic security proofs are outside the present formalization.
The types of the supplied functions do not ensure that they implement the specified
Gen and SHAKE algorithms or satisfy the assumptions needed for security proofs.

Section 8 of `[LBES26]` requires fewer than 256 ciphertexts per ephemeral public key.
This module does not enforce that usage restriction.

## References

The FrodoKEM modules use the following references:

* `[CiC25]`, Glabush, Longa, Naehrig, Peikert, Stebila and Virdia, *FrodoKEM: A
  CCA-Secure Learning With Errors Key Encapsulation Mechanism*, IACR
  Communications in Cryptology 2:3, <https://cic.iacr.org/p/2/3/25>;
* `[LBES26]`, Longa, Bos, Ehlen and Stebila, *FrodoKEM: key encapsulation from
  learning with errors*, draft-longa-cfrg-frodokem-03, 22 June 2026,
  <https://datatracker.ietf.org/doc/html/draft-longa-cfrg-frodokem-03>.

The version and date are part of the second citation because an
Internet-Draft expires, this one on 24 December 2026.
-/

namespace FrodoKEM

open OracleComp

/-- Bit string of seedA used to generate the public matrix A. -/
abbrev SeedABits := Bits lenSeedA

/-- Bit string of seedSE used to sample the secret and error matrices. -/
abbrev SeedSEBits (ps : ParameterSet) := Bits ps.params.lenSeedSE

/-- Message bit string of length ℓ for the chosen parameter set. -/
abbrev MessageBits (ps : ParameterSet) := Bits ps.params.ell

/-- Shared-secret bit string of length ℓ for the chosen parameter set. -/
abbrev SharedSecretBits (ps : ParameterSet) := Bits ps.params.ell

/-- Public-key hash bit string of length ℓ for the chosen parameter set. -/
abbrev PublicKeyHashBits (ps : ParameterSet) := Bits ps.params.ell

/-- Salt bit string of length lenSalt for the chosen parameter set; empty for ephemeral sets. -/
abbrev SaltBits (ps : ParameterSet) := Bits ps.params.lenSalt

/-- Gen and SHAKE functions that must be supplied when instantiating the PKE and KEM algorithms
for the chosen parameter set. -/
-- ANCHOR: frodoKEM_operations
structure Operations (ps : ParameterSet) where
  /-- Gen function mapping seedA to the n × n public matrix A. -/
  gen : SeedABits →
    FrodoMatrix ps.params ps.params.n ps.params.n
  /-- SHAKE function with variable output length: the `H(x, L)` of the module header. -/
  shake : List Bool → (outBits : ℕ) → Bits outBits
-- ANCHOR_END: frodoKEM_operations

/-- Bit string of the key-generation domain separator 0x5F, least-significant bit first. -/
def keygenPrefix : Bits 8 :=
  #v[true, true, true, true, true, false, true, false]

/-- Check that the key-generation prefix represents 0x5F. -/
example :
    (Nat.ofBits fun i : Fin 8 => keygenPrefix[i]) = 95 := by decide

/-- Bit string of the encryption domain separator 0x96, least-significant bit first. -/
def encryptionPrefix : Bits 8 :=
  #v[false, true, true, false, true, false, false, true]

/-- Check that the encryption prefix represents 0x96. -/
example :
    (Nat.ofBits fun i : Fin 8 => encryptionPrefix[i]) = 150 := by decide

/-- A message exactly fills the `mbar × nbar` matrix, with `B` bits per entry.
This equality converts between the message length and the bit length expected
by `Encode` and `Decode`. -/
theorem messageBits_length (ps : ParameterSet) :
    ps.params.ell = mbar * nbar * ps.params.B := by
  rw [ps.ell_eq_mul]
  ac_rfl

/-- The packed matrix B of the public key has n × nbar × D bits, a multiple of 8. -/
theorem publicKeyBits_mod_eight (ps : ParameterSet) :
    (ps.params.n * nbar * ps.params.D) % 8 = 0 := by
  simp [nbar, Nat.mul_mod]

/-- Ciphertext component c₁ has mbar × n × D bits, a multiple of 8. -/
theorem ciphertext1Bits_mod_eight (ps : ParameterSet) :
    (mbar * ps.params.n * ps.params.D) % 8 = 0 := by
  simp [mbar, Nat.mul_mod]

/-- Ciphertext component c₂ has mbar × nbar × D bits, a multiple of 8. -/
theorem ciphertext2Bits_mod_eight (ps : ParameterSet) :
    (mbar * nbar * ps.params.D) % 8 = 0 := by
  simp [mbar, Nat.mul_mod]

/-- Pack matrix M into a bit string by applying `Pack` and reversing the bits within each
octet, so each packed byte is represented least-significant bit first as in `[LBES26]`. -/
def packBits (ps : ParameterSet) (r c : ℕ)
    (h : (r * c * ps.params.D) % 8 = 0)
    (M : FrodoMatrix ps.params r c) :
    Bits (r * c * ps.params.D) :=
  reverseOctets (Pack ps.params M) h

/-- Recover a matrix from a bit string whose bytes are represented least-significant bit first,
by reversing the bits within each octet and applying `Unpack`. -/
def unpackBits (ps : ParameterSet) (r c : ℕ)
    (h : (r * c * ps.params.D) % 8 = 0)
    (b : Bits (r * c * ps.params.D)) :
    FrodoMatrix ps.params r c :=
  Unpack ps.params r c (reverseOctets b h)

/-- For FrodoKEM-640, each entry uses 15 bits, so byte and entry boundaries do not align.
With input bytes `0x00, 0x03` followed by zeros, the two consecutive `1` bits in
`0x03` (binary `00000011`) become the least significant bit of entry `(0, 0)` and
the most significant bit of entry `(0, 1)`, giving `1` and `2 ^ 14 = 16384`;
all other entries are zero. -/
example :
    unpackBits ParameterSet.FrodoKEM640 mbar nbar
      (ciphertext2Bits_mod_eight ParameterSet.FrodoKEM640)
      (Vector.ofFn fun i => decide (i.val = 8 ∨ i.val = 9)) =
    Matrix.of (fun i j =>
      if i.val = 0 ∧ j.val = 0 then
        (1 : ZMod ParameterSet.FrodoKEM640.params.q)
      else if i.val = 0 ∧ j.val = 1 then 16384
      else 0) := by
  ext i j
  simp only [unpackBits, Unpack, bitsToMatrixWith, Matrix.of_apply, bitsToEntry,
    reverseOctets, Vector.getElem_ofFn]
  revert i j
  decide +kernel

/-- For FrodoKEM-976, each 16-bit entry occupies exactly two bytes.
With input bytes `0x80, 0x00` followed by zeros, the most significant bit of the first byte
becomes the most significant bit of entry `(0, 0)`, giving `2 ^ 15 = 32768`;
all other entries are zero. -/
example :
    unpackBits ParameterSet.FrodoKEM976 mbar nbar
      (ciphertext2Bits_mod_eight ParameterSet.FrodoKEM976)
      (Vector.ofFn fun i => decide (i.val = 7)) =
    Matrix.of (fun i j =>
      if i.val = 0 ∧ j.val = 0 then
        (32768 : ZMod ParameterSet.FrodoKEM976.params.q)
      else 0) := by
  ext i j
  simp only [unpackBits, Unpack, bitsToMatrixWith, Matrix.of_apply, bitsToEntry,
    reverseOctets, Vector.getElem_ofFn]
  revert i j
  decide +kernel

/-- FrodoPKE public key (seedA, B). -/
structure PKEPublicKey (ps : ParameterSet) where
  /-- Seed used to regenerate the public matrix A. -/
  seedA : SeedABits
  /-- Modular matrix B = A S + E. -/
  matrixB : FrodoMatrix ps.params ps.params.n nbar

/-- FrodoPKE secret key Sᵀ, an nbar × n matrix over ZMod q. -/
abbrev PKESecretKey (ps : ParameterSet) :=
  FrodoMatrix ps.params nbar ps.params.n

/-- FrodoPKE ciphertext (C₁, C₂). -/
structure PKECiphertext (ps : ParameterSet) where
  /-- Matrix C₁ = S′ * A + E′. -/
  c1 : FrodoMatrix ps.params mbar ps.params.n
  /-- Matrix C₂ = S′ * B + E″ + Encode(μ). -/
  c2 : FrodoMatrix ps.params mbar nbar

/-- FrodoKEM public key (seedA, b). -/
-- ANCHOR: frodoKEM_publicKey
structure PublicKey (ps : ParameterSet) where
  /-- Seed used to generate the public matrix A. -/
  seedA : SeedABits
  /-- Packed matrix B, with each byte represented least-significant bit first. -/
  b : Bits (ps.params.n * nbar * ps.params.D)
-- ANCHOR_END: frodoKEM_publicKey

/-- FrodoKEM secret key (s, pk, Sᵀ, pkh). -/
-- ANCHOR: frodoKEM_secretKey
structure SecretKey (ps : ParameterSet) where
  /-- Fallback value s used in shared-secret derivation when ciphertext validation fails. -/
  fallback : SharedSecretBits ps
  /-- Public key pk used for reencryption during decapsulation. -/
  publicKey : PublicKey ps
  /-- PKE secret matrix Sᵀ. -/
  secretTranspose : PKESecretKey ps
  /-- Stored public-key hash pkh used to derive the reencryption seed and intermediate key. -/
  publicKeyHash : PublicKeyHashBits ps
-- ANCHOR_END: frodoKEM_secretKey

/-- FrodoKEM ciphertext (c₁, c₂, salt). -/
-- ANCHOR: frodoKEM_ciphertext
structure Ciphertext (ps : ParameterSet) where
  /-- Ciphertext component c₁: packed matrix B′, with each byte least-significant bit first. -/
  c1 : Bits (mbar * ps.params.n * ps.params.D)
  /-- Ciphertext component c₂: packed matrix C, with each byte least-significant bit first. -/
  c2 : Bits (mbar * nbar * ps.params.D)
  /-- Salt used in seed derivation and shared-secret hashing; empty for ephemeral sets. -/
  salt : SaltBits ps
-- ANCHOR_END: frodoKEM_ciphertext

namespace PKE

/-- FrodoPKE key generation from supplied seeds seedA and seedSE.
Returns the public key (seedA, B) and secret key Sᵀ, where B = A * S + E
(Algorithm 5 of `[CiC25]`). -/
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

/-- FrodoPKE encryption of message μ under public key (seedA, B), using supplied seedSE.
Returns ciphertext (C₁, C₂), where C₁ = S′ * A + E′ and
C₂ = S′ * B + E″ + Encode(μ) (Algorithm 6 of `[CiC25]`). -/
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

/-- FrodoPKE decryption of ciphertext (C₁, C₂) using secret key Sᵀ.
Returns Decode(C₂ - C₁ * S) (Algorithm 7 of `[CiC25]`). -/
def decrypt {ps : ParameterSet} (sk : PKESecretKey ps)
    (c : PKECiphertext ps) : MessageBits ps :=
  (Decode ps.params (c.c2 - c.c1 * sk.transpose)).cast
    (messageBits_length ps).symm

/-- FrodoPKE key generation: samples seedA and seedSE independently and uniformly,
then returns the key pair produced by `PKE.keygenFromSeeds`. -/
def keygen {ps : ParameterSet} (ops : Operations ps) :
    ProbComp (PKEPublicKey ps × PKESecretKey ps) := do
  let seedA ← $ᵗ SeedABits
  let seedSE ← $ᵗ (SeedSEBits ps)
  return keygenFromSeeds ops seedA seedSE

/-- FrodoPKE as an `AsymmEncAlg.ExplicitCoins` instance.
Key generation samples its seeds; encryption takes seedSE as an explicit input.
Decryption always produces a bit string, so it is returned as `some`. -/
def asExplicitCoins {ps : ParameterSet} (ops : Operations ps) :
    AsymmEncAlg.ExplicitCoins ProbComp
      (MessageBits ps) (PKEPublicKey ps) (PKESecretKey ps)
      (SeedSEBits ps) (PKECiphertext ps) where
  keygen := keygen ops
  encrypt := encryptFromSeed ops
  decrypt := fun sk c => some (decrypt sk c)

/-- FrodoPKE as an `AsymmEncAlg` instance.
Encryption samples seedSE uniformly instead of taking it as an explicit input. -/
noncomputable def asAsymmEncAlg {ps : ParameterSet}
    (ops : Operations ps) :
    AsymmEncAlg ProbComp (MessageBits ps)
      (PKEPublicKey ps) (PKESecretKey ps) (PKECiphertext ps) :=
  (asExplicitCoins ops).toAsymmEncAlg ProbCompRuntime.probComp

end PKE

namespace KEM

/-- Compute the public-key hash pkh = SHAKE(seedA || b, ℓ),
where b is the packed public matrix B. -/
def hashPublicKey {ps : ParameterSet} (ops : Operations ps)
    (pk : PublicKey ps) : PublicKeyHashBits ps :=
  ops.shake (pk.seedA.toList ++ pk.b.toList) ps.params.ell

/-- Derive seedSE and intermediate key k from SHAKE(pkh || μ || salt, lenSeedSE + ℓ).
The first lenSeedSE bits form seedSE; the remaining ℓ bits form k. -/
def deriveSeedAndKey {ps : ParameterSet} (ops : Operations ps)
    (pkh : PublicKeyHashBits ps) (message : MessageBits ps)
    (salt : SaltBits ps) : SeedSEBits ps × SharedSecretBits ps :=
  splitBits (a := ps.params.lenSeedSE) (b := ps.params.ell)
    (ops.shake (pkh.toList ++ message.toList ++ salt.toList)
      (ps.params.lenSeedSE + ps.params.ell))

/-- Generate a FrodoKEM key pair from supplied fallback value s and seeds seedSE and z
(Section 7.1.1 of `[LBES26]`, Algorithm 8 of `[CiC25]`). -/
-- ANCHOR: frodoKEM_keyGeneration
-- ANCHOR: frodoKEM_keygenFromSeeds
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
-- ANCHOR_END: frodoKEM_keygenFromSeeds

/-- FrodoKEM key generation: samples fallback value s and seeds seedSE and z
independently and uniformly, then returns the key pair produced by `KEM.keygenFromSeeds`. -/
-- ANCHOR: frodoKEM_keygen
def keygen {ps : ParameterSet} (ops : Operations ps) :
    ProbComp (PublicKey ps × SecretKey ps) := do
  let fallback ← $ᵗ (SharedSecretBits ps)
  let seedSE ← $ᵗ (SeedSEBits ps)
  let z ← $ᵗ (Bits lenZ)
  return keygenFromSeeds ops fallback seedSE z
-- ANCHOR_END: frodoKEM_keygen
-- ANCHOR_END: frodoKEM_keyGeneration

/-- Generate a FrodoKEM ciphertext and shared secret under public key pk,
using supplied message μ and salt
(Section 7.2 of `[LBES26]`, Algorithm 9 of `[CiC25]`). -/
-- ANCHOR: frodoKEM_encapsulation
-- ANCHOR: frodoKEM_encapsFromCoins
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
-- ANCHOR_END: frodoKEM_encapsFromCoins

/-- FrodoKEM encapsulation: samples message μ and salt independently and uniformly,
then returns the ciphertext and shared secret produced by `KEM.encapsFromCoins`.
The salt is empty for ephemeral parameter sets. -/
-- ANCHOR: frodoKEM_encaps
def encaps {ps : ParameterSet} (ops : Operations ps)
    (pk : PublicKey ps) :
    ProbComp (Ciphertext ps × SharedSecretBits ps) := do
  let message ← $ᵗ (MessageBits ps)
  let salt ← $ᵗ (SaltBits ps)
  return encapsFromCoins ops pk message salt
-- ANCHOR_END: frodoKEM_encaps
-- ANCHOR_END: frodoKEM_encapsulation

/-- FrodoKEM decapsulation using secret key sk, with implicit rejection:
if ciphertext validation fails, derive the shared secret using fallback value s
(Section 7.3 of `[LBES26]`, Algorithm 10 of `[CiC25]`). -/
-- ANCHOR: frodoKEM_decaps
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
-- ANCHOR_END: frodoKEM_decaps

/-- Package the FrodoKEM algorithms as a VCVio `KEMScheme`.
Implicit rejection returns a shared secret, so decapsulation always returns `some`.

For ephemeral parameter sets, Section 8 of `[LBES26]` requires fewer than 256 ciphertexts
per public key. This adapter does not check that usage restriction.

This adapter alone asserts no correctness or security guarantee. -/
-- ANCHOR: frodoKEM_scheme
def asKEMScheme {ps : ParameterSet} (ops : Operations ps) :
    KEMScheme ProbComp (SharedSecretBits ps)
      (PublicKey ps) (SecretKey ps) (Ciphertext ps) where
  keygen := keygen ops
  encaps := encaps ops
  decaps := fun sk c => return some (decaps ops sk c)
-- ANCHOR_END: frodoKEM_scheme

end KEM

end FrodoKEM
