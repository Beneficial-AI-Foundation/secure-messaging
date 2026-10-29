/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import ToVCVio.Probability.FiniteXOF
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.Ideal
import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.FailureProbability

/-! # Finite random-oracle model and deterministic adequacy for FrodoKEM
The generator is fixed independently of the sampled raw-input table.
-/
namespace FrodoKEM.ROM
open OracleComp LatticeCrypto

/-- Deterministic public-matrix generator, fixed independently of the sampled oracle table. -/
abbrev Generator (ps : ParameterSet) :=
  SeedABits → FrodoMatrix ps.params ps.params.n ps.params.n

/-- Roles of SHAKE calls used to classify raw inputs; roles are not oracle-table keys. -/
inductive QueryRole where
  /-- Expand key-generation coins into the public matrix seed. -/
  | seedA
  /-- Expand the key-generation sampling seed into secret and error bits. -/
  | keygenNoise
  /-- Hash the encoded public key. -/
  | publicKeyHash
  /-- Derive the encryption sampling seed and intermediate shared key. -/
  | seedAndKey
  /-- Expand the encryption sampling seed into three error streams. -/
  | encryptionNoise
  /-- Hash the ciphertext together with the selected intermediate or fallback key. -/
  | sharedSecret
deriving DecidableEq

/-- Raw input bit length of each SHAKE-call role. -/
def inputLength (ps : ParameterSet) : QueryRole → ℕ
  | .seedA => lenZ
  | .keygenNoise => 8 + ps.params.lenSeedSE
  | .publicKeyHash => lenSeedA + ps.params.n * nbar * ps.params.D
  | .seedAndKey => ps.params.ell + ps.params.ell + ps.params.lenSalt
  | .encryptionNoise => 8 + ps.params.lenSeedSE
  | .sharedSecret =>
      mbar * ps.params.n * ps.params.D +
        mbar * nbar * ps.params.D +
        ps.params.lenSalt + ps.params.ell

/-- Finite set of raw input lengths queried by the honest KEM algorithms. -/
def inputLengths (ps : ParameterSet) : Finset ℕ :=
  {inputLength ps .seedA,
   inputLength ps .keygenNoise,
   inputLength ps .publicKeyHash,
   inputLength ps .seedAndKey,
   inputLength ps .encryptionNoise,
   inputLength ps .sharedSecret}

/-- Common table-response length, equal to the longest error-expansion stream. -/
def outputBits (ps : ParameterSet) : ℕ :=
  mbar * ps.params.n * lenChi +
    (mbar * ps.params.n * lenChi + mbar * nbar * lenChi)

/-- Requested output prefix length for each SHAKE-call role. -/
def outputLength (ps : ParameterSet) : QueryRole → ℕ
  | .seedA => lenSeedA
  | .keygenNoise =>
      nbar * ps.params.n * lenChi + ps.params.n * nbar * lenChi
  | .publicKeyHash => ps.params.ell
  | .seedAndKey => ps.params.lenSeedSE + ps.params.ell
  | .encryptionNoise => outputBits ps
  | .sharedSecret => ps.params.ell

/-- Role-specific raw-input domain, determined by its length and applicable noise prefix. -/
def InDomain (ps : ParameterSet) (role : QueryRole)
    (x : List Bool) : Prop :=
  x.length = inputLength ps role ∧
    match role with
    | .keygenNoise => x.take 8 = keygenPrefix.toList
    | .encryptionNoise => x.take 8 = encryptionPrefix.toList
    | _ => True

theorem domain_disjoint (ps : ParameterSet)
    {r s : QueryRole} (hrs : r ≠ s) (x : List Bool) :
    ¬ (InDomain ps r x ∧ InDomain ps s x) := by
  cases ps <;> cases r <;> cases s <;>
    simp_all [InDomain, inputLength, keygenPrefix, encryptionPrefix,
      ParameterSet.params, lenZ, lenSeedA, nbar, mbar]

theorem query_bounds (ps : ParameterSet) (role : QueryRole) :
    inputLength ps role ∈ inputLengths ps ∧
      outputLength ps role ≤ outputBits ps := by
  cases ps <;> cases role <;> decide

/-- One raw-input oracle table with a common long response at every covered input. -/
abbrev Table (ps : ParameterSet) :=
  ToVCVio.FiniteXOF.Table (inputLengths ps) (outputBits ps)

/-- Instantiate the deterministic operations with a fixed generator and finite oracle table. -/
def operations (ps : ParameterSet) (gen : Generator ps)
    (H : Table ps) : Operations ps :=
  { gen := gen
    shake := ToVCVio.FiniteXOF.answer H }

/-- Split key-generation and encryption bit streams into the five sampled error matrices. -/
def samplesFromStreams (ps : ParameterSet)
    (kg : Bits (outputLength ps .keygenNoise))
    (enc : Bits (outputBits ps)) : Ideal.NoiseSamples ps :=
  let kgParts := splitBits
    (a := nbar * ps.params.n * lenChi)
    (b := ps.params.n * nbar * lenChi) kg
  let encFirst := splitBits
    (a := mbar * ps.params.n * lenChi)
    (b := mbar * ps.params.n * lenChi + mbar * nbar * lenChi) enc
  let encRest := splitBits
    (a := mbar * ps.params.n * lenChi)
    (b := mbar * nbar * lenChi) encFirst.2
  {
    st := SampleMatrix ps.errorTable nbar ps.params.n kgParts.1
    e := SampleMatrix ps.errorTable ps.params.n nbar kgParts.2
    sp := SampleMatrix ps.errorTable mbar ps.params.n encFirst.1
    ep := SampleMatrix ps.errorTable mbar ps.params.n encRest.1
    epp := SampleMatrix ps.errorTable mbar nbar encRest.2
  }

/-- Error matrices used by honest key generation and encapsulation for fixed coins and table. -/
def samplesFromCoins (ps : ParameterSet) (gen : Generator ps)
    (H : Table ps) (fallback : SharedSecretBits ps)
    (keySeed : SeedSEBits ps) (z : Bits lenZ)
    (message : MessageBits ps) (salt : SaltBits ps) :
    Ideal.NoiseSamples ps :=
  let ops := operations ps gen H
  let pk := (KEM.keygenFromCoins ops fallback keySeed z).1
  let encSeed :=
    (KEM.deriveSeedAndKey ops (KEM.hashPublicKey ops pk) message salt).1
  samplesFromStreams ps
    (ops.shake (keygenPrefix.toList ++ keySeed.toList)
      (outputLength ps .keygenNoise))
    (ops.shake (encryptionPrefix.toList ++ encSeed.toList)
      (outputBits ps))

theorem samplesFromCoins_residual_eq
    (ps : ParameterSet) (gen : Generator ps) (H : Table ps)
    (fallback : SharedSecretBits ps) (keySeed : SeedSEBits ps)
    (z : Bits lenZ) (message : MessageBits ps) (salt : SaltBits ps) :
    (Ideal.residual
      (samplesFromCoins ps gen H fallback keySeed z message salt)).map
        (fun a : ℤ => (a : ZMod ps.params.q)) =
      PKE.decryptionNoise (operations ps gen H) keySeed
        (KEM.deriveSeedAndKey (operations ps gen H)
          (KEM.hashPublicKey (operations ps gen H)
            (KEM.keygenFromCoins
              (operations ps gen H) fallback keySeed z).1)
          message salt).1 := by
  ext i j
  simp [Ideal.residual, samplesFromCoins, samplesFromStreams,
    PKE.decryptionNoise, PKE.keygenSamples, PKE.encryptionSamples,
    outputLength, outputBits, Matrix.mul_apply, Matrix.map_apply,
    Matrix.transpose_apply, Int.cast_sum, Int.cast_add, Int.cast_sub, Int.cast_mul]

theorem honestFailureProb_congr_of_bounded_agreement
    (ps : ParameterSet) (ops₁ ops₂ : Operations ps)
    (hgen : ops₁.gen = ops₂.gen)
    (hshake : ∀ (x : List Bool) (n : ℕ),
      x.length ∈ inputLengths ps → n ≤ outputBits ps →
        ops₁.shake x n = ops₂.shake x n) :
    KEM.honestFailureProb ops₁ = KEM.honestFailureProb ops₂ := by
  have hs (r : QueryRole) (x : List Bool) (hx : x.length = inputLength ps r) :
      ops₁.shake x (outputLength ps r) = ops₂.shake x (outputLength ps r) :=
    hshake x _ (hx ▸ (query_bounds ps r).1) (query_bounds ps r).2
  have hz (z : Bits lenZ) : ops₁.shake z.toList lenSeedA =
      ops₂.shake z.toList lenSeedA := hs .seedA _ (by simp [inputLength])
  have hkg (seed : SeedSEBits ps) :
      ops₁.shake (keygenPrefix.toList ++ seed.toList)
        (nbar * ps.params.n * lenChi + ps.params.n * nbar * lenChi) =
      ops₂.shake (keygenPrefix.toList ++ seed.toList)
        (nbar * ps.params.n * lenChi + ps.params.n * nbar * lenChi) :=
    hs .keygenNoise _ (by simp [inputLength])
  have he (seed : SeedSEBits ps) :
      ops₁.shake (encryptionPrefix.toList ++ seed.toList)
        (mbar * ps.params.n * lenChi + (mbar * ps.params.n * lenChi + mbar * nbar * lenChi)) =
      ops₂.shake (encryptionPrefix.toList ++ seed.toList)
        (mbar * ps.params.n * lenChi + (mbar * ps.params.n * lenChi + mbar * nbar * lenChi)) :=
    hs .encryptionNoise _ (by simp [inputLength])
  have hh (seed : SeedABits) (b : Bits (ps.params.n * nbar * ps.params.D)) :
      ops₁.shake (seed.toList ++ b.toList) ps.params.ell =
      ops₂.shake (seed.toList ++ b.toList) ps.params.ell :=
    hs .publicKeyHash _ (by simp [inputLength])
  have hd (pkh : PublicKeyHashBits ps) (message : MessageBits ps) (salt : SaltBits ps) :
      ops₁.shake (pkh.toList ++ message.toList ++ salt.toList)
        (ps.params.lenSeedSE + ps.params.ell) =
      ops₂.shake (pkh.toList ++ message.toList ++ salt.toList)
        (ps.params.lenSeedSE + ps.params.ell) :=
    hs .seedAndKey _ (by simp [inputLength, Nat.add_assoc])
  have hf (c1 : Bits (mbar * ps.params.n * ps.params.D))
      (c2 : Bits (mbar * nbar * ps.params.D)) (salt : SaltBits ps)
      (key : SharedSecretBits ps) :
      ops₁.shake (c1.toList ++ c2.toList ++ salt.toList ++ key.toList) ps.params.ell =
      ops₂.shake (c1.toList ++ c2.toList ++ salt.toList ++ key.toList) ps.params.ell :=
    hs .sharedSecret _ (by simp [inputLength, Nat.add_assoc])
  simp only [KEM.honestFailureProb, KEM.keygen_eq, KEM.encaps_eq,
    KEM.keygenFromCoins, KEM.encapsFromCoins, KEM.decaps,
    KEM.hashPublicKey, KEM.deriveSeedAndKey, PKE.keygenFromSeeds,
    PKE.encryptFromSeed, hz, hkg, he, hh, hd, hf, hgen]
  rfl

end FrodoKEM.ROM
