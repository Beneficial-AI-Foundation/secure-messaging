/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import ToVCVio.LatticeCrypto.FrodoKEM.Correctness.RandomOracle.Model
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable

/-!
# FrodoKEM correctness in the finite random-oracle model

This file proves that the five adaptive pre-residual random-oracle queries induce the same joint
noise law as independent ideal FrodoKEM noise. It then averages the existing deterministic KEM
failure containment over the sampled finite oracle table and honest coins.
-/

namespace FrodoKEM.ROM

open OracleComp OracleSpec LatticeCrypto ToVCVio
open scoped ENNReal

private def splitBitsEquiv (a b : ℕ) :
    Bits (a + b) ≃ Bits a × Bits b where
  toFun := splitBits
  invFun := fun p => p.1 ++ p.2
  left_inv := by
    intro v
    apply Vector.ext
    intro i hi
    simp only [splitBits, Vector.getElem_append hi]
    split
    · simp_all
    · simp only [Vector.getElem_ofFn]
      have hfin : Fin.natAdd a ⟨i - a, by omega⟩ = ⟨i, hi⟩ := by
        apply Fin.ext
        simp [Nat.add_sub_of_le (Nat.le_of_not_gt ‹¬i < a›)]
      exact congrArg (fun j : Fin (a + b) => v[j]) hfin
  right_inv := fun p => splitBits_append p.1 p.2

private abbrev NoiseStreams (ps : ParameterSet) :=
  (Bits (nbar * ps.params.n * lenChi) ×
    Bits (ps.params.n * nbar * lenChi)) ×
  (Bits (mbar * ps.params.n * lenChi) ×
    (Bits (mbar * ps.params.n * lenChi) ×
      Bits (mbar * nbar * lenChi)))

private def streamPairEquiv (ps : ParameterSet) :
    (Bits (outputLength ps .keygenNoise) × Bits (outputBits ps)) ≃
      NoiseStreams ps :=
  Equiv.prodCongr
    (splitBitsEquiv (nbar * ps.params.n * lenChi)
      (ps.params.n * nbar * lenChi))
    ((splitBitsEquiv (mbar * ps.params.n * lenChi)
      (mbar * ps.params.n * lenChi + mbar * nbar * lenChi)).trans
      (Equiv.prodCongr (Equiv.refl _)
        (splitBitsEquiv (mbar * ps.params.n * lenChi)
          (mbar * nbar * lenChi))))

private def streamsToSamples (ps : ParameterSet)
    (s : NoiseStreams ps) : Ideal.NoiseSamples ps :=
  {
    st := SampleMatrix ps.errorTable nbar ps.params.n s.1.1
    e := SampleMatrix ps.errorTable ps.params.n nbar s.1.2
    sp := SampleMatrix ps.errorTable mbar ps.params.n s.2.1
    ep := SampleMatrix ps.errorTable mbar ps.params.n s.2.2.1
    epp := SampleMatrix ps.errorTable mbar nbar s.2.2.2
  }

theorem finiteLaw_samplesFromStreams_uniform (ps : ParameterSet) :
    ToVCVio.finiteLaw
      (do
        let kg ← $ᵗ (Bits (outputLength ps .keygenNoise))
        let enc ← $ᵗ (Bits (outputBits ps))
        return samplesFromStreams ps kg enc) =
      ToVCVio.finiteLaw (Ideal.sampleNoise ps) := by
  let : MeasurableSpace
      (Bits (outputLength ps .keygenNoise) × Bits (outputBits ps)) := ⊤
  let : MeasurableSpace (NoiseStreams ps) := ⊤
  have he := SampleableType.map_uniformSample_evalDistEq_of_bijective
    (streamPairEquiv ps).bijective
  have hm := finiteLaw_map_congr he.evalDist_eq (streamsToSamples ps)
  rw [Functor.map_map] at hm
  calc
    ToVCVio.finiteLaw
        (do
          let kg ← $ᵗ (Bits (outputLength ps .keygenNoise))
          let enc ← $ᵗ (Bits (outputBits ps))
          return samplesFromStreams ps kg enc) =
      ToVCVio.finiteLaw
        ((fun p => samplesFromStreams ps p.1 p.2) <$>
          ($ᵗ (Bits (outputLength ps .keygenNoise) × Bits (outputBits ps)))) := by
        rw [SampleableType.uniformSample_prod_eq_bind]
        simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
    _ = ToVCVio.finiteLaw
        ((streamsToSamples ps ∘ streamPairEquiv ps) <$>
          ($ᵗ (Bits (outputLength ps .keygenNoise) × Bits (outputBits ps)))) := by
        congr 3
    _ = ToVCVio.finiteLaw (streamsToSamples ps <$> ($ᵗ (NoiseStreams ps))) := hm
    _ = ToVCVio.finiteLaw (Ideal.sampleNoise ps) := by
      simp only [SampleableType.uniformSample_prod_eq_bind, Ideal.sampleNoise,
        streamsToSamples, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply,
        pure_bind]

private abbrev RawInput (ps : ParameterSet) :=
  ToVCVio.FiniteXOF.Input (inputLengths ps)

private abbrev RawAnswer (ps : ParameterSet) := Bits (outputBits ps)

private abbrev RawOracle (ps : ParameterSet) := RawInput ps →ₒ RawAnswer ps

private noncomputable instance tableFintype (ps : ParameterSet) :
    Fintype (Table ps) := Fintype.ofFinite _

private noncomputable instance tableSampleable (ps : ParameterSet) :
    SampleableType (Table ps) := SampleableType.ofFintype _

private def queryInput (ps : ParameterSet) (role : QueryRole)
    (x : List Bool) (hx : x.length = inputLength ps role) : RawInput ps :=
  ToVCVio.FiniteXOF.encode (inputLengths ps) x
    (hx ▸ (query_bounds ps role).1)

private def longQuery (ps : ParameterSet) (role : QueryRole)
    (x : List Bool) (hx : x.length = inputLength ps role) :
    OracleComp (RawOracle ps) (RawAnswer ps) :=
  liftM ((RawOracle ps).query (queryInput ps role x hx))

private def publicKeyFromStreams (ps : ParameterSet) (gen : Generator ps)
    (seedA : SeedABits) (kg : Bits (outputLength ps .keygenNoise)) :
    PublicKey ps :=
  let kgParts := splitBits
    (a := nbar * ps.params.n * lenChi)
    (b := ps.params.n * nbar * lenChi) kg
  let st := (SampleMatrix ps.errorTable nbar ps.params.n kgParts.1).map
    (fun x : ℤ => (x : ZMod ps.params.q))
  let e := (SampleMatrix ps.errorTable ps.params.n nbar kgParts.2).map
    (fun x : ℤ => (x : ZMod ps.params.q))
  {
    seedA := seedA
    b := packBits ps ps.params.n nbar (publicKeyBits_mod_eight ps)
      (gen seedA * st.transpose + e)
  }

private def fixedCoinsProgram (ps : ParameterSet) (gen : Generator ps)
    (_fallback : SharedSecretBits ps) (keySeed : SeedSEBits ps)
    (z : Bits lenZ) (message : MessageBits ps) (salt : SaltBits ps) :
    OracleComp (RawOracle ps) (Ideal.NoiseSamples ps) := do
  let seedALong ← longQuery ps .seedA z.toList (by simp [inputLength])
  let seedA := ToVCVio.FiniteXOF.prefix seedALong lenSeedA
  let kgLong ← longQuery ps .keygenNoise
    (keygenPrefix.toList ++ keySeed.toList) (by simp [inputLength])
  let kg := ToVCVio.FiniteXOF.prefix kgLong (outputLength ps .keygenNoise)
  let pk := publicKeyFromStreams ps gen seedA kg
  let hashLong ← longQuery ps .publicKeyHash
    (pk.seedA.toList ++ pk.b.toList) (by simp [inputLength])
  let pkh := ToVCVio.FiniteXOF.prefix hashLong (outputLength ps .publicKeyHash)
  let derivedLong ← longQuery ps .seedAndKey
    (pkh.toList ++ message.toList ++ salt.toList)
      (by
        simp only [List.length_append]
        rw [Vector.length_toList, Vector.length_toList, Vector.length_toList]
        simp [inputLength, outputLength, Nat.add_assoc])
  let derived := splitBits (a := ps.params.lenSeedSE) (b := ps.params.ell)
    (ToVCVio.FiniteXOF.prefix derivedLong (outputLength ps .seedAndKey))
  let encLong ← longQuery ps .encryptionNoise
    (encryptionPrefix.toList ++ derived.1.toList) (by simp [inputLength])
  let enc := ToVCVio.FiniteXOF.prefix encLong (outputBits ps)
  return samplesFromStreams ps kg enc

private theorem eval_fixedCoinsProgram
    (ps : ParameterSet) (gen : Generator ps) (H : Table ps)
    (fallback : SharedSecretBits ps) (keySeed : SeedSEBits ps)
    (z : Bits lenZ) (message : MessageBits ps) (salt : SaltBits ps) :
    evalWithAnswerFn (QueryImpl.ofFn H)
        (fixedCoinsProgram ps gen fallback keySeed z message salt) =
      samplesFromCoins ps gen H fallback keySeed z message salt := by
  have hz : lenZ ∈ inputLengths ps := by
    simpa [inputLength] using (query_bounds ps .seedA).1
  have hkg : 8 + ps.params.lenSeedSE ∈ inputLengths ps := by
    simpa [inputLength] using (query_bounds ps .keygenNoise).1
  have hh : lenSeedA + ps.params.n * nbar * ps.params.D ∈ inputLengths ps := by
    simpa [inputLength] using (query_bounds ps .publicKeyHash).1
  have hd : ps.params.ell + (ps.params.ell + ps.params.lenSalt) ∈ inputLengths ps := by
    simpa [inputLength, Nat.add_assoc] using (query_bounds ps .seedAndKey).1
  simp only [fixedCoinsProgram, longQuery, evalWithAnswerFn_bind,
    evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply, evalWithAnswerFn_pure]
  simp [samplesFromCoins, operations, ToVCVio.FiniteXOF.answer, queryInput,
    publicKeyFromStreams, KEM.keygenFromCoins, PKE.keygenFromSeeds,
    KEM.hashPublicKey, KEM.deriveSeedAndKey, hz, hkg, hh, hd,
    outputLength, outputBits]

private def fiveQueryProgram {D R α : Type}
    (q₀ : D) (q₁ : R → D) (q₂ : R → R → D)
    (q₃ : R → R → R → D) (q₄ : R → R → R → R → D)
    (out : R → R → R → R → R → α) : OracleComp (D →ₒ R) α := do
  let u₀ ← liftM ((D →ₒ R).query q₀)
  let u₁ ← liftM ((D →ₒ R).query (q₁ u₀))
  let u₂ ← liftM ((D →ₒ R).query (q₂ u₀ u₁))
  let u₃ ← liftM ((D →ₒ R).query (q₃ u₀ u₁ u₂))
  let u₄ ← liftM ((D →ₒ R).query (q₄ u₀ u₁ u₂ u₃))
  return out u₀ u₁ u₂ u₃ u₄

private theorem randomOracle_query_bind_run'
    {D R α : Type} [DecidableEq D] [SampleableType R]
    (t : D) (k : R → OracleComp (D →ₒ R) α)
    (c : (D →ₒ R).QueryCache) :
    (simulateQ (D →ₒ R).randomOracle
      (liftM ((D →ₒ R).query t) >>= k)).run' c =
      (((D →ₒ R).randomOracle t).run c) >>=
        fun p => (simulateQ (D →ₒ R).randomOracle (k p.1)).run' p.2 := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

private theorem fiveQueryProgram_run_eq {D R α : Type}
    [DecidableEq D] [SampleableType R]
    (q₀ : D) (q₁ : R → D) (q₂ : R → R → D)
    (q₃ : R → R → R → D) (q₄ : R → R → R → R → D)
    (out : R → R → R → R → R → α)
    (h₁₀ : ∀ u₀, q₁ u₀ ≠ q₀)
    (h₂₀ : ∀ u₀ u₁, q₂ u₀ u₁ ≠ q₀)
    (h₂₁ : ∀ u₀ u₁, q₂ u₀ u₁ ≠ q₁ u₀)
    (h₃₀ : ∀ u₀ u₁ u₂, q₃ u₀ u₁ u₂ ≠ q₀)
    (h₃₁ : ∀ u₀ u₁ u₂, q₃ u₀ u₁ u₂ ≠ q₁ u₀)
    (h₃₂ : ∀ u₀ u₁ u₂, q₃ u₀ u₁ u₂ ≠ q₂ u₀ u₁)
    (h₄₀ : ∀ u₀ u₁ u₂ u₃, q₄ u₀ u₁ u₂ u₃ ≠ q₀)
    (h₄₁ : ∀ u₀ u₁ u₂ u₃, q₄ u₀ u₁ u₂ u₃ ≠ q₁ u₀)
    (h₄₂ : ∀ u₀ u₁ u₂ u₃, q₄ u₀ u₁ u₂ u₃ ≠ q₂ u₀ u₁)
    (h₄₃ : ∀ u₀ u₁ u₂ u₃, q₄ u₀ u₁ u₂ u₃ ≠ q₃ u₀ u₁ u₂) :
    (simulateQ (D →ₒ R).randomOracle
      (fiveQueryProgram q₀ q₁ q₂ q₃ q₄ out)).run' ∅ =
      (do
        let u₀ ← $ᵗ R
        let u₁ ← $ᵗ R
        let u₂ ← $ᵗ R
        let u₃ ← $ᵗ R
        let u₄ ← $ᵗ R
        return out u₀ u₁ u₂ u₃ u₄) := by
  simp only [fiveQueryProgram, randomOracle_query_bind_run', randomOracle.run_eq,
    QueryCache.empty_apply]
  simp [QueryCache.cacheQuery_of_ne, h₁₀, h₂₀, h₂₁, h₃₀, h₃₁, h₃₂,
    h₄₀, h₄₁, h₄₂, h₄₃, map_eq_bind_pure_comp, bind_assoc]

private def coinQuery₀ (ps : ParameterSet) (z : Bits lenZ) : RawInput ps :=
  queryInput ps .seedA z.toList (by simp [inputLength])

private def coinQuery₁ (ps : ParameterSet) (keySeed : SeedSEBits ps)
    (_u₀ : RawAnswer ps) : RawInput ps :=
  queryInput ps .keygenNoise (keygenPrefix.toList ++ keySeed.toList)
    (by simp [inputLength])

private def coinQuery₂ (ps : ParameterSet) (gen : Generator ps)
    (u₀ u₁ : RawAnswer ps) : RawInput ps :=
  let seedA := ToVCVio.FiniteXOF.prefix u₀ lenSeedA
  let kg := ToVCVio.FiniteXOF.prefix u₁ (outputLength ps .keygenNoise)
  let pk := publicKeyFromStreams ps gen seedA kg
  queryInput ps .publicKeyHash (pk.seedA.toList ++ pk.b.toList)
    (by simp [inputLength])

private def coinQuery₃ (ps : ParameterSet) (message : MessageBits ps)
    (salt : SaltBits ps) (_u₀ _u₁ u₂ : RawAnswer ps) : RawInput ps :=
  let pkh := ToVCVio.FiniteXOF.prefix u₂ (outputLength ps .publicKeyHash)
  queryInput ps .seedAndKey (pkh.toList ++ message.toList ++ salt.toList)
    (by
      simp only [List.length_append]
      rw [Vector.length_toList, Vector.length_toList, Vector.length_toList]
      simp [inputLength, outputLength, Nat.add_assoc])

private def coinQuery₄ (ps : ParameterSet) (_u₀ _u₁ _u₂ u₃ : RawAnswer ps) :
    RawInput ps :=
  let derived := splitBits (a := ps.params.lenSeedSE) (b := ps.params.ell)
    (ToVCVio.FiniteXOF.prefix u₃ (outputLength ps .seedAndKey))
  queryInput ps .encryptionNoise
    (encryptionPrefix.toList ++ derived.1.toList) (by simp [inputLength])

private def coinOutput (ps : ParameterSet)
    (_u₀ u₁ _u₂ _u₃ u₄ : RawAnswer ps) : Ideal.NoiseSamples ps :=
  samplesFromStreams ps
    (ToVCVio.FiniteXOF.prefix u₁ (outputLength ps .keygenNoise))
    (ToVCVio.FiniteXOF.prefix u₄ (outputBits ps))

private theorem fixedCoinsProgram_eq_fiveQuery
    (ps : ParameterSet) (gen : Generator ps)
    (fallback : SharedSecretBits ps) (keySeed : SeedSEBits ps)
    (z : Bits lenZ) (message : MessageBits ps) (salt : SaltBits ps) :
    fixedCoinsProgram ps gen fallback keySeed z message salt =
      fiveQueryProgram (coinQuery₀ ps z) (coinQuery₁ ps keySeed)
        (coinQuery₂ ps gen) (coinQuery₃ ps message salt) (coinQuery₄ ps)
        (coinOutput ps) := by
  rfl

private theorem queryInput_ne_of_role_ne (ps : ParameterSet)
    {r s : QueryRole} (hrs : r ≠ s)
    (x y : List Bool) (hx : x.length = inputLength ps r)
    (hy : y.length = inputLength ps s)
    (hdx : InDomain ps r x) (hdy : InDomain ps s y) :
    queryInput ps r x hx ≠ queryInput ps s y hy := by
  intro h
  have hxy := (ToVCVio.FiniteXOF.encode_eq_iff
    (inputLengths ps) x y
    (hx ▸ (query_bounds ps r).1)
    (hy ▸ (query_bounds ps s).1)).mp h
  subst y
  exact domain_disjoint ps hrs x ⟨hdx, hdy⟩

private theorem seedAText_domain (ps : ParameterSet) (z : Bits lenZ) :
    InDomain ps .seedA z.toList := by
  simp [InDomain, inputLength]

private theorem keygenText_domain (ps : ParameterSet) (keySeed : SeedSEBits ps) :
    InDomain ps .keygenNoise (keygenPrefix.toList ++ keySeed.toList) := by
  constructor
  · simp [inputLength]
  · simp [keygenPrefix]

private theorem publicHashText_domain (ps : ParameterSet) (pk : PublicKey ps) :
    InDomain ps .publicKeyHash (pk.seedA.toList ++ pk.b.toList) := by
  simp [InDomain, inputLength]

private theorem seedAndKeyText_domain (ps : ParameterSet)
    (pkh : PublicKeyHashBits ps) (message : MessageBits ps) (salt : SaltBits ps) :
    InDomain ps .seedAndKey (pkh.toList ++ message.toList ++ salt.toList) := by
  simp [InDomain, inputLength, Nat.add_assoc]

private theorem encryptionText_domain (ps : ParameterSet) (seed : SeedSEBits ps) :
    InDomain ps .encryptionNoise (encryptionPrefix.toList ++ seed.toList) := by
  constructor
  · simp [inputLength]
  · simp [encryptionPrefix]

private theorem coinQuery₁_ne₀ (ps : ParameterSet)
    (keySeed : SeedSEBits ps) (z : Bits lenZ) (u₀ : RawAnswer ps) :
    coinQuery₁ ps keySeed u₀ ≠ coinQuery₀ ps z := by
  unfold coinQuery₁ coinQuery₀
  apply queryInput_ne_of_role_ne ps (by decide)
  · exact keygenText_domain ps keySeed
  · exact seedAText_domain ps z

private theorem coinQuery₂_ne₀ (ps : ParameterSet) (gen : Generator ps)
    (z : Bits lenZ) (u₀ u₁ : RawAnswer ps) :
    coinQuery₂ ps gen u₀ u₁ ≠ coinQuery₀ ps z := by
  unfold coinQuery₂ coinQuery₀
  apply queryInput_ne_of_role_ne ps (by decide)
  · exact publicHashText_domain ps _
  · exact seedAText_domain ps z

private theorem coinQuery₂_ne₁ (ps : ParameterSet) (gen : Generator ps)
    (keySeed : SeedSEBits ps) (u₀ u₁ : RawAnswer ps) :
    coinQuery₂ ps gen u₀ u₁ ≠ coinQuery₁ ps keySeed u₀ := by
  unfold coinQuery₂ coinQuery₁
  apply queryInput_ne_of_role_ne ps (by decide)
  · exact publicHashText_domain ps _
  · exact keygenText_domain ps keySeed

private theorem coinQuery₃_ne₀ (ps : ParameterSet)
    (message : MessageBits ps) (salt : SaltBits ps) (z : Bits lenZ)
    (u₀ u₁ u₂ : RawAnswer ps) :
    coinQuery₃ ps message salt u₀ u₁ u₂ ≠ coinQuery₀ ps z := by
  unfold coinQuery₃ coinQuery₀
  apply queryInput_ne_of_role_ne ps (by decide)
  · exact seedAndKeyText_domain ps _ message salt
  · exact seedAText_domain ps z

private theorem coinQuery₃_ne₁ (ps : ParameterSet)
    (message : MessageBits ps) (salt : SaltBits ps)
    (keySeed : SeedSEBits ps) (u₀ u₁ u₂ : RawAnswer ps) :
    coinQuery₃ ps message salt u₀ u₁ u₂ ≠ coinQuery₁ ps keySeed u₀ := by
  unfold coinQuery₃ coinQuery₁
  apply queryInput_ne_of_role_ne ps (by decide)
  · exact seedAndKeyText_domain ps _ message salt
  · exact keygenText_domain ps keySeed

private theorem coinQuery₃_ne₂ (ps : ParameterSet) (gen : Generator ps)
    (message : MessageBits ps) (salt : SaltBits ps)
    (u₀ u₁ u₂ : RawAnswer ps) :
    coinQuery₃ ps message salt u₀ u₁ u₂ ≠ coinQuery₂ ps gen u₀ u₁ := by
  unfold coinQuery₃ coinQuery₂
  apply queryInput_ne_of_role_ne ps (by decide)
  · exact seedAndKeyText_domain ps _ message salt
  · exact publicHashText_domain ps _

private theorem coinQuery₄_ne₀ (ps : ParameterSet) (z : Bits lenZ)
    (u₀ u₁ u₂ u₃ : RawAnswer ps) :
    coinQuery₄ ps u₀ u₁ u₂ u₃ ≠ coinQuery₀ ps z := by
  unfold coinQuery₄ coinQuery₀
  apply queryInput_ne_of_role_ne ps (by decide)
  · exact encryptionText_domain ps _
  · exact seedAText_domain ps z

private theorem coinQuery₄_ne₁ (ps : ParameterSet) (keySeed : SeedSEBits ps)
    (u₀ u₁ u₂ u₃ : RawAnswer ps) :
    coinQuery₄ ps u₀ u₁ u₂ u₃ ≠ coinQuery₁ ps keySeed u₀ := by
  unfold coinQuery₄ coinQuery₁
  apply queryInput_ne_of_role_ne ps (by decide)
  · exact encryptionText_domain ps _
  · exact keygenText_domain ps keySeed

private theorem coinQuery₄_ne₂ (ps : ParameterSet) (gen : Generator ps)
    (u₀ u₁ u₂ u₃ : RawAnswer ps) :
    coinQuery₄ ps u₀ u₁ u₂ u₃ ≠ coinQuery₂ ps gen u₀ u₁ := by
  unfold coinQuery₄ coinQuery₂
  apply queryInput_ne_of_role_ne ps (by decide)
  · exact encryptionText_domain ps _
  · exact publicHashText_domain ps _

private theorem coinQuery₄_ne₃ (ps : ParameterSet)
    (message : MessageBits ps) (salt : SaltBits ps)
    (u₀ u₁ u₂ u₃ : RawAnswer ps) :
    coinQuery₄ ps u₀ u₁ u₂ u₃ ≠ coinQuery₃ ps message salt u₀ u₁ u₂ := by
  unfold coinQuery₄ coinQuery₃
  apply queryInput_ne_of_role_ne ps (by decide)
  · exact encryptionText_domain ps _
  · exact seedAndKeyText_domain ps _ message salt

private theorem fixedCoinsProgram_run_eq
    (ps : ParameterSet) (gen : Generator ps)
    (fallback : SharedSecretBits ps) (keySeed : SeedSEBits ps)
    (z : Bits lenZ) (message : MessageBits ps) (salt : SaltBits ps) :
    (simulateQ (RawOracle ps).randomOracle
      (fixedCoinsProgram ps gen fallback keySeed z message salt)).run' ∅ =
      (do
        let u₀ ← $ᵗ (RawAnswer ps)
        let u₁ ← $ᵗ (RawAnswer ps)
        let u₂ ← $ᵗ (RawAnswer ps)
        let u₃ ← $ᵗ (RawAnswer ps)
        let u₄ ← $ᵗ (RawAnswer ps)
        return coinOutput ps u₀ u₁ u₂ u₃ u₄) := by
  rw [fixedCoinsProgram_eq_fiveQuery]
  exact fiveQueryProgram_run_eq
    (coinQuery₀ ps z) (coinQuery₁ ps keySeed) (coinQuery₂ ps gen)
    (coinQuery₃ ps message salt) (coinQuery₄ ps) (coinOutput ps)
    (coinQuery₁_ne₀ ps keySeed z)
    (coinQuery₂_ne₀ ps gen z) (coinQuery₂_ne₁ ps gen keySeed)
    (coinQuery₃_ne₀ ps message salt z)
    (coinQuery₃_ne₁ ps message salt keySeed)
    (coinQuery₃_ne₂ ps gen message salt)
    (coinQuery₄_ne₀ ps z) (coinQuery₄_ne₁ ps keySeed)
    (coinQuery₄_ne₂ ps gen) (coinQuery₄_ne₃ ps message salt)

private theorem finiteLaw_bind_head {α β : Type} {mx my : ProbComp α}
    (h : finiteLaw mx = finiteLaw my) (k : α → ProbComp β) :
    finiteLaw (mx >>= k) = finiteLaw (my >>= k) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  exact ((EvalDistEq.of_evalDist_eq h).bind (fun _ => EvalDistEq.refl _)).evalDist_eq

private theorem finiteLaw_bind_const {α β : Type}
    (mx : ProbComp α) (my : ProbComp β) :
    finiteLaw (mx >>= fun _ => my) = finiteLaw my := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  exact (EvalDistEq.bind_const mx my).evalDist_eq

private theorem finiteLaw_fiveAnswers (ps : ParameterSet) :
    finiteLaw
      (do
        let u₀ ← $ᵗ (RawAnswer ps)
        let u₁ ← $ᵗ (RawAnswer ps)
        let u₂ ← $ᵗ (RawAnswer ps)
        let u₃ ← $ᵗ (RawAnswer ps)
        let u₄ ← $ᵗ (RawAnswer ps)
        return coinOutput ps u₀ u₁ u₂ u₃ u₄) =
      finiteLaw
        (do
          let kg ← $ᵗ (Bits (outputLength ps .keygenNoise))
          let enc ← $ᵗ (Bits (outputBits ps))
          return samplesFromStreams ps kg enc) := by
  let long := $ᵗ (RawAnswer ps)
  let rest (u₁ : RawAnswer ps) : ProbComp (Ideal.NoiseSamples ps) := do
    let u₄ ← long
    return samplesFromStreams ps
      (ToVCVio.FiniteXOF.prefix u₁ (outputLength ps .keygenNoise))
      (ToVCVio.FiniteXOF.prefix u₄ (outputBits ps))
  let tail (u₁ : RawAnswer ps) : ProbComp (Ideal.NoiseSamples ps) := do
    let _u₂ ← long
    let _u₃ ← long
    rest u₁
  let middle : ProbComp (Ideal.NoiseSamples ps) := do
    let u₁ ← long
    tail u₁
  have hdrop : finiteLaw
      (do
        let u₀ ← long
        let u₁ ← long
        let u₂ ← long
        let u₃ ← long
        let u₄ ← long
        return coinOutput ps u₀ u₁ u₂ u₃ u₄) =
      finiteLaw (do let u₁ ← long; rest u₁) := by
    have htail (u₁ : RawAnswer ps) : finiteLaw (tail u₁) = finiteLaw (rest u₁) := by
      apply (finiteLaw_bind_const long _).trans
      exact finiteLaw_bind_const long (rest u₁)
    have hmiddle : finiteLaw middle =
        finiteLaw (do let u₁ ← long; rest u₁) :=
      finiteLaw_bind_congr long htail
    calc
      finiteLaw
          (do
            let u₀ ← long
            let u₁ ← long
            let u₂ ← long
            let u₃ ← long
            let u₄ ← long
            return coinOutput ps u₀ u₁ u₂ u₃ u₄) =
        finiteLaw (long >>= fun _ => middle) := by rfl
      _ = finiteLaw middle := finiteLaw_bind_const long middle
      _ = finiteLaw (do let u₁ ← long; rest u₁) := hmiddle
  apply hdrop.trans
  have hkg := ToVCVio.FiniteXOF.finiteLaw_prefix_uniform
    (outputBits ps) (outputLength ps .keygenNoise)
    (query_bounds ps .keygenNoise).2
  have henc := ToVCVio.FiniteXOF.finiteLaw_prefix_uniform
    (outputBits ps) (outputBits ps) (by rfl)
  have htwo : finiteLaw
      (do
        let u₁ ← long
        let u₄ ← long
        return samplesFromStreams ps
          (ToVCVio.FiniteXOF.prefix u₁ (outputLength ps .keygenNoise))
          (ToVCVio.FiniteXOF.prefix u₄ (outputBits ps))) =
      finiteLaw
        (do
          let kg ← $ᵗ (Bits (outputLength ps .keygenNoise))
          let enc ← $ᵗ (Bits (outputBits ps))
          return samplesFromStreams ps kg enc) := by
    have hmap : finiteLaw
        ((ToVCVio.FiniteXOF.prefix · (outputLength ps .keygenNoise)) <$> long >>=
          fun kg => (ToVCVio.FiniteXOF.prefix · (outputBits ps)) <$> long >>=
            fun enc => pure (samplesFromStreams ps kg enc)) =
        finiteLaw
          (($ᵗ (Bits (outputLength ps .keygenNoise))) >>= fun kg =>
            ($ᵗ (Bits (outputBits ps))) >>= fun enc =>
              pure (samplesFromStreams ps kg enc)) := by
      apply (finiteLaw_bind_head hkg _).trans
      refine finiteLaw_bind_congr
        ($ᵗ (Bits (outputLength ps .keygenNoise))) fun _ => ?_
      exact finiteLaw_bind_head henc _
    simpa only [rest, long, map_eq_bind_pure_comp, Function.comp_apply,
      bind_assoc, pure_bind] using hmap
  exact htwo

private theorem finiteLaw_lazy_fixedCoins
    (ps : ParameterSet) (gen : Generator ps)
    (fallback : SharedSecretBits ps) (keySeed : SeedSEBits ps)
    (z : Bits lenZ) (message : MessageBits ps) (salt : SaltBits ps) :
    finiteLaw
        ((simulateQ (RawOracle ps).randomOracle
          (fixedCoinsProgram ps gen fallback keySeed z message salt)).run' ∅) =
      finiteLaw (Ideal.sampleNoise ps) := by
  rw [fixedCoinsProgram_run_eq]
  exact (finiteLaw_fiveAnswers ps).trans
    (finiteLaw_samplesFromStreams_uniform ps)

theorem finiteLaw_samplesFromCoins
    (ps : ParameterSet) (gen : Generator ps)
    (fallback : SharedSecretBits ps) (keySeed : SeedSEBits ps)
    (z : Bits lenZ) (message : MessageBits ps) (salt : SaltBits ps) :
    ToVCVio.finiteLaw
      ((fun H =>
          samplesFromCoins ps gen H fallback keySeed z message salt) <$>
      ToVCVio.FiniteXOF.sampleTable
          (inputLengths ps) (outputBits ps)) =
      ToVCVio.finiteLaw (Ideal.sampleNoise ps) := by
  let : MeasurableSpace (Table ps) := ⊤
  let : MeasurableSpace (Ideal.NoiseSamples ps) := ⊤
  have htable : finiteLaw
      (ToVCVio.FiniteXOF.sampleTable (inputLengths ps) (outputBits ps)) =
      finiteLaw ($ᵗ (Table ps)) := by
    unfold ToVCVio.FiniteXOF.sampleTable
    exact SampleableType.evalDist_uniformSample_inst_irrel _ _
  have htableMap := finiteLaw_map_congr htable
    (fun H => samplesFromCoins ps gen H fallback keySeed z message salt)
  have heager :=
    OracleComp.evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTable
      (fixedCoinsProgram ps gen fallback keySeed z message salt)
  have heager' : finiteLaw
      ((fun H => samplesFromCoins ps gen H fallback keySeed z message salt) <$>
        ($ᵗ (Table ps))) =
      finiteLaw
        ((simulateQ (RawOracle ps).randomOracle
          (fixedCoinsProgram ps gen fallback keySeed z message salt)).run' ∅) := by
    calc
      finiteLaw
          ((fun H => samplesFromCoins ps gen H fallback keySeed z message salt) <$>
            ($ᵗ (Table ps))) =
        finiteLaw
          (do
            let H ← $ᵗ (Table ps)
            pure (evalWithAnswerFn (QueryImpl.ofFn H)
              (fixedCoinsProgram ps gen fallback keySeed z message salt))) := by
          simp only [map_eq_bind_pure_comp, Function.comp_def]
          refine finiteLaw_bind_congr ($ᵗ (Table ps)) fun H => ?_
          rw [eval_fixedCoinsProgram]
      _ = finiteLaw
          ((simulateQ (RawOracle ps).randomOracle
            (fixedCoinsProgram ps gen fallback keySeed z message salt)).run' ∅) :=
        heager.symm
  exact htableMap.trans (heager'.trans
    (finiteLaw_lazy_fixedCoins ps gen fallback keySeed z message salt))

/-- Honest KEM failure averaged over a sampled finite oracle table and all honest coins. -/
noncomputable def honestFailureProb
    (ps : ParameterSet) (gen : Generator ps) : ℝ≥0∞ :=
  Pr{
    let H ← ToVCVio.FiniteXOF.sampleTable
      (inputLengths ps) (outputBits ps)
    let keys ← KEM.keygen (operations ps gen H)
    let out ← KEM.encaps (operations ps gen H) keys.1
  }[
    KEM.decaps (operations ps gen H) keys.2 out.1 ≠ out.2
  ]

/-- Residual-noise failure averaged over the same finite oracle table and honest coins. -/
noncomputable def honestNoiseBadProb
    (ps : ParameterSet) (gen : Generator ps) : ℝ≥0∞ :=
  Pr{
    let H ← ToVCVio.FiniteXOF.sampleTable
      (inputLengths ps) (outputBits ps)
    let fallback ← $ᵗ (SharedSecretBits ps)
    let keySeed ← $ᵗ (SeedSEBits ps)
    let z ← $ᵗ (Bits lenZ)
    let message ← $ᵗ (MessageBits ps)
    let salt ← $ᵗ (SaltBits ps)
  }[
    ¬ NoiseBound ps.params
      (PKE.decryptionNoise (operations ps gen H) keySeed
        (KEM.deriveSeedAndKey (operations ps gen H)
          (KEM.hashPublicKey (operations ps gen H)
            (KEM.keygenFromCoins
              (operations ps gen H) fallback keySeed z).1)
          message salt).1)
  ]

private theorem prob_bind_const {α : Type} (mx : ProbComp α)
    (hmx : Pr{let _ ← mx}[True] = 1) (f : α → ProbComp Prop) {ε : ℝ≥0∞}
    (h : ∀ a, prEvent (f a) = ε) : prEvent (mx >>= f) = ε := by
  have hh := prEvent_bind_eq_of_forall_eq mx hmx f (fun p => p)
    (fun a => by simpa only [id_map'] using h a)
  simpa only [id_map'] using hh

private theorem five_coin_average {T A B C D E : Type}
    (table : ProbComp T) (a : ProbComp A) (b : ProbComp B) (c : ProbComp C)
    (d : ProbComp D) (e : ProbComp E) (P : T → A → B → C → D → E → Prop)
    (ha : Pr{let _ ← a}[True] = 1) (hb : Pr{let _ ← b}[True] = 1)
    (hc : Pr{let _ ← c}[True] = 1) (hd : Pr{let _ ← d}[True] = 1)
    (he : Pr{let _ ← e}[True] = 1) {ε : ℝ≥0∞}
    (h : ∀ aa bb cc dd ee, Pr{let t ← table}[P t aa bb cc dd ee] = ε) :
    Pr{
      let t ← table
      let aa ← a
      let bb ← b
      let cc ← c
      let dd ← d
      let ee ← e
    }[P t aa bb cc dd ee] = ε := by
  simp only [← bind_pure_comp]
  rw [OracleComp.prEvent_bind_bind_swap]
  apply prob_bind_const a ha
  intro aa
  rw [OracleComp.prEvent_bind_bind_swap]
  apply prob_bind_const b hb
  intro bb
  rw [OracleComp.prEvent_bind_bind_swap]
  apply prob_bind_const c hc
  intro cc
  rw [OracleComp.prEvent_bind_bind_swap]
  apply prob_bind_const d hd
  intro dd
  rw [OracleComp.prEvent_bind_bind_swap]
  apply prob_bind_const e he
  intro ee
  simpa only [← bind_pure_comp] using h aa bb cc dd ee

/-- The table-averaged residual-noise event has exactly the accepted ideal noise law. -/
theorem honestNoiseBadProb_eq_ideal
    (ps : ParameterSet) (gen : Generator ps) :
    honestNoiseBadProb ps gen = Ideal.noiseBadProb ps := by
  let P (H : Table ps) (fallback : SharedSecretBits ps) (keySeed : SeedSEBits ps)
      (z : Bits lenZ) (message : MessageBits ps) (salt : SaltBits ps) : Prop :=
    ¬ NoiseBound ps.params
      (PKE.decryptionNoise (operations ps gen H) keySeed
        (KEM.deriveSeedAndKey (operations ps gen H)
          (KEM.hashPublicKey (operations ps gen H)
            (KEM.keygenFromCoins (operations ps gen H) fallback keySeed z).1)
          message salt).1)
  have hpoint (fallback : SharedSecretBits ps) (keySeed : SeedSEBits ps)
      (z : Bits lenZ) (message : MessageBits ps) (salt : SaltBits ps) :
      Pr{let H ← ToVCVio.FiniteXOF.sampleTable (inputLengths ps) (outputBits ps)}[
        P H fallback keySeed z message salt] = Ideal.noiseBadProb ps := by
    have h := (EvalDistEq.of_evalDist_eq
      (finiteLaw_samplesFromCoins ps gen fallback keySeed z message salt)).prEvent_eq
        (fun t => ¬ NoiseBound ps.params
          ((Ideal.residual t).map (fun z : ℤ => (z : ZMod ps.params.q))))
    simpa only [prEvent_map, samplesFromCoins_residual_eq, Ideal.noiseBadProb, P] using h
  exact five_coin_average
    (T := Table ps) (A := SharedSecretBits ps) (B := SeedSEBits ps)
    (C := Bits lenZ) (D := MessageBits ps) (E := SaltBits ps)
    (table := ToVCVio.FiniteXOF.sampleTable (inputLengths ps) (outputBits ps))
    (a := $ᵗ (SharedSecretBits ps)) (b := $ᵗ (SeedSEBits ps))
    (c := $ᵗ (Bits lenZ)) (d := $ᵗ (MessageBits ps))
    (e := $ᵗ (SaltBits ps)) (P := P)
    (by simp) (by simp) (by simp) (by simp) (by simp) hpoint

private theorem honestFailureProb_le_honestNoiseBadProb
    (ps : ParameterSet) (gen : Generator ps) :
    honestFailureProb ps gen ≤ honestNoiseBadProb ps gen := by
  unfold honestFailureProb honestNoiseBadProb
  apply prEvent_bind_mono_of_support
  intro H _
  exact KEM.honestFailureProb_le_honestNoiseBadProb (operations ps gen H)

/-- Honest finite-random-oracle KEM failure is bounded by the accepted ideal noise event. -/
theorem honestFailureProb_le_idealNoiseBadProb
    (ps : ParameterSet) (gen : Generator ps) :
    honestFailureProb ps gen ≤ Ideal.noiseBadProb ps := by
  rw [← honestNoiseBadProb_eq_ideal]
  exact honestFailureProb_le_honestNoiseBadProb ps gen

end FrodoKEM.ROM
