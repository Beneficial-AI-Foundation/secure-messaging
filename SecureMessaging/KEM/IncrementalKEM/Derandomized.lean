/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.IncrementalKEM.Defs

/-!
# Incremental KEM with explicit coins

An incremental KEM (`KEMScheme.IncrementalStructure`) splits public keys into a header and a
vector, and encapsulation into two stages. `IncrementalKEMDet` gives one with explicit coins: key
generation and the first stage are deterministic functions of their coins, which come with
samplers, and the second stage and decapsulation are deterministic.

`toKEM` is the KEM that samples the coins and runs these functions on them, and `toIncremental`
is its incremental structure. `toRandLeak` is its randomness leakage: key generation and the
first stage also return the coins they draw.
-/

namespace KEMScheme

universe u

/-- Deterministic incremental KEM algorithms and their coin samplers. -/
-- ANCHOR: IncrementalKEMDet
structure IncrementalKEMDet (m : Type → Type u) (K PK SK C : Type) where
  /-- Public-key header. -/
  PKheader : Type
  /-- Public-key vector. -/
  PKvector : Type
  /-- First ciphertext component. -/
  C₁ : Type
  /-- Second ciphertext component. -/
  C₂ : Type
  /-- Secret state retained between encapsulation stages. -/
  St : Type
  /-- Key-generation coins. -/
  KeygenRand : Type
  /-- First-stage encapsulation coins. -/
  Encaps1Rand : Type
  /-- Consistency of a public-key header and vector. -/
  validPK : PKheader → PKvector → Bool
  /-- Public keys are precisely the valid header/vector pairs. -/
  splitPK : PK ≃ { parts : PKheader × PKvector // validPK parts.1 parts.2 = true }
  /-- Ciphertext decomposition into its two components. -/
  splitC : C ≃ C₁ × C₂
  /-- Key generation from explicit coins. -/
  keygenDet : KeygenRand → PK × SK
  /-- First-stage encapsulation from a header and explicit coins. -/
  encaps1Det : PKheader → Encaps1Rand → St × C₁ × K
  /-- Second-stage encapsulation using the retained state. -/
  encaps2Det : St → PKheader → PKvector → C₂
  /-- Decapsulation, with `none` denoting rejection. -/
  decapsDet : SK → C → Option K
  /-- Sampler for key-generation coins. -/
  sampleKeygen : m KeygenRand
  /-- Sampler for first-stage encapsulation coins. -/
  sampleEncaps1 : m Encaps1Rand
-- ANCHOR_END: IncrementalKEMDet

namespace IncrementalKEMDet

variable {m : Type → Type u} [Monad m] {K PK SK C : Type}
  (det : IncrementalKEMDet m K PK SK C)

/-- The header of a public key. -/
def toHeader (pk : PK) : det.PKheader := (det.splitPK pk).1.1

/-- The vector of a public key. -/
def toVector (pk : PK) : det.PKvector := (det.splitPK pk).1.2

-- ANCHOR: IncrementalKEMDet_toKEM
/-- The KEM that samples the coins and runs the deterministic algorithms on them. -/
def toKEM : KEMScheme m K PK SK C where
  keygen := det.keygenDet <$> det.sampleKeygen
  encaps pk := do
    let (hdr, vec) := (det.splitPK pk).1
    let (st, c1, k) ← det.encaps1Det hdr <$> det.sampleEncaps1
    let c2 ← pure (det.encaps2Det st hdr vec)
    pure (det.splitC.symm (c1, c2), k)
  decaps sk c := pure (det.decapsDet sk c)
-- ANCHOR_END: IncrementalKEMDet_toKEM

-- ANCHOR: IncrementalKEMDet_toIncremental
/-- Incremental structure obtained by sampling coins for the first stage. -/
def toIncremental : det.toKEM.IncrementalStructure where
  PKheader := det.PKheader
  PKvector := det.PKvector
  C₁ := det.C₁
  C₂ := det.C₂
  St := det.St
  validPK := det.validPK
  splitPK := det.splitPK
  splitC := det.splitC
  encaps1 hdr := det.encaps1Det hdr <$> det.sampleEncaps1
  encaps2 st hdr vec := pure (det.encaps2Det st hdr vec)
  factor _ := rfl
-- ANCHOR_END: IncrementalKEMDet_toIncremental

/-- The derived KEM has the supplied deterministic decapsulation. -/
def toDetDecaps : det.toKEM.DeterministicDecaps where
  decapsDet := det.decapsDet
  decaps_eq _ _ := rfl

/-- The derived incremental structure has the supplied deterministic second stage. -/
def toDetEncaps2 : det.toIncremental.DeterministicEncaps2 where
  encaps2Det := det.encaps2Det
  encaps2_eq _ _ _ := rfl

-- ANCHOR: IncrementalKEMDet_toRandLeak
/-- Randomness leakage of the derived incremental structure: key generation and the first stage
also return their coins, and the second stage draws none. -/
def toRandLeak [LawfulMonad m] : det.toKEM.IncrementalRandLeak det.toIncremental where
  KeygenRand := det.KeygenRand
  Encaps1Rand := det.Encaps1Rand
  Encaps2Rand := Unit
  keygenRleak := do
    let r ← det.sampleKeygen
    pure (det.keygenDet r, r)
  encaps1Rleak hdr := do
    let r ← det.sampleEncaps1
    pure (det.encaps1Det hdr r, r)
  encaps2Rleak st hdr vec := pure (det.encaps2Det st hdr vec, ())
  keygen_fst := by simp only [toKEM, map_eq_pure_bind, bind_assoc, pure_bind]
  encaps1_fst _ := by simp only [toIncremental, map_eq_pure_bind, bind_assoc, pure_bind]
  encaps2_fst _ _ _ := by simp [toIncremental]
-- ANCHOR_END: IncrementalKEMDet_toRandLeak

end IncrementalKEMDet

end KEMScheme
