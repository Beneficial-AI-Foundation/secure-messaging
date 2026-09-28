/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Branches

/-!
# Complete selected-epoch material

**Construction.** `Material leak` contains one key-generation output, one
offline output, and one online output, together with their returned coins.
`sampleMaterial` runs these three leakage samplers in that order, supplying
the sampled public key and offline state to the online sampler.

**Statement.** For every continuation depending on the public key,
reassembled ciphertext, and shared key, sampling a complete material value
and running the continuation equals ordinary KEM key generation followed
by encapsulation and the same continuation.

**Proof.** The three coin-forgetting laws remove the unused coins; the
on/off factorization reassembles the encapsulation computation. This
representation supplies honest private material for the simulation proof
while preserving the KEM reduction's observable challenge distribution.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- Outputs and coins for the three selected-epoch phases. `sampleMaterial`
samples the online output at the recorded public key and offline state. -/
structure Material {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) where
  /-- Public/secret key pair and the key-generation coins. -/
  keygen : (PK × SK) × leak.KeygenRand
  /-- Offline encapsulation state/ciphertext and its coins. -/
  off : (onoff.St × onoff.C₀) × leak.OffRand
  /-- Online ciphertext/shared key and its coins. -/
  on : (onoff.C₁ × K) × leak.OnRand

/-- Sample one epoch's complete material using the leakage witnesses;
the online phase receives the sampled offline state and public key. -/
def sampleMaterial {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) : ProbComp (Material leak) := do
  let kg ← leak.keygenRleak
  let off ← leak.encapsOffRleak
  let on ← leak.encapsOnRleak off.1.1 kg.1.1
  pure ⟨kg, off, on⟩

/-- Reassemble the offline and online ciphertext components in a material value. -/
def Material.ciphertext {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak) : C :=
  onoff.split.symm (m.off.1.2, m.on.1.1)

/-- For every result type and continuation `f(pk, ct, k)`, sampling complete
material and discarding its secrets and coins gives the ordinary KEM
key-generation/encapsulation computation followed by `f`. -/
theorem sampleMaterial_bind_challenge
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (leak : base.OnOffRandLeak onoff) {α : Type} (f : PK → C → K → ProbComp α) :
    (do
      let material ← sampleMaterial leak
      f material.keygen.1.1 material.ciphertext material.on.1.2) =
    (do
      let (pk, _) ← base.keygen
      let (ct, key) ← base.encaps pk
      f pk ct key) := by
  rw [← leak.keygen_fst]
  simp only [sampleMaterial, bind_assoc, pure_bind, Material.ciphertext]
  apply bind_congr
  intro kg
  rw [onoff.factor, ← leak.encapsOff_fst]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro off
  rw [← leak.encapsOn_fst]
  simp only [bind_assoc, pure_bind]

/-- Every supported material value consists of supported key-generation
and offline outputs and a supported online output at their public key and
state. These conditions retain the dependence between sampling phases. -/
theorem sampleMaterial_support
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) (m : Material leak)
    (hm : m ∈ support (sampleMaterial leak)) :
    m.keygen ∈ support leak.keygenRleak ∧
    m.off ∈ support leak.encapsOffRleak ∧
    m.on ∈ support (leak.encapsOnRleak m.off.1.1 m.keygen.1.1) := by
  simp only [sampleMaterial, mem_support_bind_iff, mem_support_pure_iff] at hm
  obtain ⟨kg, hkg, off, hoff, on, hon, rfl⟩ := hm
  exact ⟨hkg, hoff, hon⟩

/-- For every supported complete material value, its key pair, offline
output, and online output belong to the corresponding ordinary sampler
supports. The online input is its stored offline state and public key. -/
theorem sampleMaterial_ordinary_support
    {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) (m : Material leak)
    (hm : m ∈ support (sampleMaterial leak)) :
    m.keygen.1 ∈ support base.keygen ∧
    m.off.1 ∈ support onoff.encapsOff ∧
    m.on.1 ∈ support (onoff.encapsOn m.off.1.1 m.keygen.1.1) := by
  obtain ⟨hkg, hoff, hon⟩ := sampleMaterial_support leak m hm
  refine ⟨?_, ?_, ?_⟩
  · rw [← leak.keygen_fst]
    exact (mem_support_bind_iff _ _ _).mpr ⟨_, hkg, by simp⟩
  · rw [← leak.encapsOff_fst]
    exact (mem_support_bind_iff _ _ _).mpr ⟨_, hoff, by simp⟩
  · rw [← leak.encapsOn_fst]
    exact (mem_support_bind_iff _ _ _).mpr ⟨_, hon, by simp⟩

/-- For every selected epoch and KEM branch bit, the reduction's fixed
branch equals a simulation with a complete material sample and a fresh
uniform candidate key. Only the public key, ciphertext, and selected
challenge response are supplied to the simulator. -/
theorem fixedBranch_eq_material
    [DecidableEq K] [DecidableEq Sym] [SampleableType K]
    (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (ecEk : ErasureCodePayload PK Sym)
    (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
    (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)
    (adv : SecurityAdversary leak Sym) (e : ℕ) (b : Bool) :
    fixedBranch base onoff ecEk ecCt0 ecCt1 leak adv e b = (do
      let material ← sampleMaterial leak
      let randomKey ← ($ᵗ K : ProbComp K)
      run base onoff ecEk ecCt0 ecCt1 leak adv e material.keygen.1.1 material.ciphertext
        (if b then material.on.1.2 else randomKey)) := by
  exact (sampleMaterial_bind_challenge base onoff leak (fun pk ct key => do
    let randomKey ← ($ᵗ K : ProbComp K)
    run base onoff ecEk ecCt0 ecCt1 leak adv e pk ct (if b then key else randomKey))).symm

end oppUniKemCKA.Security.Embedding
