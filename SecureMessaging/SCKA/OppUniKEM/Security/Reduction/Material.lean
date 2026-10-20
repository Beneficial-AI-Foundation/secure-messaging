/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Simulator
import ToVCVio.CryptoFoundations.KeyEncapMech.Advantage

/-!
# Fixed branches and stored epoch material

**Setting.** Let `adv` be a security adversary, `q` a send budget, `e` a selected epoch, and
`b : Bool` an IND-CPA challenge bit, with `b = true` for the encapsulated key. For Boolean
computations `G_b`, the *real-minus-random acceptance gap* is
`Pr[G_true = true] - Pr[G_false = true]`.

**Definitions.**

- `fixedBranch adv e b`: KEM key generation and encapsulation of `(ct, k)` under `pk`, followed
  by `run adv e pk ct (if b then k else k')` with an independent uniform key `k'`.
- *Complete material* `m : Material leak`: the outputs and coins of key generation, offline
  encapsulation, and online encapsulation of one epoch. `sampleMaterial leak` samples them with
  the leakage samplers, running online encapsulation at the sampled offline state and public key.
- `Pinned.kem m pinKeygen pinOffline pinOnline key`: the KEM whose flagged phases are *pinned* to
  `m`, returning its stored outputs, while the other phases run the original samplers;
  decapsulation returns `key`.

**Results.**

- `securityReduction_signed_gap_average`: for `q > 0`, the real-minus-random acceptance gap of
  `securityReduction adv q` in the IND-CPA experiment is the average over `e ∈ {1, …, q}` of the
  real-minus-random acceptance gaps of `fixedBranch adv e`.
- `fixedBranch_eq_material`: `fixedBranch adv e b` equals the computation that samples complete
  material `m` and runs the same simulation with the public key, ciphertext, and shared key of
  `m`.
-/

open ToVCVio OracleSpec OracleComp KEMScheme ENNReal

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}
variable [DecidableEq K] [DecidableEq Sym] [SampleableType K]
variable (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
variable (ecEk : ErasureCodePayload PK Sym)
variable (ecCt0 : ErasureCodePayload onoff.C₀ Sym)
variable (ecCt1 : ErasureCodePayload onoff.C₁ Sym) (leak : base.OnOffRandLeak onoff)

/-- Fixed-bit branch of the reduction at selected epoch `e`: sample `(pk, sk) ← keygen` and
`(ct, k) ← encaps pk`, and return `run adv e pk ct k'` with `k' = k` if `b = true` and an
independent uniform key `k'` if `b = false`. -/
def fixedBranch (adv : SecurityAdversary leak Sym) (e : ℕ) (b : Bool) : ProbComp Bool := do
  let (pk, _) ← base.keygen
  let (ct, key) ← base.encaps pk
  let randomKey ← ($ᵗ K : ProbComp K)
  run base onoff ecEk ecCt0 ecCt1 leak adv e pk ct (if b then key else randomKey)

/-- For every send budget `q`, bit `b`, and output `output`, the IND-CPA experiment with bit `b`
for `securityReduction adv q` returns `output` with the probability of
`e ← epochChoice q; fixedBranch adv e b`. -/
theorem securityReduction_probOutput
    (adv : SecurityAdversary leak Sym) (q : ℕ) (b output : Bool) :
    Pr[= output | base.IND_CPA_Exp ProbCompRuntime.probComp
      (securityReduction base onoff ecEk ecCt0 ecCt1 leak adv q) b] =
    Pr[= output | do
      let e ← epochChoice q
      fixedBranch base onoff ecEk ecCt0 ecCt1 leak adv e b] := by
  unfold KEMScheme.IND_CPA_Exp
  rw [probOutput_probCompRuntime_evalDist_eq]
  simp only [securityReduction, fixedBranch, ProbCompRuntime.probComp,
    ProbCompRuntime.liftProbComp, ProbCompLift.id, bind_assoc, pure_bind]
  exact probOutput_bind_bind_swap base.keygen (epochChoice q) _ output

/-- For `q ≠ 0` and every bit `b`, the IND-CPA experiment with bit `b` for
`securityReduction adv q` returns `true` with probability
`q⁻¹ · ∑_{e = 1}^{q} Pr[fixedBranch adv e b = true]`. -/
theorem securityReduction_acceptance_average
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : q ≠ 0) (b : Bool) :
    (Pr[= true | base.IND_CPA_Exp ProbCompRuntime.probComp
      (securityReduction base onoff ecEk ecCt0 ecCt1 leak adv q) b]).toReal =
    (q : ℝ)⁻¹ * ∑ i : Fin q,
      (Pr[= true | fixedBranch base onoff ecEk ecCt0 ecCt1 leak adv (i.val + 1) b]).toReal := by
  rw [securityReduction_probOutput]
  let : NeZero q := ⟨hq⟩
  simp only [epochChoice, hq, ↓reduceDIte, bind_map_left, probOutput_bind_eq_sum_fintype,
    probOutput_uniformSample, Fintype.card_fin, ← Finset.mul_sum]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_sum (fun _ _ => probOutput_ne_top)]

/-- For `q ≠ 0`, the real-minus-random acceptance gap of `securityReduction adv q` in the IND-CPA
experiment is `q⁻¹` times the sum over `e ∈ {1, …, q}` of those of `fixedBranch adv e`. -/
theorem securityReduction_signed_gap_average
    (adv : SecurityAdversary leak Sym) (q : ℕ) (hq : q ≠ 0) :
    (Pr[= true | base.IND_CPA_Exp ProbCompRuntime.probComp
      (securityReduction base onoff ecEk ecCt0 ecCt1 leak adv q) true]).toReal -
    (Pr[= true | base.IND_CPA_Exp ProbCompRuntime.probComp
      (securityReduction base onoff ecEk ecCt0 ecCt1 leak adv q) false]).toReal =
    (q : ℝ)⁻¹ * ∑ i : Fin q,
      ((Pr[= true | fixedBranch base onoff ecEk ecCt0 ecCt1 leak adv
        (i.val + 1) true]).toReal -
       (Pr[= true | fixedBranch base onoff ecEk ecCt0 ecCt1 leak adv
        (i.val + 1) false]).toReal) := by
  rw [securityReduction_acceptance_average base onoff ecEk ecCt0 ecCt1 leak adv q hq true,
    securityReduction_acceptance_average base onoff ecEk ecCt0 ecCt1 leak adv q hq false,
    Finset.sum_sub_distrib, mul_sub]

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- Complete material: the outputs and coins of the three sampling phases of one epoch. -/
structure Material {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) where
  /-- Public/secret key pair and the key-generation coins. -/
  keygen : (PK × SK) × leak.KeygenRand
  /-- Offline encapsulation state/ciphertext and its coins. -/
  off : (onoff.St × onoff.C₀) × leak.OffRand
  /-- Online ciphertext/shared key and its coins. -/
  on : (onoff.C₁ × K) × leak.OnRand

/-- Sample complete material with the leakage samplers; online encapsulation runs at the sampled
offline state and public key. -/
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

/-- For every continuation `f`, the computation `m ← sampleMaterial leak; f pk ct k`, with the
public key, reassembled ciphertext, and shared key of `m`, equals
`(pk, _) ← keygen; (ct, k) ← encaps pk; f pk ct k`. -/
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

/-- For every possible result `m` of `sampleMaterial leak`, `m.keygen` and `m.off` are possible
results of the leaking key generation and offline encapsulation, and `m.on` is a possible result
of leaking online encapsulation at the offline state and public key of `m`. -/
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

/-- The version of `sampleMaterial_support` for the samplers without coins: `base.keygen`,
`onoff.encapsOff`, and `onoff.encapsOn` at the stored offline state and public key. -/
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

/-- For every selected epoch `e` and bit `b`, `fixedBranch adv e b` equals the computation that
samples `m ← sampleMaterial leak` and a uniform key `k'`, and returns
`run adv e pk ct (if b then k else k')` for the public key `pk`, ciphertext `ct`, and shared key
`k` of `m`. -/
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
        (if b then material.on.1.2 else randomKey)) :=
  (sampleMaterial_bind_challenge base onoff leak (fun pk ct key => do
    let randomKey ← ($ᵗ K : ProbComp K)
    run base onoff ecEk ecCt0 ecCt1 leak adv e pk ct (if b then key else randomKey))).symm

end oppUniKemCKA.Security.Embedding

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding.Pinned

variable {K PK SK C : Type}

/-- Key generation pinned to `m`: return the stored key pair if `selected`, and run
`base.keygen` otherwise. -/
def keygen {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak) (selected : Bool) : ProbComp (PK × SK) :=
  if selected then pure m.keygen.1 else base.keygen

/-- Offline encapsulation pinned to `m`: return the stored output if `selected`, and run
`onoff.encapsOff` otherwise. -/
def encapsOff {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak) (selected : Bool) :
    ProbComp (onoff.St × onoff.C₀) :=
  if selected then pure m.off.1 else onoff.encapsOff

/-- Online encapsulation pinned to `m`: return the stored output if `selected`, and run
`onoff.encapsOn st pk` otherwise. -/
def encapsOn {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak) (selected : Bool)
    (st : onoff.St) (pk : PK) : ProbComp (onoff.C₁ × K) :=
  if selected then pure m.on.1 else onoff.encapsOn st pk

/-- KEM whose key generation, offline encapsulation, and online encapsulation return the stored
outputs of `m` when `pinKeygen`, `pinOffline`, and `pinOnline` hold, and use the original
samplers otherwise. Decapsulation returns the constant result `key`. -/
abbrev kem {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak)
    (pinKeygen pinOffline pinOnline : Bool) (key : Option K) :
    KEMScheme ProbComp K PK SK C where
  keygen := keygen m pinKeygen
  encaps pk := do
    let (st, ct0) ← encapsOff m pinOffline
    let (ct1, k) ← encapsOn m pinOnline st pk
    pure (onoff.split.symm (ct0, ct1), k)
  decaps _ _ := pure key

/-- Deterministic-decapsulation witness for `Pinned.kem`: decapsulation returns `key`. -/
abbrev deterministic {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak)
    (pinKeygen pinOffline pinOnline : Bool) (key : Option K) :
    (kem m pinKeygen pinOffline pinOnline key).DeterministicDecaps where
  decapsDet _ _ := key
  decaps_eq _ _ := rfl

/-- On/off structure of `Pinned.kem`: the original ciphertext split with the pinned offline and
online samplers; the factorization holds by definition. -/
abbrev onOff {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak)
    (pinKeygen pinOffline pinOnline : Bool) (key : Option K) :
    (kem m pinKeygen pinOffline pinOnline key).OnOffStructure where
  St := onoff.St
  C₀ := onoff.C₀
  C₁ := onoff.C₁
  split := onoff.split
  encapsOff := encapsOff m pinOffline
  encapsOn := encapsOn m pinOnline
  factor _ := rfl

/-- Leakage witness for `Pinned.kem`: flagged phases return the stored outputs and coins of `m`,
other phases run the samplers of `leak`; discarding coins gives the samplers of `Pinned.kem`. -/
abbrev leakage {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) (m : Material leak)
    (pinKeygen pinOffline pinOnline : Bool) (key : Option K) :
    (kem m pinKeygen pinOffline pinOnline key).OnOffRandLeak
      (onOff m pinKeygen pinOffline pinOnline key) where
  KeygenRand := leak.KeygenRand
  OffRand := leak.OffRand
  OnRand := leak.OnRand
  keygenRleak := if pinKeygen then pure m.keygen else leak.keygenRleak
  encapsOffRleak := if pinOffline then pure m.off else leak.encapsOffRleak
  encapsOnRleak st pk := if pinOnline then pure m.on else leak.encapsOnRleak st pk
  keygen_fst := by cases pinKeygen <;> simp [keygen, leak.keygen_fst]
  encapsOff_fst := by cases pinOffline <;> simp [encapsOff, leak.encapsOff_fst]
  encapsOn_fst st pk := by cases pinOnline <;> simp [encapsOn, leak.encapsOn_fst]

end oppUniKemCKA.Security.Embedding.Pinned
