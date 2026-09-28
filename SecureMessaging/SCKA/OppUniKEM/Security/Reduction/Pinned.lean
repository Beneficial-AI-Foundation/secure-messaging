/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Material

/-!
# KEM primitives with fixed selected-epoch material

**Inputs.** Fix a complete material value `m`, booleans `selectedA` and
`selectedB`, and an optional auxiliary decapsulation result `key`.

**Construction.** Selected key generation returns `m.keygen`; selected
offline and online encapsulation return `m.off` and `m.on`. Each ordinary
sampler returns the output component; each leaking sampler also returns
its stored coins. Other phases use the original KEM samplers. Decapsulation
returns `key`.

**Purpose.** These primitives retain the selected epoch's honest secrets
and key, providing an intermediate execution for comparison with the
simulator's unavailable markers. The factored encapsulation and all three
leakage marginal laws hold by construction.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding.Pinned

variable {K PK SK C : Type}

/-- Key generation uses the stored pair in a selected phase and the
original key-generation sampler in every other phase. -/
def keygen {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak) (selected : Bool) : ProbComp (PK × SK) :=
  if selected then pure m.keygen.1 else base.keygen

/-- Offline encapsulation uses the stored output in a selected phase and
the original offline sampler otherwise. -/
def encapsOff {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak) (selected : Bool) :
    ProbComp (onoff.St × onoff.C₀) :=
  if selected then pure m.off.1 else onoff.encapsOff

/-- Online encapsulation uses the stored ciphertext/key in a selected phase
and the original online sampler on the supplied state and public key otherwise. -/
def encapsOn {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak) (selected : Bool)
    (st : onoff.St) (pk : PK) : ProbComp (onoff.C₁ × K) :=
  if selected then pure m.on.1 else onoff.encapsOn st pk

/-- Honest-state KEM for one intermediate-game query: fixed material in
the selected phases, original sampling elsewhere, and constant auxiliary
decapsulation result `key`. -/
abbrev kem {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak)
    (selectedA selectedB : Bool) (key : Option K) : KEMScheme ProbComp K PK SK C where
  keygen := keygen m selectedA
  encaps pk := do
    let (st, ct0) ← encapsOff m selectedB
    let (ct1, k) ← encapsOn m selectedB st pk
    pure (onoff.split.symm (ct0, ct1), k)
  decaps _ _ := pure key

/-- Constant decapsulation for the intermediate KEM is deterministic. -/
abbrev deterministic {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak)
    (selectedA selectedB : Bool) (key : Option K) :
    (kem m selectedA selectedB key).DeterministicDecaps where
  decapsDet _ _ := key
  decaps_eq _ _ := rfl

/-- The intermediate KEM uses the original ciphertext split and the fixed
or original offline/online samplers selected by `selectedB`. -/
abbrev onOff {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    {leak : base.OnOffRandLeak onoff} (m : Material leak)
    (selectedA selectedB : Bool) (key : Option K) :
    (kem m selectedA selectedB key).OnOffStructure where
  St := onoff.St
  C₀ := onoff.C₀
  C₁ := onoff.C₁
  split := onoff.split
  encapsOff := encapsOff m selectedB
  encapsOn := encapsOn m selectedB
  factor _ := rfl

/-- Leaking variants return the stored output and coins in selected phases
and the original leakage samples otherwise. Forgetting coins yields the
corresponding intermediate KEM sampler for each of the three phases. -/
abbrev leakage {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) (m : Material leak)
    (selectedA selectedB : Bool) (key : Option K) :
    (kem m selectedA selectedB key).OnOffRandLeak (onOff m selectedA selectedB key) where
  KeygenRand := leak.KeygenRand
  OffRand := leak.OffRand
  OnRand := leak.OnRand
  keygenRleak := if selectedA then pure m.keygen else leak.keygenRleak
  encapsOffRleak := if selectedB then pure m.off else leak.encapsOffRleak
  encapsOnRleak st pk := if selectedB then pure m.on else leak.encapsOnRleak st pk
  keygen_fst := by cases selectedA <;> simp [keygen, leak.keygen_fst]
  encapsOff_fst := by cases selectedB <;> simp [encapsOff, leak.encapsOff_fst]
  encapsOn_fst st pk := by cases selectedB <;> simp [encapsOn, leak.encapsOn_fst]

end oppUniKemCKA.Security.Embedding.Pinned
