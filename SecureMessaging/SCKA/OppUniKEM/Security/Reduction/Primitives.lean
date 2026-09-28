/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Basic

/-!
# Selected-epoch KEM primitives

**Inputs.** Fix a KEM with on/off and leakage witnesses, an IND-CPA public
key `pkStar`, ciphertext `ctStar`, and Booleans selecting each party's epoch.

**Construction.** The selected key-generation and offline phases return
`pkStar` and the first component of `ctStar`; selected online encapsulation
returns its second component. Their secrets, honest key, and coins use the
unavailable marker `none`. Other phases use the original samplers and mark
known results as `some x`. Auxiliary decapsulation returns B's symbolic key.

**Representation.** Protocol absence uses an outer option: `none` means
erased, `some none` means present but unavailable, and `some (some x)` means
present and known. The factored samplers and leaking variants satisfy their
marginal laws by construction and the original leakage witness.

`Simulator` uses these primitives for protocol queries and uses the IND-CPA
challenge key for the selected epoch's challenge response.
-/

open OracleSpec OracleComp KEMScheme

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C : Type}

/-- Key generation for a simulator query. When `selected = true`, return
`pkStar` with an unavailable secret; otherwise sample an honest key pair
and mark its secret as known. -/
def keygen (kem : KEMScheme ProbComp K PK SK C) (selected : Bool) (pkStar : PK) :
    ProbComp (PK × Option SK) :=
  if selected then pure (pkStar, none) else Prod.map id some <$> kem.keygen

/-- Offline encapsulation for a simulator query. In the selected epoch,
return the offline component of `ctStar` with unavailable offline state;
otherwise sample the original offline algorithm. -/
def encapsOff {kem : KEMScheme ProbComp K PK SK C} (onoff : kem.OnOffStructure)
    (selected : Bool) (ctStar : C) : ProbComp (Option onoff.St × onoff.C₀) :=
  if selected then pure (none, (onoff.split ctStar).1)
  else Prod.map some id <$> onoff.encapsOff

/-- Online encapsulation uses the original algorithm for known offline
state. Unavailable state denotes the selected epoch: return `ctStar`'s
online component and mark its honest encapsulated key as unavailable. -/
def encapsOn {kem : KEMScheme ProbComp K PK SK C} (onoff : kem.OnOffStructure)
    (ctStar : C) (st : Option onoff.St) (pk : PK) : ProbComp (onoff.C₁ × Option K) :=
  match st with
  | none => pure ((onoff.split ctStar).2, none)
  | some st => Prod.map id some <$> onoff.encapsOn st pk

/-- KEM used for one simulator query. `selectedA` and `selectedB` identify
whether each role is in the selected epoch. `key` is B's recorded symbolic
key for A's current epoch and is used for auxiliary decapsulation. -/
abbrev kem (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (selectedA selectedB : Bool) (pkStar : PK) (ctStar : C) (key : Option (Option K)) :
    KEMScheme ProbComp (Option K) PK (Option SK) C where
  keygen := keygen base selectedA pkStar
  encaps pk := do
    let (st, ct0) ← encapsOff onoff selectedB ctStar
    let (ct1, key) ← encapsOn onoff ctStar st pk
    pure (onoff.split.symm (ct0, ct1), key)
  decaps _ _ := pure key

/-- The simulator's constant decapsulation is deterministic and returns
its supplied auxiliary key `key`, including an unavailable selected key. -/
abbrev deterministic (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (selectedA selectedB : Bool) (pkStar : PK) (ctStar : C) (key : Option (Option K)) :
    (kem base onoff selectedA selectedB pkStar ctStar key).DeterministicDecaps where
  decapsDet _ _ := key
  decaps_eq _ _ := rfl

/-- The simulator retains the original ciphertext split and marks its
offline state as known or unavailable. Its encapsulation factors into the
simulator's offline and online algorithms by construction. -/
abbrev onOff (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (selectedA selectedB : Bool) (pkStar : PK) (ctStar : C) (key : Option (Option K)) :
    (kem base onoff selectedA selectedB pkStar ctStar key).OnOffStructure where
  St := Option onoff.St
  C₀ := onoff.C₀
  C₁ := onoff.C₁
  split := onoff.split
  encapsOff := encapsOff onoff selectedB ctStar
  encapsOn := encapsOn onoff ctStar
  factor _ := rfl

/-- Leaking key generation returns unavailable coins in the selected epoch
and the original leakage sample, with known secret and coins, otherwise. -/
def keygenLeak {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) (selected : Bool) (pkStar : PK) :
    ProbComp ((PK × Option SK) × Option leak.KeygenRand) :=
  if selected then pure ((pkStar, none), none)
  else (fun z => ((z.1.1, some z.1.2), some z.2)) <$> leak.keygenRleak

/-- Leaking offline encapsulation returns unavailable state and coins in
the selected epoch; all other epochs use the original leakage algorithm. -/
def offLeak {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) (selected : Bool) (ctStar : C) :
    ProbComp ((Option onoff.St × onoff.C₀) × Option leak.OffRand) :=
  if selected then pure ((none, (onoff.split ctStar).1), none)
  else (fun z => ((some z.1.1, z.1.2), some z.2)) <$> leak.encapsOffRleak

/-- Leaking online encapsulation returns unavailable key and coins for the
selected offline state; known states use the original leakage algorithm. -/
def onLeak {base : KEMScheme ProbComp K PK SK C} {onoff : base.OnOffStructure}
    (leak : base.OnOffRandLeak onoff) (ctStar : C) (st : Option onoff.St) (pk : PK) :
    ProbComp ((onoff.C₁ × Option K) × Option leak.OnRand) :=
  match st with
  | none => pure (((onoff.split ctStar).2, none), none)
  | some st => (fun z => ((z.1.1, some z.1.2), some z.2)) <$> leak.encapsOnRleak st pk

/-- Simulator leakage witnesses. Forgetting the marked coins recovers
each ordinary simulator algorithm, by the original leakage marginal laws. -/
abbrev leakage (base : KEMScheme ProbComp K PK SK C) (onoff : base.OnOffStructure)
    (leak : base.OnOffRandLeak onoff)
    (selectedA selectedB : Bool) (pkStar : PK) (ctStar : C) (key : Option (Option K)) :
    (kem base onoff selectedA selectedB pkStar ctStar key).OnOffRandLeak
      (onOff base onoff selectedA selectedB pkStar ctStar key) where
  KeygenRand := Option leak.KeygenRand
  OffRand := Option leak.OffRand
  OnRand := Option leak.OnRand
  keygenRleak := keygenLeak leak selectedA pkStar
  encapsOffRleak := offLeak leak selectedB ctStar
  encapsOnRleak := onLeak leak ctStar
  keygen_fst := by
    cases selectedA
    · change (do let z ← keygenLeak leak false pkStar; pure z.1) = keygen base false pkStar
      simp only [keygenLeak, keygen, Bool.false_eq_true, ↓reduceIte, bind_map_left]
      rw [← leak.keygen_fst]
      simp [map_eq_bind_pure_comp, bind_assoc, Prod.map, id]
    · simp [keygenLeak, keygen]
  encapsOff_fst := by
    cases selectedB
    · change (do let z ← offLeak leak false ctStar; pure z.1) = encapsOff onoff false ctStar
      simp only [offLeak, encapsOff, Bool.false_eq_true, ↓reduceIte, bind_map_left]
      rw [← leak.encapsOff_fst]
      simp [map_eq_bind_pure_comp, bind_assoc, Prod.map, id]
    · simp [offLeak, encapsOff]
  encapsOn_fst st pk := by
    cases st with
    | none => simp [onLeak, encapsOn]
    | some st =>
      change (do let z ← onLeak leak ctStar (some st) pk; pure z.1) =
        encapsOn onoff ctStar (some st) pk
      simp only [onLeak, encapsOn, bind_map_left]
      rw [← leak.encapsOn_fst st pk]
      simp [map_eq_bind_pure_comp, bind_assoc, Prod.map, id]

end oppUniKemCKA.Security.Embedding
