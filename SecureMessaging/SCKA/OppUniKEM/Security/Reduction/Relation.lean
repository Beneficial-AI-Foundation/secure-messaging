/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.OppUniKEM.Security.Reduction.Simulator

/-!
# Marking honest states for symbolic simulation

**Construction.** For `e : ℕ` and an honest game state `s`, `markState e s`
replaces epoch-e secrets and recorded keys by the unavailable marker `none`.
Other values receive the known marker `some`. Outer options retain absence
and erasure. Public data, message tables, counters, exposure and challenge
sets, and the correctness flag retain their values.

**Results.** For every local state, revelation of its marked form recovers
the original whenever its epoch differs from `e` or its secret is erased.
For every epoch and optional key-table entry, marking preserves `isSome`.

**Proof.** Case analysis on the epoch equality and optional field computes
both operations. These recovery lemmas supply the state comparison for the
pending relational simulation proof, including corruptions after erasure.
-/

namespace oppUniKemCKA.Security.Embedding

variable {K PK SK C Sym : Type}

/-- Mark a value from epoch `t` as unavailable exactly when `t = e`.
Known values are embedded with `some`; this marking is independent of the
key supplied in the IND-CPA challenge. -/
def mark {α : Type} (e t : ℕ) (value : α) : Option α :=
  if t = e then none else some value

/-- Mark A's current secret key according to its epoch, retaining its
absence after erasure and preserving all public fields. -/
def markA {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    (e : ℕ) (s : StA onoff Sym) : StateA (Option SK) PK onoff.C₀ Sym where
  dkA := s.dkA.map (mark e s.t)
  ekA := s.ekA
  ct0 := s.ct0
  t := s.t
  ich := s.ich
  lch := s.lch
  ack := s.ack

/-- Mark B's offline state according to its epoch, preserving ciphertexts,
public key, acknowledgements, chunk buffers, and counters. -/
def markB {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    (e : ℕ) (s : StB onoff Sym) : StateB PK onoff.C₀ onoff.C₁ (Option onoff.St) Sym where
  ekA := s.ekA
  ct0 := s.ct0
  ct1 := s.ct1
  stCt := s.stCt.map (mark e s.t)
  t := s.t
  ich := s.ich
  lch := s.lch
  ack := s.ack

/-- Embed an honest game state into the symbolic state space. Private
material and recorded keys of epoch `e` become unavailable; all other
values, including the message tables and exposure/challenge sets, are retained. -/
def markState {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    (e : ℕ) (s : SCKAScheme.GameState (StA onoff Sym) (StB onoff Sym) K (Message Sym)) :
    SimState onoff Sym where
  stA := markA e s.stA
  stB := markB e s.stB
  keyA t := (s.keyA t).map (mark e t)
  keyB t := (s.keyB t).map (mark e t)
  msgA := s.msgA
  msgB := s.msgB
  nA := s.nA
  nB := s.nB
  tcurA := s.tcurA
  tcurB := s.tcurB
  exposed := s.exposed
  challenged := s.challenged
  correct := s.correct

/-- Recovering a marked optional field succeeds whenever its epoch is not
selected or the original field is absent. These are exactly the cases in
which corruption can recover the original field. -/
theorem revealField_mark {α : Type} (e t : ℕ) (value : Option α)
    (h : t ≠ e ∨ value = none) :
    revealField (value.map (mark e t)) = some value := by
  rcases h with h | rfl
  · cases value <;> simp [mark, h, revealField]
  · rfl

/-- A's marked state can be returned unchanged to the adversary if A is
outside the selected epoch or has already erased its secret key. -/
theorem revealA_markA {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    (e : ℕ) (s : StA onoff Sym) (h : s.t ≠ e ∨ s.dkA = none) :
    revealA (markA e s) = some s := by
  simp only [revealA, markA, revealField_mark e s.t s.dkA h]
  rfl

/-- B's marked state can be returned unchanged to the adversary if B is
outside the selected epoch or has already erased its offline state. -/
theorem revealB_markB {kem : KEMScheme ProbComp K PK SK C} {onoff : kem.OnOffStructure}
    (e : ℕ) (s : StB onoff Sym) (h : s.t ≠ e ∨ s.stCt = none) :
    revealB (markB e s) = some s := by
  simp only [revealB, markB, revealField_mark e s.t s.stCt h]
  rfl

/-- Marking a key-table entry preserves its availability, including in
the selected epoch: an unavailable key is represented by `some none`,
whereas an absent table entry remains `none`. -/
theorem mark_isSome {α : Type} (e t : ℕ) (value : Option α) :
    (value.map (mark e t)).isSome = value.isSome := by
  cases value <;> rfl

/-- Marking every entry of a key table commutes with recording a key at
epoch `t`: the new entry is the marked key for that same epoch. -/
theorem mark_update (e t : ℕ) (table : ℕ → Option K) (k : K) :
    (fun u => (Function.update table t (some k) u).map (mark e u)) =
      Function.update (fun u => (table u).map (mark e u)) t (some (mark e t k)) := by
  funext u
  by_cases h : u = t <;> simp [h, Function.update_of_ne]

/-- For every table and finite list of epochs, marking preserves the
known-prefix test, which reads only whether each key is present. -/
theorem mark_knownPrefix (e : ℕ) (table : ℕ → Option K) (epochs : List ℕ) :
    epochs.all (fun t => t = 0 || ((table t).map (mark e t)).isSome) =
      epochs.all (fun t => t = 0 || (table t).isSome) := by
  simp only [Option.isSome_map]

/-- For every epoch `e` and A-state `s`, revealing its marked state
terminates exactly when corruption exposes `e`; otherwise it returns `s`. -/
theorem revealA_markA_eq {kem : KEMScheme ProbComp K PK SK C}
    {onoff : kem.OnOffStructure} (e : ℕ) (s : StA onoff Sym) :
    revealA (markA e s) = if e ∈ vulnA kem onoff s then none else some s := by
  rcases s with ⟨dk, pk, ct, t, ich, lch, ack⟩
  cases dk <;> by_cases ht : t = e <;>
    simp_all [revealA, revealField, markA, mark, vulnA, eq_comm]

/-- For every epoch `e` and B-state `s`, revealing its marked state
terminates exactly when corruption exposes `e`; otherwise it returns `s`. -/
theorem revealB_markB_eq {kem : KEMScheme ProbComp K PK SK C}
    {onoff : kem.OnOffStructure} (e : ℕ) (s : StB onoff Sym) :
    revealB (markB e s) = if e ∈ vulnB kem onoff s then none else some s := by
  rcases s with ⟨pk, ct0, ct1, st, t, ich, lch, ack⟩
  cases st <;> by_cases ht : t = e <;>
    simp_all [revealB, revealField, markB, mark, vulnB, eq_comm]

/-- Marking preserves A's vulnerable-epoch set, since the outer secret-key
option retains whether the key is present. -/
theorem markA_vulnerable {base : KEMScheme ProbComp K PK SK C}
    {onoff : base.OnOffStructure} (e : ℕ) (s : StA onoff Sym) :
    (if (markA e s).dkA.isSome then {(markA e s).t} else ∅) = vulnA base onoff s := by
  cases h : s.dkA <;> simp [markA, vulnA, h]

/-- Marking preserves B's vulnerable-epoch set, since the outer offline-state
option retains whether the state is present. -/
theorem markB_vulnerable {base : KEMScheme ProbComp K PK SK C}
    {onoff : base.OnOffStructure} (e : ℕ) (s : StB onoff Sym) :
    (if (markB e s).stCt.isSome then {(markB e s).t} else ∅) = vulnB base onoff s := by
  cases h : s.stCt <;> simp [markB, vulnB, h]

end oppUniKemCKA.Security.Embedding
