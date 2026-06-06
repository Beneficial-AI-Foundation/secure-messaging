/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SecureMessaging.CKA.FromDDH.Construction

/-!
# CKA from DDH — Common Results for Correctness and Security
-/

open OracleSpec OracleComp ENNReal
open CKAScheme

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]

namespace ddhCKA

/-- **Epoch counter invariant**

At every reachable state, the per-party epoch counters `tA`, `tB` differ by
at most 1:

  * `lastAction ∈ {none, recvA, recvB}`  ⟹  `tA = tB`      (synchronized)
  * `lastAction ∈ {sendA, challA}`       ⟹  `tA = tB + 1`  (A's send pending recvB)
  * `lastAction ∈ {sendB, challB}`       ⟹  `tB = tA + 1`  (B's send pending recvA)
-/
def epochCounterInv (s : GameState (F ⊕ G) G G) : Prop :=
  match s.lastAction with
  | none | some .recvA | some .recvB => s.tA = s.tB
  | some .sendA | some .challA => s.tA = s.tB + 1
  | some .sendB | some .challB => s.tB = s.tA + 1

/-- **State shape invariant**

Every reachable state has one of four phases:
  1. ready for A to send;
  2. A → B in transmission;
  3. ready for B to send;
  4. B → A in transmission.

In each phase, `(stA, stB, ρA, ρB, keyA, keyB)` has the shape below
(with `x, y : F` and `⊥` for `none`):

 # | `lastAction`        | `stA`    | `stB`    | `ρA`    | `ρB`    | `keyA`       | `keyB`     |
 --|---------------------|----------|----------|---------|---------|--------------|------------|
 1 | `none`, `recvA`     | `x•gen`  | `x`      | `⊥`     | `⊥`     | `⊥`          | `⊥`       |
 2 | `sendA`, `challA`   | `y`      | `x`      | `y•gen` | `⊥`     | `y•(x•gen)`  | `⊥`        |
 3 | `recvB`             | `y`      | `y•gen`  | `⊥`     | `⊥`     | `⊥`          | `⊥`       |
 4 | `sendB`, `challB`   | `y`      | `x`      | `⊥`     | `x•gen` | `⊥`          | `x•(y•gen)`|
-/
def stateShapeInv (gen : G) (s : GameState (F ⊕ G) G G) : Prop :=
  match s.lastAction with
  | none | some .recvA =>
    ∃ x : F, s.stA = .inr (x • gen) ∧ s.stB = .inl x ∧
      s.rhoA = none ∧ s.rhoB = none ∧ s.keyA = none ∧ s.keyB = none
  | some .sendA | some .challA =>
    ∃ x y : F, s.stA = .inl y ∧ s.stB = .inl x ∧
      s.rhoA = some (y • gen) ∧ s.rhoB = none ∧
      s.keyA = some (y • (x • gen)) ∧ s.keyB = none
  | some .recvB =>
    ∃ y : F, s.stA = .inl y ∧ s.stB = .inr (y • gen) ∧
      s.rhoA = none ∧ s.rhoB = none ∧ s.keyA = none ∧ s.keyB = none
  | some .sendB | some .challB =>
    ∃ x y : F, s.stA = .inl y ∧ s.stB = .inl x ∧
      s.rhoA = none ∧ s.rhoB = some (x • gen) ∧
      s.keyA = none ∧ s.keyB = some (x • (y • gen))

/-- **Reachable shape invariant**: `epochCounterInv s ∧ stateShapeInv gen s`.

* Epoch counter invariant — `tA, tB` are aligned depending on `s.lastAction`:

 `lastAction`                | constraint
 ----------------------------|---------------
 `none`, `recvA`, `recvB`    | `tA = tB`
 `sendA`, `challA`           | `tA = tB + 1`
 `sendB`, `challB`           | `tB = tA + 1`

* State shape invariant — `(stA, stB, ρA, ρB, keyA, keyB)` is in one of four
  DH-compatible shapes depending on `s.lastAction`:

 # | `lastAction`        | `stA`    | `stB`    | `ρA`    | `ρB`    | `keyA`       | `keyB`     |
 --|---------------------|----------|----------|---------|---------|--------------|------------|
 1 | `none`, `recvA`     | `x•gen`  | `x`      | `⊥`     | `⊥`     | `⊥`          | `⊥`       |
 2 | `sendA`, `challA`   | `y`      | `x`      | `y•gen` | `⊥`     | `y•(x•gen)`  | `⊥`        |
 3 | `recvB`             | `y`      | `y•gen`  | `⊥`     | `⊥`     | `⊥`          | `⊥`       |
 4 | `sendB`, `challB`   | `y`      | `x`      | `⊥`     | `x•gen` | `⊥`          | `x•(y•gen)`|
-/
def reachableShape (gen : G) (s : GameState (F ⊕ G) G G) : Prop :=
  epochCounterInv s ∧ stateShapeInv gen s

/-- **Reachable-state invariant** `reachableInv gen s`:
`epochCounterInv s ∧ s.correct = true ∧ stateShapeInv gen s`.

* `epochCounterInv s` — epoch counters are aligned;
* `s.correct = true` — every receive so far matched the sender's stored key;
* `stateShapeInv gen s` — state is in one of four DH-compatible shapes.

Maintained by every oracle call along reachable traces. -/
def reachableInv (gen : G) (s : GameState (F ⊕ G) G G) : Prop :=
  epochCounterInv s ∧
  s.correct = true ∧
  stateShapeInv gen s

end ddhCKA
