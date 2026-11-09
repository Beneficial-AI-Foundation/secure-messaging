/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Logic.Equiv.Defs

/-!
# Splitting a vector in two

`Vector.splitAt` cuts a vector of length `a + b` into its first `a` entries and its last `b`
entries. `Vector.splitAtEquiv` packages it as an equivalence whose inverse is concatenation.
-/

@[expose] public section

namespace Vector

variable {α : Type*}

/-- Split a vector of length `a + b` into its first `a` entries and its last `b` entries. -/
def splitAt {a b : ℕ} (v : Vector α (a + b)) : Vector α a × Vector α b :=
  (Vector.ofFn fun i : Fin a => v[i.val]'(by omega),
   Vector.ofFn fun i : Fin b => v[a + i.val]'(by omega))

/-- The first part of `splitAt` keeps the entries at the same positions. -/
@[simp]
theorem getElem_splitAt_fst {a b : ℕ} (v : Vector α (a + b)) (i : ℕ) (hi : i < a) :
    (splitAt v).1[i] = v[i]'(by omega) := by
  simp [splitAt]

/-- The second part of `splitAt` shifts each position by `a`. -/
@[simp]
theorem getElem_splitAt_snd {a b : ℕ} (v : Vector α (a + b)) (i : ℕ) (hi : i < b) :
    (splitAt v).2[i] = v[a + i]'(by omega) := by
  simp [splitAt]

/-- `splitAt` inverts concatenation. -/
@[simp]
theorem splitAt_append {a b : ℕ} (x : Vector α a) (y : Vector α b) :
    splitAt (x ++ y) = (x, y) := by
  apply Prod.ext <;> apply Vector.ext <;> intro i hi <;> simp [splitAt]

/-- Concatenating the two parts of `splitAt` gives back the vector. -/
@[simp]
theorem splitAt_fst_append_snd {a b : ℕ} (v : Vector α (a + b)) :
    (splitAt v).1 ++ (splitAt v).2 = v := by
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_append hi]
  split
  · simp
  · simp only [getElem_splitAt_snd]
    congr 1
    omega

/-- `splitAt` as an equivalence, with concatenation as its inverse. -/
def splitAtEquiv (a b : ℕ) : Vector α (a + b) ≃ Vector α a × Vector α b where
  toFun := splitAt
  invFun := fun p => p.1 ++ p.2
  left_inv := splitAt_fst_append_snd
  right_inv := fun p => splitAt_append p.1 p.2

end Vector
