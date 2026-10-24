/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import Mathlib.Data.Nat.Bitwise

/-! # Generic low-memory arithmetic iteration lemmas -/

namespace lweCKA.Frodo2016.Certificate.Arithmetic

/-- Right-recursive iteration of a natural-number endomorphism. -/
def rightIterate (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | n + 1, x => f (rightIterate f n x)

/-- One more right-recursive iteration applies the function last. -/
theorem rightIterate_succ (f : ℕ → ℕ) (n x : ℕ) :
    rightIterate f (n + 1) x = f (rightIterate f n x) := by
  rfl

/-- Split right-recursive iteration at an arbitrary boundary. -/
theorem rightIterate_add (f : ℕ → ℕ) (m n x : ℕ) :
    rightIterate f (m + n) x = rightIterate f n (rightIterate f m x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.add_succ, rightIterate_succ, ih, rightIterate_succ]

/-- A range fold equals right-recursive iteration of the same function. -/
theorem foldl_range_eq_rightIterate (f : ℕ → ℕ) (n x : ℕ) :
    (List.range n).foldl (fun y _ => f y) x = rightIterate f n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, ih]
      rfl

end lweCKA.Frodo2016.Certificate.Arithmetic
