/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Matrix.Basic

/-!
# Matrices as bit strings

`Frodo.Encode` and `Frodo.Pack` both cut a matrix into one bit block per entry,
laid out row by row, differing only in the codec on a single entry and in the
width of a block. This file is that layout, with both left as parameters:

* `matrixToBitsWith f`, for `f : α → Vector Bool d`, writes the entries of an
  `r`-by-`c` matrix into a `Vector Bool (r * c * d)`;
* `bitsToMatrixWith g` reads one back.

`Encoding.lean` instantiates them at `d = B` and `Packing.lean` at `d = D`, each
stating its own definition as its section of the specification does and bridging
to these by `rfl`, so that the index lemma and the two round trips are proved
once here rather than in both files.

## Main definitions

* `matrixToBitsWith`, `bitsToMatrixWith`: the layout and its inverse.

## Main results

* `bitIndex_lt`: bit `t` of entry `(i, j)` lands in range;
* `getElem_matrixToBitsWith`: where the bits of an entry sit;
* `bitsToMatrixWith_matrixToBitsWith`, `matrixToBitsWith_bitsToMatrixWith`: the
  layer is a round trip whenever the codec on one entry is.
-/

namespace FrodoKEM

/-- Bit `t` of entry `(i, j)` of an `r`-by-`c` matrix sits at position
`(i * c + j) * d + t` of a bit string of length `r * c * d`, when each entry
takes `d` bits and entries are laid out row by row. This is the bound the
layer below indexes with, at `d = B` for the chunks of `Encoding.lean` and
`d = D` for the packed entries of `Packing.lean`. -/
theorem bitIndex_lt {r c d i j t : ℕ} (hi : i < r) (hj : j < c) (ht : t < d) :
    (i * c + j) * d + t < r * c * d :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left ht _)
    (by rw [← Nat.succ_mul, Nat.mul_comm i c]; gcongr
        exact Nat.mul_add_lt_mul_of_lt_of_lt hi hj)

/-- Lay the entries of a matrix out as bit blocks of width `d`, row by row and
each row left to right, `f` giving the `d` bits of one entry. -/
def matrixToBitsWith {α : Type*} {r c d : ℕ} (f : α → Vector Bool d)
    (M : Matrix (Fin r) (Fin c) α) : Vector Bool (r * c * d) :=
  (Vector.ofFn fun idx : Fin (r * c) => f (M idx.divNat idx.modNat)).flatten

/-- Read a bit string back as a matrix, `g` giving the entry with the given
`d` bits. -/
def bitsToMatrixWith {α : Type*} {r c d : ℕ} (g : Vector Bool d → α)
    (b : Vector Bool (r * c * d)) : Matrix (Fin r) (Fin c) α :=
  Matrix.of fun i j => g (Vector.ofFn fun l =>
    b[(i.val * c + j.val) * d + l.val]'(bitIndex_lt i.isLt j.isLt l.isLt))

/-- The bits of entry `(i, j)` sit at positions `(i * c + j) * d` onwards. -/
theorem getElem_matrixToBitsWith {α : Type*} {r c d : ℕ} (f : α → Vector Bool d)
    (M : Matrix (Fin r) (Fin c) α) {i j l : ℕ} (hi : i < r) (hj : j < c) (hl : l < d) :
    (matrixToBitsWith f M)[(i * c + j) * d + l]'(bitIndex_lt hi hj hl) =
      (f (M ⟨i, hi⟩ ⟨j, hj⟩))[l] := by
  rw [matrixToBitsWith, Vector.getElem_flatten]
  simp only [Nat.mul_comm (i * c + j) d, Nat.mul_add_div (by omega : 0 < d),
    Nat.mul_add_mod, Nat.div_eq_of_lt hl, Nat.mod_eq_of_lt hl, Nat.add_zero,
    Vector.getElem_ofFn]
  congr 3 <;> simp only [Fin.divNat, Fin.modNat, Nat.mul_comm i c,
    Nat.mul_add_div (by omega : 0 < c), Nat.mul_add_mod, Nat.div_eq_of_lt hj,
    Nat.mod_eq_of_lt hj, Nat.add_zero]

/-- A matrix is recovered from its bit string, whenever an entry is recovered
from its own bits. -/
theorem bitsToMatrixWith_matrixToBitsWith {α : Type*} {r c d : ℕ}
    {f : α → Vector Bool d} {g : Vector Bool d → α} (hgf : ∀ x, g (f x) = x)
    (M : Matrix (Fin r) (Fin c) α) :
    bitsToMatrixWith g (matrixToBitsWith f M) = M := by
  ext i j
  simp only [bitsToMatrixWith, Matrix.of_apply]
  rw [← hgf (M i j)]
  congr 1
  apply Vector.ext
  intro l hl
  rw [Vector.getElem_ofFn]
  exact getElem_matrixToBitsWith f M i.isLt j.isLt hl

/-- A bit string is recovered from its matrix, whenever the bits of an entry
are recovered from the entry. -/
theorem matrixToBitsWith_bitsToMatrixWith {α : Type*} {r c d : ℕ}
    {f : α → Vector Bool d} {g : Vector Bool d → α} (hfg : ∀ v, f (g v) = v)
    (b : Vector Bool (r * c * d)) :
    matrixToBitsWith f (bitsToMatrixWith g b) = b := by
  apply Vector.ext
  intro k hk
  obtain ⟨i, j, l, hi, hj, hl, rfl⟩ :
      ∃ i j l, i < r ∧ j < c ∧ l < d ∧ k = (i * c + j) * d + l :=
    ⟨k / d / c, k / d % c, k % d,
      Nat.div_lt_of_lt_mul (Nat.div_lt_of_lt_mul
        (by rw [Nat.mul_comm d (c * r), Nat.mul_comm c r]; exact hk)),
      Nat.mod_lt _ (Nat.pos_of_ne_zero fun h => absurd hk (by simp [h])),
      Nat.mod_lt _ (Nat.pos_of_ne_zero fun h => absurd hk (by simp [h])),
      by rw [Nat.div_add_mod', Nat.div_add_mod']⟩
  rw [getElem_matrixToBitsWith _ _ hi hj hl]
  simp only [bitsToMatrixWith, Matrix.of_apply, hfg, Vector.getElem_ofFn]

end FrodoKEM
