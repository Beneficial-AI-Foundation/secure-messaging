/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Matrix.Basic

/-!
# Matrices as bit strings

`Encoding.lean` and `Packing.lean` both pass between a matrix and a bit vector,
one entry at a time and row by row. They differ in two things: the map between a
single entry and its bits, and how many bits that takes. Both are parameters
here:

* `matrixToBitsWith f`, for `f : α → Vector Bool d`, writes the entries of an
  `r`-by-`c` matrix into a `Vector Bool (r * c * d)`;
* `bitsToMatrixWith g r c`, for `g : Vector Bool d → α`, reads one back. The
  dimensions are explicit: a `Vector Bool (r * c * d)` does not determine them.

|                      | `Encoding.lean`     | `Packing.lean` |
| -------------------- | ------------------- | -------------- |
| `matrixToBitsWith f` | `chunkMatrixToBits` | `Pack`         |
| `bitsToMatrixWith g` | `bitsToChunkMatrix` | `Unpack`       |

## Main definitions

* `matrixToBitsWith`, `bitsToMatrixWith`: the layout and its inverse.

## Main results

* `bitIndex_lt`: bit `t` of entry `(i, j)` lands in range;
* `getElem_matrixToBitsWith`: where the bits of an entry sit.
-/

namespace FrodoKEM

/-- Bit `t` of entry `(i, j)` of an `r`-by-`c` matrix sits at position
`(i * c + j) * d + t` of a bit string of length `r * c * d`, when each entry
takes `d` bits and entries are laid out row by row from row `0`, each row left
to right.
This is the bound the layer below indexes with, at `d = B` for the chunks of
`Encoding.lean` and `d = D` for the packed entries of `Packing.lean`. -/
theorem bitIndex_lt {r c d i j t : ℕ} (hi : i < r) (hj : j < c) (ht : t < d) :
    (i * c + j) * d + t < r * c * d :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left ht _)
    (by rw [← Nat.succ_mul, Nat.mul_comm i c]; gcongr
        exact Nat.mul_add_lt_mul_of_lt_of_lt hi hj)

/-- Concatenate the entries of a matrix, row by row from row `0` and each row
left to right, `f` giving the `d` bits of one entry. -/
def matrixToBitsWith {α : Type*} {r c d : ℕ} (f : α → Vector Bool d)
    (M : Matrix (Fin r) (Fin c) α) : Vector Bool (r * c * d) :=
  (Vector.ofFn fun idx : Fin (r * c) => f (M idx.divNat idx.modNat)).flatten

/-- Read a bit string back as a matrix, `g` giving the entry with the given
`d` bits. -/
def bitsToMatrixWith {α : Type*} {d : ℕ} (g : Vector Bool d → α) (r c : ℕ)
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

end FrodoKEM
