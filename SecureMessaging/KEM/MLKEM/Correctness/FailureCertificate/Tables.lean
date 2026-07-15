/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.KEM.MLKEM.Correctness.FailureCertificate.Radix

/-!
# Kernel-certified component tables

This file records four small finite tables used by the packed arithmetic proof
and proves that they have the intended values.

The two `convTable*` tables certify the finite measure for a term of
`sᵀ(e₁ + ε_u)`: first add a centered-binomial `CBD₂` encryption-error coefficient to a
`Compress_{d_u}` round-trip error, then count the resulting integer value.

* `convTableTen` is for `d_u = 10`, used by ML-KEM-512 and ML-KEM-768; its
  support is `[-4, 4]`.
* `convTableEleven` is for `d_u = 11`, used by ML-KEM-1024; its support is
  `[-3, 3]`.

The two `ceTable*` tables certify the `v`-component compression error `ε_v`:
they count `Decompress_d(Compress_d x) - x` over all `q = 3329` residues.

* `ceTableFour` is for `d_v = 4`, used by ML-KEM-512 and ML-KEM-768; its
  support is `[-104, 104]`.
* `ceTableFive` is for `d_v = 5`, used by ML-KEM-1024; its support is
  `[-52, 52]`.

These tables feed the packed coefficient-noise measures in
`PackedMeasures.lean`.  The compression-error counts range over all residues,
so the kernel checks are split into bounded blocks and then reassembled.  The
`_spec` and `measurePack_*` theorems establish the table entries by finite
computation.
-/

open LatticeCrypto
open scoped ENNReal

namespace MLKEM

/-- Mass table for `CBD₂ + ε_u` with `d_u = 10`, indexed from support point
`-4 + i`. -/
def convTableTen : ℕ → ℕ
  | 0 => 128 | 1 => 1536 | 2 => 5888 | 3 => 11776 | 4 => 14593
  | 5 => 11780 | 6 => 5894 | 7 => 1540 | _ => 129

/-- Mass table for `CBD₂ + ε_u` with `d_u = 11`, indexed from support point
`-3 + i`. -/
def convTableEleven : ℕ → ℕ
  | 0 => 640 | 1 => 4608 | 2 => 12673 | 3 => 17412 | 4 => 12678
  | 5 => 4612 | _ => 641

theorem convTableTen_spec :
    ∀ i < (9 : ℕ),
      (cbdMeasure 2 * compressionErrorMeasure 10) (-4 + (i : ℤ)) =
        convTableTen i := by
  have hcbd2 : MeasureWindow (cbdMeasure 2) (-2) (-2 + ((5 : ℕ) : ℤ) - 1) := by
    have h : (-2 + ((5 : ℕ) : ℤ) - 1) = (2 : ℤ) := by norm_num
    rw [h]; exact measureWindow_cbdMeasure_two
  intro i hi
  rw [mul_apply_window hcbd2]
  simp only [cbdMeasure, compressionErrorMeasure, enumMeasure_apply]
  interval_cases i <;> decide +kernel

theorem convTableEleven_spec :
    ∀ i < (7 : ℕ),
      (cbdMeasure 2 * compressionErrorMeasure 11) (-3 + (i : ℤ)) =
        convTableEleven i := by
  have hcbd2 : MeasureWindow (cbdMeasure 2) (-2) (-2 + ((5 : ℕ) : ℤ) - 1) := by
    have h : (-2 + ((5 : ℕ) : ℤ) - 1) = (2 : ℤ) := by norm_num
    rw [h]; exact measureWindow_cbdMeasure_two
  intro i hi
  rw [mul_apply_window hcbd2]
  simp only [cbdMeasure, compressionErrorMeasure, enumMeasure_apply]
  interval_cases i <;> decide +kernel

/-- Mass table for the `v`-component compression error with `d_v = 4`, indexed
from support point `-104 + i`. -/
def ceTableFour : ℕ → ℕ
  | 0 => 8 | 208 => 9 | _ => 16

/-- Mass table for the `v`-component compression error with `d_v = 5`, indexed
from support point `-52 + i`. -/
def ceTableFive : ℕ → ℕ
  | 0 => 16 | 104 => 17 | _ => 32

-- The window counts are verified in bounded blocks so each kernel decide over
-- the `3329` residues stays small; the blocks are reassembled below.
private theorem ceTableFour_count_block0 :
    ∀ i < (42 : ℕ),
      (((Finset.range modulus).filter fun x =>
        compressionError 4 x = -104 + (i : ℤ)).card) = ceTableFour i := by
  decide +kernel

private theorem ceTableFour_count_block1 :
    ∀ i < (42 : ℕ),
      (((Finset.range modulus).filter fun x =>
        compressionError 4 x = -104 + ((42 + i : ℕ) : ℤ)).card) = ceTableFour (42 + i) := by
  decide +kernel

private theorem ceTableFour_count_block2 :
    ∀ i < (42 : ℕ),
      (((Finset.range modulus).filter fun x =>
        compressionError 4 x = -104 + ((84 + i : ℕ) : ℤ)).card) = ceTableFour (84 + i) := by
  decide +kernel

private theorem ceTableFour_count_block3 :
    ∀ i < (42 : ℕ),
      (((Finset.range modulus).filter fun x =>
        compressionError 4 x = -104 + ((126 + i : ℕ) : ℤ)).card) = ceTableFour (126 + i) := by
  decide +kernel

private theorem ceTableFour_count_block4 :
    ∀ i < (41 : ℕ),
      (((Finset.range modulus).filter fun x =>
        compressionError 4 x = -104 + ((168 + i : ℕ) : ℤ)).card) = ceTableFour (168 + i) := by
  decide +kernel

private theorem ceTableFour_count :
    ∀ i < (209 : ℕ),
      (((Finset.range modulus).filter fun x =>
        compressionError 4 x = -104 + (i : ℤ)).card) = ceTableFour i := by
  intro i hi
  rcases Nat.lt_or_ge i 42 with h | h
  · exact ceTableFour_count_block0 i h
  rcases Nat.lt_or_ge i 84 with h1 | h1
  · have := ceTableFour_count_block1 (i - 42) (by omega)
    rwa [show 42 + (i - 42) = i by omega] at this
  rcases Nat.lt_or_ge i 126 with h2 | h2
  · have := ceTableFour_count_block2 (i - 84) (by omega)
    rwa [show 84 + (i - 84) = i by omega] at this
  rcases Nat.lt_or_ge i 168 with h3 | h3
  · have := ceTableFour_count_block3 (i - 126) (by omega)
    rwa [show 126 + (i - 126) = i by omega] at this
  · have := ceTableFour_count_block4 (i - 168) (by omega)
    rwa [show 168 + (i - 168) = i by omega] at this

private theorem ceTableFive_count_block0 :
    ∀ i < (35 : ℕ),
      (((Finset.range modulus).filter fun x =>
        compressionError 5 x = -52 + (i : ℤ)).card) = ceTableFive i := by
  decide +kernel

private theorem ceTableFive_count_block1 :
    ∀ i < (35 : ℕ),
      (((Finset.range modulus).filter fun x =>
        compressionError 5 x = -52 + ((35 + i : ℕ) : ℤ)).card) = ceTableFive (35 + i) := by
  decide +kernel

private theorem ceTableFive_count_block2 :
    ∀ i < (35 : ℕ),
      (((Finset.range modulus).filter fun x =>
        compressionError 5 x = -52 + ((70 + i : ℕ) : ℤ)).card) = ceTableFive (70 + i) := by
  decide +kernel

private theorem ceTableFive_count :
    ∀ i < (105 : ℕ),
      (((Finset.range modulus).filter fun x =>
        compressionError 5 x = -52 + (i : ℤ)).card) = ceTableFive i := by
  intro i hi
  rcases Nat.lt_or_ge i 35 with h | h
  · exact ceTableFive_count_block0 i h
  rcases Nat.lt_or_ge i 70 with h1 | h1
  · have := ceTableFive_count_block1 (i - 35) (by omega)
    rwa [show 35 + (i - 35) = i by omega] at this
  · have := ceTableFive_count_block2 (i - 70) (by omega)
    rwa [show 70 + (i - 70) = i by omega] at this

/-- The packing of `compressionErrorMeasure 4` as a window sum weighted by the
`209`-entry mass table `ceTableFour`. -/
theorem measurePack_compressionErrorMeasure_four (R : ℕ) :
    measurePack R (-104) (compressionErrorMeasure 4) =
      ∑ i ∈ Finset.range 209, ceTableFour i * R ^ i := by
  have hw : MeasureWindow (compressionErrorMeasure 4) (-104) (-104 + ((209 : ℕ) : ℤ) - 1) := by
    have h : (-104 + ((209 : ℕ) : ℤ) - 1) = (104 : ℤ) := by norm_num
    rw [h]; exact measureWindow_compressionErrorMeasure_four
  rw [measurePack_eq_range_sum hw]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [compressionErrorMeasure, enumMeasure_apply, ceTableFour_count i (Finset.mem_range.mp hi)]

/-- The packing of `compressionErrorMeasure 5` as a window sum weighted by the
`105`-entry mass table `ceTableFive`. -/
theorem measurePack_compressionErrorMeasure_five (R : ℕ) :
    measurePack R (-52) (compressionErrorMeasure 5) =
      ∑ i ∈ Finset.range 105, ceTableFive i * R ^ i := by
  have hw : MeasureWindow (compressionErrorMeasure 5) (-52) (-52 + ((105 : ℕ) : ℤ) - 1) := by
    have h : (-52 + ((105 : ℕ) : ℤ) - 1) = (52 : ℤ) := by norm_num
    rw [h]; exact measureWindow_compressionErrorMeasure_five
  rw [measurePack_eq_range_sum hw]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [compressionErrorMeasure, enumMeasure_apply, ceTableFive_count i (Finset.mem_range.mp hi)]

end MLKEM
