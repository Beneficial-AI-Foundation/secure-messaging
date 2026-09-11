/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import ToVCVio.LatticeCrypto.FrodoKEM.Bits
import ToVCVio.LatticeCrypto.FrodoKEM.Parameters

/-!
# FrodoKEM error sampling

`Sample` and `SampleMatrix` follow Sections 6.5 and 6.6 of `[LBES26]` and
Section 3.1 of `[CiC25]`. References are as in `Parameters.lean`.

The three threshold tables are transcribed from Table 5 of `[LBES26]`.
The error probabilities in its Table 4 agree with Table 3 of `[CiC25]`;
Section 3.1 of `[CiC25]` gives their relation to the thresholds. Each
FrodoKEM parameter set shares its table with the corresponding eFrodoKEM set.

For a fixed `table : ErrorTable`, with `lenChi = 16`, the sampling maps are

* `Sample table : Vector Bool lenChi → ℤ`,
  `r ↦ (-1) ^ r[0] * #{i < table.d | table.thresholds[i] < t}`, where
  `t = r[1] * 2^0 + ... + r[15] * 2^14` and bits are read as `0` or `1`;
* `SampleMatrix table rows cols : Vector Bool (rows * cols * lenChi) →
  Matrix (Fin rows) (Fin cols) ℤ`,
  `r ↦ ((i,j) ↦ Sample table (r^(i * cols + j)))`, where `r^(k)` denotes
  input block `k`: its bit `t` is at position `k * lenChi + t` in `r`.

Both maps transform supplied bits; they generate no randomness themselves.
-/

namespace FrodoKEM

/-- The table `Tχ` of Section 6.5 of `[LBES26]`, together with `d`.
For the intended distribution, the support is the integers from `-d` to `d`,
with `2 * d + 1` elements. This structure records the table's length;
it does not impose positivity, increasing thresholds, or a final value. -/
structure ErrorTable where
  /-- Maximum magnitude in the intended error distribution. -/
  d : ℕ
  /-- The comparison values `Tχ(0), ..., Tχ(d)`, derived from cumulative
  probabilities. `Sample` uses only the first `d` entries. -/
  thresholds : Vector ℕ (d + 1)

namespace ParameterSet

/-- The three threshold tables of Table 5 of `[LBES26]`. Each table includes
its final value `32767`, which Section 6.5's sampling loop never reads. -/
def errorTable : ParameterSet → ErrorTable
  | .FrodoKEM640 | .eFrodoKEM640 =>
      { d := 12
        thresholds := #v[4643, 13363, 20579, 25843, 29227, 31145, 32103,
          32525, 32689, 32745, 32762, 32766, 32767] }
  | .FrodoKEM976 | .eFrodoKEM976 =>
      { d := 10
        thresholds := #v[5638, 15915, 23689, 28571, 31116, 32217, 32613,
          32731, 32760, 32766, 32767] }
  | .FrodoKEM1344 | .eFrodoKEM1344 =>
      { d := 6
        thresholds := #v[9142, 23462, 30338, 32361, 32725, 32765, 32767] }

end ParameterSet

/-- `Sample` of Section 6.5 of `[LBES26]` and Algorithm 1 of `[CiC25]`.
Read `t = r[1] * 2^0 + ... + r[15] * 2^14`, count indices `i < table.d`
with `table.thresholds[i] < t`, and negate that count when `r[0]` is true. -/
def Sample (table : ErrorTable) (r : Vector Bool lenChi) : ℤ :=
  let t := Nat.ofBits fun i : Fin (lenChi - 1) => r[i.val + 1]'(by omega)
  let e := (List.finRange table.d).countP fun i =>
    decide (table.thresholds[i.val]'(Nat.lt_succ_of_lt i.isLt) < t)
  if r[0]'(by decide) then -(e : ℤ) else (e : ℤ)

/-- At the 640 table's first threshold `t = 4643`, the result is zero.
The word `9286 = 2 * 4643` places `t` in bits `1` through `15`. -/
example : Sample ParameterSet.FrodoKEM640.errorTable
    (Vector.ofFn fun i => (9286 : ℕ).testBit i.val) = 0 := by decide

/-- The next value `t = 4644` passes the first threshold. -/
example : Sample ParameterSet.FrodoKEM640.errorTable
    (Vector.ofFn fun i => (9288 : ℕ).testBit i.val) = 1 := by decide

/-- With every input bit set, each table gives its largest negative error. -/
example :
    Sample ParameterSet.FrodoKEM640.errorTable (Vector.replicate lenChi true) = -12 ∧
    Sample ParameterSet.FrodoKEM976.errorTable (Vector.replicate lenChi true) = -10 ∧
    Sample ParameterSet.FrodoKEM1344.errorTable (Vector.replicate lenChi true) = -6 := by
  decide

/-- `SampleMatrix` of Section 6.6 of `[LBES26]` and Algorithm 2 of `[CiC25]`.
Entry `(i,j)` is sampled from input block `i * cols + j`. Bit `t` of that
block is at position `(i * cols + j) * lenChi + t` in the input bitstring,
where `0 ≤ i < rows`, `0 ≤ j < cols`, and `0 ≤ t < lenChi`. -/
def SampleMatrix (table : ErrorTable) (rows cols : ℕ)
    (r : Vector Bool (rows * cols * lenChi)) : Matrix (Fin rows) (Fin cols) ℤ :=
  bitsToMatrixWith (Sample table) rows cols r

/-- Six distinct samples check the input-block assignment in a `2`-by-`3`
matrix. Word `words[k]` supplies the bits at positions `k * lenChi + t`.
In particular, block `3` supplies entry `(1,0)`. -/
example :
    let words : Vector ℕ 6 := #v[0, 9288, 9289, 26728, 26729, 65534]
    let r := Vector.ofFn fun k : Fin (2 * 3 * lenChi) =>
      (words[k.val / lenChi]'(by have := k.isLt; simp only [lenChi] at *; omega)).testBit
        (k.val % lenChi)
    SampleMatrix ParameterSet.FrodoKEM640.errorTable 2 3 r =
      Matrix.of ![![(0 : ℤ), 1, -1], ![2, -2, 12]] := by decide

end FrodoKEM
