/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.ArithmeticLemmas

/-! # Low-memory arithmetic base for the historical Frodo Paranoid row -/

namespace lweCKA.Frodo2016.Certificate.Arithmetic.Paranoid

/-- The bit width of each packed coefficient. -/
def bits : ℕ := 161

/-- The radix separating packed coefficients. -/
def radix : ℕ := 2 ^ bits

/-- The specialized historical weight function. -/
def weight (z : ℤ) : ℕ :=
  match z.natAbs with
  | 0 => 19304
  | 1 => 14700
  | 2 => 6490
  | 3 => 1659
  | 4 => 245
  | 5 => 21
  | 6 => 1
  | _ => 0

/-- The product pack in folded semantic form. -/
def semanticProductPack : ℕ :=
  (List.range 13).foldl (fun acc (i : ℕ) =>
    (List.range 13).foldl (fun acc (j : ℕ) =>
      let x := (i : ℤ) - 6
      let y := (j : ℤ) - 6
      acc + weight x * weight y * radix ^ (x * y + 36).toNat) acc) 0

/-- The explicit packed Paranoid product distribution. -/
def productPack : ℕ :=
  2 +
  84 * radix ^ 6 +
  882 * radix ^ 11 +
  980 * radix ^ 12 +
  20580 * radix ^ 16 +
  6636 * radix ^ 18 +
  120050 * radix ^ 20 +
  139356 * radix ^ 21 +
  1651780 * radix ^ 24 +
  545160 * radix ^ 26 +
  5504562 * radix ^ 27 +
  6360200 * radix ^ 28 +
  43126440 * radix ^ 30 +
  1234800 * radix ^ 31 +
  98646200 * radix ^ 32 +
  97549200 * radix ^ 33 +
  381612000 * radix ^ 34 +
  432180000 * radix ^ 35 +
  2157569472 * radix ^ 36 +
  432180000 * radix ^ 37 +
  381612000 * radix ^ 38 +
  97549200 * radix ^ 39 +
  98646200 * radix ^ 40 +
  1234800 * radix ^ 41 +
  43126440 * radix ^ 42 +
  6360200 * radix ^ 44 +
  5504562 * radix ^ 45 +
  545160 * radix ^ 46 +
  1651780 * radix ^ 48 +
  139356 * radix ^ 51 +
  120050 * radix ^ 52 +
  6636 * radix ^ 54 +
  20580 * radix ^ 56 +
  980 * radix ^ 60 +
  882 * radix ^ 61 +
  84 * radix ^ 66 +
  2 * radix ^ 72

/-- The correction pack in folded semantic form. -/
def semanticExtraPack : ℕ :=
  (List.range 13).foldl (fun acc (i : ℕ) =>
    acc + weight ((i : ℤ) - 6) * radix ^ i) 0

/-- The explicit packed Paranoid correction distribution. -/
def extraPack : ℕ :=
  1 +
  21 * radix ^ 1 +
  245 * radix ^ 2 +
  1659 * radix ^ 3 +
  6490 * radix ^ 4 +
  14700 * radix ^ 5 +
  19304 * radix ^ 6 +
  14700 * radix ^ 7 +
  6490 * radix ^ 8 +
  1659 * radix ^ 9 +
  245 * radix ^ 10 +
  21 * radix ^ 11 +
  1 * radix ^ 12

/-- Kernel check of the folded and explicit product packs. -/
theorem semanticProductPack_eq_productPack : semanticProductPack = productPack := by
  rfl

/-- Kernel check of the folded and explicit correction packs. -/
theorem semanticExtraPack_eq_extraPack : semanticExtraPack = extraPack := by
  rfl

/-- Packed unit coefficients for the certificate window. -/
def repunit : ℕ :=
  (List.range 1537).foldl (fun acc _ => acc * radix + 1) 0

/-- Rounding mask for every packed coefficient. -/
def mask : ℕ := (2 ^ 129 - 1) * repunit

/-- Specialized packed recurrence step. -/
def step (x : ℕ) : ℕ :=
  ((x * productPack) >>> (36 * bits + 32)) &&& mask

/-- Right-recursive specialized packed recurrence. -/
def packedRun (n x : ℕ) : ℕ :=
  Frodo2016.Certificate.Arithmetic.rightIterate step n x

/-- Initial packed point mass. -/
def initial : ℕ :=
  2 ^ 128 * radix ^ 768

/-- Center of the packed certificate window. -/
def center : ℕ := 774

/-- Reversed packed weights for endpoint extraction. -/
def weightPack : ℕ :=
  (List.range 1549).foldl (fun acc i =>
    acc * radix + min 1024
      ((if i ≤ center then center - i else i - center) - 512)) 0

/-- Extract the weighted count and missing mass. -/
def valuePair (x : ℕ) : ℕ × ℕ :=
  (((x * extraPack * weightPack) >>> (bits * 1548)) % radix,
    2 ^ 128 - x % (radix - 1))

/-- Split the packed recurrence at an arbitrary boundary. -/
theorem packedRun_add (m n x : ℕ) :
    packedRun (m + n) x = packedRun n (packedRun m x) := by
  exact Frodo2016.Certificate.Arithmetic.rightIterate_add _ _ _ _

end lweCKA.Frodo2016.Certificate.Arithmetic.Paranoid
