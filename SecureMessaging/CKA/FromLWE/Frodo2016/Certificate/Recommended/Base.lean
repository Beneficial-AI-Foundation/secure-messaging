/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.ArithmeticLemmas

/-! # Low-memory arithmetic base for the historical Frodo Recommended row -/

namespace lweCKA.Frodo2016.Certificate.Arithmetic.Recommended

/-- The bit width of each packed coefficient. -/
def bits : ℕ := 153

/-- The radix separating packed coefficients. -/
def radix : ℕ := 2 ^ bits

/-- The specialized historical weight function. -/
def weight (z : ℤ) : ℕ :=
  match z.natAbs with
  | 0 => 1206
  | 1 => 919
  | 2 => 406
  | 3 => 104
  | 4 => 15
  | 5 => 1
  | _ => 0

/-- The product pack in folded semantic form. -/
def semanticProductPack : ℕ :=
  (List.range 11).foldl (fun acc (i : ℕ) =>
    (List.range 11).foldl (fun acc (j : ℕ) =>
      let x := (i : ℤ) - 5
      let y := (j : ℤ) - 5
      acc + weight x * weight y * radix ^ (x * y + 25).toNat) acc) 0

/-- The explicit packed Recommended product distribution. -/
def productPack : ℕ :=
  2 +
  60 * radix ^ 5 +
  450 * radix ^ 9 +
  416 * radix ^ 10 +
  6240 * radix ^ 13 +
  1624 * radix ^ 15 +
  21632 * radix ^ 16 +
  24360 * radix ^ 17 +
  168896 * radix ^ 19 +
  3676 * radix ^ 20 +
  384812 * radix ^ 21 +
  382304 * radix ^ 22 +
  1492456 * radix ^ 23 +
  1689122 * radix ^ 24 +
  8425116 * radix ^ 25 +
  1689122 * radix ^ 26 +
  1492456 * radix ^ 27 +
  382304 * radix ^ 28 +
  384812 * radix ^ 29 +
  3676 * radix ^ 30 +
  168896 * radix ^ 31 +
  24360 * radix ^ 33 +
  21632 * radix ^ 34 +
  1624 * radix ^ 35 +
  6240 * radix ^ 37 +
  416 * radix ^ 40 +
  450 * radix ^ 41 +
  60 * radix ^ 45 +
  2 * radix ^ 50

/-- The correction pack in folded semantic form. -/
def semanticExtraPack : ℕ :=
  (List.range 11).foldl (fun acc (i : ℕ) =>
    acc + weight ((i : ℤ) - 5) * radix ^ i) 0

/-- The explicit packed Recommended correction distribution. -/
def extraPack : ℕ :=
  1 +
  15 * radix ^ 1 +
  104 * radix ^ 2 +
  406 * radix ^ 3 +
  919 * radix ^ 4 +
  1206 * radix ^ 5 +
  919 * radix ^ 6 +
  406 * radix ^ 7 +
  104 * radix ^ 8 +
  15 * radix ^ 9 +
  1 * radix ^ 10

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
  ((x * productPack) >>> (25 * bits + 24)) &&& mask

/-- Right-recursive specialized packed recurrence. -/
def packedRun (n x : ℕ) : ℕ :=
  Frodo2016.Certificate.Arithmetic.rightIterate step n x

/-- Initial packed point mass. -/
def initial : ℕ :=
  2 ^ 128 * radix ^ 768

/-- Center of the packed certificate window. -/
def center : ℕ := 773

/-- Reversed packed weights for endpoint extraction. -/
def weightPack : ℕ :=
  (List.range 1547).foldl (fun acc i =>
    acc * radix + min 1024
      ((if i ≤ center then center - i else i - center) - 512)) 0

/-- Extract the weighted count and missing mass. -/
def valuePair (x : ℕ) : ℕ × ℕ :=
  (((x * extraPack * weightPack) >>> (bits * 1546)) % radix,
    2 ^ 128 - x % (radix - 1))

/-- Split the packed recurrence at an arbitrary boundary. -/
theorem packedRun_add (m n x : ℕ) :
    packedRun (m + n) x = packedRun n (packedRun m x) := by
  exact Frodo2016.Certificate.Arithmetic.rightIterate_add _ _ _ _

end lweCKA.Frodo2016.Certificate.Arithmetic.Recommended
