/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.HistoricalCertificateArithmeticLemmas

/-!
# Low-memory exact arithmetic for the historical Frodo Classical certificate

This implementation-only module checks one closed packed recurrence without
loading the semantic certificate proof environment.
-/

namespace lweCKA.HistoricalCertificateArithmeticCore

set_option Elab.async false in
section

namespace Classical

/-- The bit width of each packed Classical coefficient. -/
def bits : ℕ := 153

/-- The radix separating packed Classical coefficients. -/
def radix : ℕ := 2 ^ bits

/-- The specialized D2 weight function used by the arithmetic core. -/
def weight (z : ℤ) : ℕ :=
  match z.natAbs with
  | 0 => 1570
  | 1 => 990
  | 2 => 248
  | 3 => 24
  | 4 => 1
  | _ => 0

/-- The product pack in the same folded form as the semantic certificate. -/
def semanticProductPack : ℕ :=
  (List.range 9).foldl (fun acc (i : ℕ) =>
    (List.range 9).foldl (fun acc (j : ℕ) =>
      let x := (i : ℤ) - 4
      let y := (j : ℤ) - 4
      acc + weight x * weight y * radix ^ (x * y + 16).toNat) acc) 0

/-- The explicit packed Classical product distribution. -/
def productPack : ℕ :=
  2 +
  96 * radix ^ 4 +
  1152 * radix ^ 7 +
  992 * radix ^ 8 +
  23808 * radix ^ 10 +
  126968 * radix ^ 12 +
  95040 * radix ^ 13 +
  982080 * radix ^ 14 +
  1960200 * radix ^ 15 +
  10396540 * radix ^ 16 +
  1960200 * radix ^ 17 +
  982080 * radix ^ 18 +
  95040 * radix ^ 19 +
  126968 * radix ^ 20 +
  23808 * radix ^ 22 +
  992 * radix ^ 24 +
  1152 * radix ^ 25 +
  96 * radix ^ 28 +
  2 * radix ^ 32

/-- The folded correction pack matching the semantic certificate. -/
def semanticExtraPack : ℕ :=
  (List.range 9).foldl (fun acc (i : ℕ) =>
    acc + weight ((i : ℤ) - 4) * radix ^ i) 0

/-- The explicit packed Classical correction distribution. -/
def extraPack : ℕ :=
  1 +
  24 * radix ^ 1 +
  248 * radix ^ 2 +
  990 * radix ^ 3 +
  1570 * radix ^ 4 +
  990 * radix ^ 5 +
  248 * radix ^ 6 +
  24 * radix ^ 7 +
  1 * radix ^ 8

/-- Kernel check of the folded and explicit Classical product packs. -/
theorem semanticProductPack_eq_productPack :
    semanticProductPack = productPack := by
  rfl

/-- Kernel check of the folded and explicit Classical correction packs. -/
theorem semanticExtraPack_eq_extraPack : semanticExtraPack = extraPack := by
  rfl

/-- A packed sequence of 769 unit coefficients. -/
def repunit : ℕ :=
  (List.range 769).foldl
    (fun acc _ => acc * radix + 1) 0

/-- The mask that rounds and retains every packed Classical coefficient. -/
def mask : ℕ := (2 ^ 129 - 1) * repunit

/-- The specialized packed recurrence step used by the internal certificate. -/
def step (x : ℕ) : ℕ :=
  ((x * productPack) >>> (16 * bits + 24)) &&& mask

/-- The specialized packed recurrence iterated for `n` steps. -/
def packedRun (n x : ℕ) : ℕ :=
  HistoricalCertificateArithmeticCore.rightIterate step n x

/-- The initial packed point mass for this historical row. -/
def initial : ℕ :=
  2 ^ 128 * radix ^ 384

/-- The center of the packed Classical certificate window. -/
def center : ℕ := 388

/-- The reversed packed weights for the Classical certificate dot product. -/
def weightPack : ℕ :=
  (List.range 777).foldl (fun acc i =>
    acc * radix + min 512
      ((if i ≤ center then center - i else i - center) - 256)) 0

/-- Extract the weighted count and missing mass from a packed state. -/
def valuePair (x : ℕ) : ℕ × ℕ :=
  (((x * extraPack * weightPack) >>> (bits * 776)) % radix,
    2 ^ 128 - x % (radix - 1))

/-- Split a packed recurrence at an arbitrary step boundary. -/
theorem packedRun_add (m n x : ℕ) :
    packedRun (m + n) x = packedRun n (packedRun m x) := by
  exact HistoricalCertificateArithmeticCore.rightIterate_add _ _ _ _

end Classical

end

end lweCKA.HistoricalCertificateArithmeticCore
