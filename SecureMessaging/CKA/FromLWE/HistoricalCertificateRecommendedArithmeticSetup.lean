/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.HistoricalCertificate
import SecureMessaging.CKA.FromLWE.HistoricalCertificateRecommendedArithmeticBase

/-! # Exact arithmetic bridge for the historical Frodo Recommended certificate -/

namespace lweCKA.HistoricalCertificate

set_option Elab.async false in
section

/-- The historical Frodo Recommended certificate parameters. -/
def recommendedConfig : Config :=
  ⟨752, 5, 12, 768,
    512, d3Weight⟩

/-- Internal packed coefficient width for the Recommended bridge. -/
def recommendedBits : ℕ := bits recommendedConfig

/-- Internal packed radix for the Recommended bridge. -/
def recommendedRadix : ℕ := radix recommendedConfig

theorem recommendedRadix_eq_core :
    recommendedRadix = HistoricalCertificateArithmeticCore.Recommended.radix := by
  rfl

/-- Semantic folded product pack for the Recommended bridge. -/
def recommendedProductPack : ℕ :=
  productPack recommendedConfig

theorem recommendedProductPack_eq_core :
    recommendedProductPack = HistoricalCertificateArithmeticCore.Recommended.productPack := by
  change HistoricalCertificateArithmeticCore.Recommended.semanticProductPack =
    HistoricalCertificateArithmeticCore.Recommended.productPack
  exact HistoricalCertificateArithmeticCore.Recommended.semanticProductPack_eq_productPack

/-- Semantic folded correction pack for the Recommended bridge. -/
def recommendedExtraPack : ℕ :=
  extraPack recommendedConfig

theorem recommendedExtraPack_eq_core :
    recommendedExtraPack = HistoricalCertificateArithmeticCore.Recommended.extraPack := by
  change HistoricalCertificateArithmeticCore.Recommended.semanticExtraPack =
    HistoricalCertificateArithmeticCore.Recommended.extraPack
  exact HistoricalCertificateArithmeticCore.Recommended.semanticExtraPack_eq_extraPack

/-- Semantic repunit for the Recommended bridge. -/
def recommendedRepunit : ℕ :=
  repunit recommendedConfig

theorem recommendedRepunit_eq_core :
    recommendedRepunit = HistoricalCertificateArithmeticCore.Recommended.repunit := by
  change repunit recommendedConfig = HistoricalCertificateArithmeticCore.Recommended.repunit
  unfold repunit HistoricalCertificateArithmeticCore.Recommended.repunit
  rfl

/-- Semantic rounding mask for the Recommended bridge. -/
def recommendedMask : ℕ := mask recommendedConfig

theorem recommendedMask_eq_core :
    recommendedMask = HistoricalCertificateArithmeticCore.Recommended.mask := by
  change mask recommendedConfig = HistoricalCertificateArithmeticCore.Recommended.mask
  unfold mask HistoricalCertificateArithmeticCore.Recommended.mask
  rw [show repunit recommendedConfig =
    HistoricalCertificateArithmeticCore.Recommended.repunit by
      exact recommendedRepunit_eq_core]

/-- Semantic recurrence step for the Recommended bridge. -/
def recommendedStep (x : ℕ) : ℕ :=
  step recommendedConfig x

set_option maxRecDepth 65536 in
theorem recommendedStep_eq_core :
    recommendedStep = HistoricalCertificateArithmeticCore.Recommended.step := by
  change step recommendedConfig = HistoricalCertificateArithmeticCore.Recommended.step
  funext x
  unfold step HistoricalCertificateArithmeticCore.Recommended.step
  rw [show productPack recommendedConfig =
      HistoricalCertificateArithmeticCore.Recommended.productPack by
        exact recommendedProductPack_eq_core,
    show mask recommendedConfig = HistoricalCertificateArithmeticCore.Recommended.mask by
      exact recommendedMask_eq_core]
  rfl

end

end lweCKA.HistoricalCertificate
