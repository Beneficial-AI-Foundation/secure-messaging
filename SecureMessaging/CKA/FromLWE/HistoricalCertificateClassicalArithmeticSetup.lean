/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.HistoricalCertificate
import SecureMessaging.CKA.FromLWE.HistoricalCertificateClassicalArithmeticBase

/-! # Exact arithmetic bridge for the historical Frodo Classical certificate -/

namespace lweCKA.HistoricalCertificate

set_option Elab.async false in
section

/-- The historical Frodo Classical certificate parameters. -/
def classicalConfig : Config :=
  ⟨592, 4, 12, 384,
    256, d2Weight⟩

/-- Internal packed coefficient width for the Classical bridge. -/
def classicalBits : ℕ := bits classicalConfig

/-- Internal packed radix for the Classical bridge. -/
def classicalRadix : ℕ := radix classicalConfig

theorem classicalRadix_eq_core :
    classicalRadix = HistoricalCertificateArithmeticCore.Classical.radix := by
  rfl

/-- Semantic folded product pack for the Classical bridge. -/
def classicalProductPack : ℕ :=
  productPack classicalConfig

theorem classicalProductPack_eq_core :
    classicalProductPack = HistoricalCertificateArithmeticCore.Classical.productPack := by
  change HistoricalCertificateArithmeticCore.Classical.semanticProductPack =
    HistoricalCertificateArithmeticCore.Classical.productPack
  exact HistoricalCertificateArithmeticCore.Classical.semanticProductPack_eq_productPack

/-- Semantic folded correction pack for the Classical bridge. -/
def classicalExtraPack : ℕ :=
  extraPack classicalConfig

theorem classicalExtraPack_eq_core :
    classicalExtraPack = HistoricalCertificateArithmeticCore.Classical.extraPack := by
  change HistoricalCertificateArithmeticCore.Classical.semanticExtraPack =
    HistoricalCertificateArithmeticCore.Classical.extraPack
  exact HistoricalCertificateArithmeticCore.Classical.semanticExtraPack_eq_extraPack

/-- Semantic repunit for the Classical bridge. -/
def classicalRepunit : ℕ :=
  repunit classicalConfig

theorem classicalRepunit_eq_core :
    classicalRepunit = HistoricalCertificateArithmeticCore.Classical.repunit := by
  change repunit classicalConfig = HistoricalCertificateArithmeticCore.Classical.repunit
  unfold repunit HistoricalCertificateArithmeticCore.Classical.repunit
  rfl

/-- Semantic rounding mask for the Classical bridge. -/
def classicalMask : ℕ := mask classicalConfig

theorem classicalMask_eq_core :
    classicalMask = HistoricalCertificateArithmeticCore.Classical.mask := by
  change mask classicalConfig = HistoricalCertificateArithmeticCore.Classical.mask
  unfold mask HistoricalCertificateArithmeticCore.Classical.mask
  rw [show repunit classicalConfig =
    HistoricalCertificateArithmeticCore.Classical.repunit by
      exact classicalRepunit_eq_core]

/-- Semantic recurrence step for the Classical bridge. -/
def classicalStep (x : ℕ) : ℕ :=
  step classicalConfig x

set_option maxRecDepth 65536 in
theorem classicalStep_eq_core :
    classicalStep = HistoricalCertificateArithmeticCore.Classical.step := by
  change step classicalConfig = HistoricalCertificateArithmeticCore.Classical.step
  funext x
  unfold step HistoricalCertificateArithmeticCore.Classical.step
  rw [show productPack classicalConfig =
      HistoricalCertificateArithmeticCore.Classical.productPack by
        exact classicalProductPack_eq_core,
    show mask classicalConfig = HistoricalCertificateArithmeticCore.Classical.mask by
      exact classicalMask_eq_core]
  rfl

end

end lweCKA.HistoricalCertificate
