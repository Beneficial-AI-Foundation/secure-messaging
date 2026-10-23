/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.HistoricalCertificate
import SecureMessaging.CKA.FromLWE.HistoricalCertificateParanoidArithmeticBase

/-! # Exact arithmetic bridge for the historical Frodo Paranoid certificate -/

namespace lweCKA.HistoricalCertificate

set_option Elab.async false in
section

/-- The historical Frodo Paranoid certificate parameters. -/
def paranoidConfig : Config :=
  ⟨864, 6, 16, 768,
    512, d4Weight⟩

/-- Internal packed coefficient width for the Paranoid bridge. -/
def paranoidBits : ℕ := bits paranoidConfig

/-- Internal packed radix for the Paranoid bridge. -/
def paranoidRadix : ℕ := radix paranoidConfig

theorem paranoidRadix_eq_core :
    paranoidRadix = HistoricalCertificateArithmeticCore.Paranoid.radix := by
  rfl

/-- Semantic folded product pack for the Paranoid bridge. -/
def paranoidProductPack : ℕ :=
  productPack paranoidConfig

theorem paranoidProductPack_eq_core :
    paranoidProductPack = HistoricalCertificateArithmeticCore.Paranoid.productPack := by
  change HistoricalCertificateArithmeticCore.Paranoid.semanticProductPack =
    HistoricalCertificateArithmeticCore.Paranoid.productPack
  exact HistoricalCertificateArithmeticCore.Paranoid.semanticProductPack_eq_productPack

/-- Semantic folded correction pack for the Paranoid bridge. -/
def paranoidExtraPack : ℕ :=
  extraPack paranoidConfig

theorem paranoidExtraPack_eq_core :
    paranoidExtraPack = HistoricalCertificateArithmeticCore.Paranoid.extraPack := by
  change HistoricalCertificateArithmeticCore.Paranoid.semanticExtraPack =
    HistoricalCertificateArithmeticCore.Paranoid.extraPack
  exact HistoricalCertificateArithmeticCore.Paranoid.semanticExtraPack_eq_extraPack

/-- Semantic repunit for the Paranoid bridge. -/
def paranoidRepunit : ℕ :=
  repunit paranoidConfig

theorem paranoidRepunit_eq_core :
    paranoidRepunit = HistoricalCertificateArithmeticCore.Paranoid.repunit := by
  change repunit paranoidConfig = HistoricalCertificateArithmeticCore.Paranoid.repunit
  unfold repunit HistoricalCertificateArithmeticCore.Paranoid.repunit
  rfl

/-- Semantic rounding mask for the Paranoid bridge. -/
def paranoidMask : ℕ := mask paranoidConfig

theorem paranoidMask_eq_core :
    paranoidMask = HistoricalCertificateArithmeticCore.Paranoid.mask := by
  change mask paranoidConfig = HistoricalCertificateArithmeticCore.Paranoid.mask
  unfold mask HistoricalCertificateArithmeticCore.Paranoid.mask
  rw [show repunit paranoidConfig =
    HistoricalCertificateArithmeticCore.Paranoid.repunit by
      exact paranoidRepunit_eq_core]

/-- Semantic recurrence step for the Paranoid bridge. -/
def paranoidStep (x : ℕ) : ℕ :=
  step paranoidConfig x

set_option maxRecDepth 65536 in
theorem paranoidStep_eq_core :
    paranoidStep = HistoricalCertificateArithmeticCore.Paranoid.step := by
  change step paranoidConfig = HistoricalCertificateArithmeticCore.Paranoid.step
  funext x
  unfold step HistoricalCertificateArithmeticCore.Paranoid.step
  rw [show productPack paranoidConfig =
      HistoricalCertificateArithmeticCore.Paranoid.productPack by
        exact paranoidProductPack_eq_core,
    show mask paranoidConfig = HistoricalCertificateArithmeticCore.Paranoid.mask by
      exact paranoidMask_eq_core]
  rfl

end

end lweCKA.HistoricalCertificate
