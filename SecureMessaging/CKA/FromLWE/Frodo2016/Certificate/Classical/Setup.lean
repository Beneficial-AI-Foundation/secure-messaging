/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Model
import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Classical.Base

/-! # Exact arithmetic bridge for the historical Frodo Classical certificate -/

namespace lweCKA.Frodo2016.Certificate

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
    classicalRadix = Frodo2016.Certificate.Arithmetic.Classical.radix := by
  rfl

/-- Semantic folded product pack for the Classical bridge. -/
def classicalProductPack : ℕ :=
  productPack classicalConfig

theorem classicalProductPack_eq_core :
    classicalProductPack = Frodo2016.Certificate.Arithmetic.Classical.productPack := by
  change Frodo2016.Certificate.Arithmetic.Classical.semanticProductPack =
    Frodo2016.Certificate.Arithmetic.Classical.productPack
  exact Frodo2016.Certificate.Arithmetic.Classical.semanticProductPack_eq_productPack

/-- Semantic folded correction pack for the Classical bridge. -/
def classicalExtraPack : ℕ :=
  extraPack classicalConfig

theorem classicalExtraPack_eq_core :
    classicalExtraPack = Frodo2016.Certificate.Arithmetic.Classical.extraPack := by
  change Frodo2016.Certificate.Arithmetic.Classical.semanticExtraPack =
    Frodo2016.Certificate.Arithmetic.Classical.extraPack
  exact Frodo2016.Certificate.Arithmetic.Classical.semanticExtraPack_eq_extraPack

/-- Semantic repunit for the Classical bridge. -/
def classicalRepunit : ℕ :=
  repunit classicalConfig

theorem classicalRepunit_eq_core :
    classicalRepunit = Frodo2016.Certificate.Arithmetic.Classical.repunit := by
  change repunit classicalConfig = Frodo2016.Certificate.Arithmetic.Classical.repunit
  unfold repunit Frodo2016.Certificate.Arithmetic.Classical.repunit
  rfl

/-- Semantic rounding mask for the Classical bridge. -/
def classicalMask : ℕ := mask classicalConfig

theorem classicalMask_eq_core :
    classicalMask = Frodo2016.Certificate.Arithmetic.Classical.mask := by
  change mask classicalConfig = Frodo2016.Certificate.Arithmetic.Classical.mask
  unfold mask Frodo2016.Certificate.Arithmetic.Classical.mask
  rw [show repunit classicalConfig =
    Frodo2016.Certificate.Arithmetic.Classical.repunit by
      exact classicalRepunit_eq_core]

/-- Semantic recurrence step for the Classical bridge. -/
def classicalStep (x : ℕ) : ℕ :=
  step classicalConfig x

set_option maxRecDepth 65536 in
theorem classicalStep_eq_core :
    classicalStep = Frodo2016.Certificate.Arithmetic.Classical.step := by
  change step classicalConfig = Frodo2016.Certificate.Arithmetic.Classical.step
  funext x
  unfold step Frodo2016.Certificate.Arithmetic.Classical.step
  rw [show productPack classicalConfig =
      Frodo2016.Certificate.Arithmetic.Classical.productPack by
        exact classicalProductPack_eq_core,
    show mask classicalConfig = Frodo2016.Certificate.Arithmetic.Classical.mask by
      exact classicalMask_eq_core]
  rfl

end

end lweCKA.Frodo2016.Certificate
