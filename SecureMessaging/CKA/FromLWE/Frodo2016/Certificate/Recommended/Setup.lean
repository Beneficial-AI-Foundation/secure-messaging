/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Model
import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Recommended.Base

/-! # Exact arithmetic bridge for the historical Frodo Recommended certificate -/

namespace lweCKA.Frodo2016.Certificate

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
    recommendedRadix = Frodo2016.Certificate.Arithmetic.Recommended.radix := by
  rfl

/-- Semantic folded product pack for the Recommended bridge. -/
def recommendedProductPack : ℕ :=
  productPack recommendedConfig

theorem recommendedProductPack_eq_core :
    recommendedProductPack = Frodo2016.Certificate.Arithmetic.Recommended.productPack := by
  change Frodo2016.Certificate.Arithmetic.Recommended.semanticProductPack =
    Frodo2016.Certificate.Arithmetic.Recommended.productPack
  exact Frodo2016.Certificate.Arithmetic.Recommended.semanticProductPack_eq_productPack

/-- Semantic folded correction pack for the Recommended bridge. -/
def recommendedExtraPack : ℕ :=
  extraPack recommendedConfig

theorem recommendedExtraPack_eq_core :
    recommendedExtraPack = Frodo2016.Certificate.Arithmetic.Recommended.extraPack := by
  change Frodo2016.Certificate.Arithmetic.Recommended.semanticExtraPack =
    Frodo2016.Certificate.Arithmetic.Recommended.extraPack
  exact Frodo2016.Certificate.Arithmetic.Recommended.semanticExtraPack_eq_extraPack

/-- Semantic repunit for the Recommended bridge. -/
def recommendedRepunit : ℕ :=
  repunit recommendedConfig

theorem recommendedRepunit_eq_core :
    recommendedRepunit = Frodo2016.Certificate.Arithmetic.Recommended.repunit := by
  change repunit recommendedConfig = Frodo2016.Certificate.Arithmetic.Recommended.repunit
  unfold repunit Frodo2016.Certificate.Arithmetic.Recommended.repunit
  rfl

/-- Semantic rounding mask for the Recommended bridge. -/
def recommendedMask : ℕ := mask recommendedConfig

theorem recommendedMask_eq_core :
    recommendedMask = Frodo2016.Certificate.Arithmetic.Recommended.mask := by
  change mask recommendedConfig = Frodo2016.Certificate.Arithmetic.Recommended.mask
  unfold mask Frodo2016.Certificate.Arithmetic.Recommended.mask
  rw [show repunit recommendedConfig =
    Frodo2016.Certificate.Arithmetic.Recommended.repunit by
      exact recommendedRepunit_eq_core]

/-- Semantic recurrence step for the Recommended bridge. -/
def recommendedStep (x : ℕ) : ℕ :=
  step recommendedConfig x

set_option maxRecDepth 65536 in
theorem recommendedStep_eq_core :
    recommendedStep = Frodo2016.Certificate.Arithmetic.Recommended.step := by
  change step recommendedConfig = Frodo2016.Certificate.Arithmetic.Recommended.step
  funext x
  unfold step Frodo2016.Certificate.Arithmetic.Recommended.step
  rw [show productPack recommendedConfig =
      Frodo2016.Certificate.Arithmetic.Recommended.productPack by
        exact recommendedProductPack_eq_core,
    show mask recommendedConfig = Frodo2016.Certificate.Arithmetic.Recommended.mask by
      exact recommendedMask_eq_core]
  rfl

end

end lweCKA.Frodo2016.Certificate
