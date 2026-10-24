/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Model
import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Paranoid.Base

/-! # Exact arithmetic bridge for the historical Frodo Paranoid certificate -/

namespace lweCKA.Frodo2016.Certificate

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
    paranoidRadix = Frodo2016.Certificate.Arithmetic.Paranoid.radix := by
  rfl

/-- Semantic folded product pack for the Paranoid bridge. -/
def paranoidProductPack : ℕ :=
  productPack paranoidConfig

theorem paranoidProductPack_eq_core :
    paranoidProductPack = Frodo2016.Certificate.Arithmetic.Paranoid.productPack := by
  change Frodo2016.Certificate.Arithmetic.Paranoid.semanticProductPack =
    Frodo2016.Certificate.Arithmetic.Paranoid.productPack
  exact Frodo2016.Certificate.Arithmetic.Paranoid.semanticProductPack_eq_productPack

/-- Semantic folded correction pack for the Paranoid bridge. -/
def paranoidExtraPack : ℕ :=
  extraPack paranoidConfig

theorem paranoidExtraPack_eq_core :
    paranoidExtraPack = Frodo2016.Certificate.Arithmetic.Paranoid.extraPack := by
  change Frodo2016.Certificate.Arithmetic.Paranoid.semanticExtraPack =
    Frodo2016.Certificate.Arithmetic.Paranoid.extraPack
  exact Frodo2016.Certificate.Arithmetic.Paranoid.semanticExtraPack_eq_extraPack

/-- Semantic repunit for the Paranoid bridge. -/
def paranoidRepunit : ℕ :=
  repunit paranoidConfig

theorem paranoidRepunit_eq_core :
    paranoidRepunit = Frodo2016.Certificate.Arithmetic.Paranoid.repunit := by
  change repunit paranoidConfig = Frodo2016.Certificate.Arithmetic.Paranoid.repunit
  unfold repunit Frodo2016.Certificate.Arithmetic.Paranoid.repunit
  rfl

/-- Semantic rounding mask for the Paranoid bridge. -/
def paranoidMask : ℕ := mask paranoidConfig

theorem paranoidMask_eq_core :
    paranoidMask = Frodo2016.Certificate.Arithmetic.Paranoid.mask := by
  change mask paranoidConfig = Frodo2016.Certificate.Arithmetic.Paranoid.mask
  unfold mask Frodo2016.Certificate.Arithmetic.Paranoid.mask
  rw [show repunit paranoidConfig =
    Frodo2016.Certificate.Arithmetic.Paranoid.repunit by
      exact paranoidRepunit_eq_core]

/-- Semantic recurrence step for the Paranoid bridge. -/
def paranoidStep (x : ℕ) : ℕ :=
  step paranoidConfig x

set_option maxRecDepth 65536 in
theorem paranoidStep_eq_core :
    paranoidStep = Frodo2016.Certificate.Arithmetic.Paranoid.step := by
  change step paranoidConfig = Frodo2016.Certificate.Arithmetic.Paranoid.step
  funext x
  unfold step Frodo2016.Certificate.Arithmetic.Paranoid.step
  rw [show productPack paranoidConfig =
      Frodo2016.Certificate.Arithmetic.Paranoid.productPack by
        exact paranoidProductPack_eq_core,
    show mask paranoidConfig = Frodo2016.Certificate.Arithmetic.Paranoid.mask by
      exact paranoidMask_eq_core]
  rfl

end

end lweCKA.Frodo2016.Certificate
