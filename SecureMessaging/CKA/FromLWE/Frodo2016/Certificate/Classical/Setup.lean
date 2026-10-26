/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Model
import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Classical.Suffix
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

namespace lweCKA.Frodo2016.Certificate

set_option Elab.async false in
section

/-- Semantic initial state for the Classical bridge. -/
def classicalInitial : ℕ :=
  2 ^ 128 * classicalRadix ^ classicalConfig.window

/-- The semantic Classical initial state matches the arithmetic core. -/
theorem classicalInitial_eq_core :
    classicalInitial = Frodo2016.Certificate.Arithmetic.Classical.initial := by
  unfold classicalInitial
    Frodo2016.Certificate.Arithmetic.Classical.initial
  rw [classicalRadix_eq_core]
  rw [show classicalConfig.window = 384 by rfl]

/-- A symbolic semantic recurrence for the Classical bridge. -/
def classicalRun (n x : ℕ) : ℕ :=
  (List.range n).foldl (fun y _ => classicalStep y) x

/-- The symbolic Classical recurrence matches the arithmetic core. -/
theorem classicalRun_eq_core (n x : ℕ) :
    classicalRun n x =
      Frodo2016.Certificate.Arithmetic.Classical.packedRun n x := by
  unfold classicalRun Frodo2016.Certificate.Arithmetic.Classical.packedRun
  rw [classicalStep_eq_core]
  exact Frodo2016.Certificate.Arithmetic.foldl_range_eq_rightIterate _ _ _

/-- Semantic folded recurrence for the Classical bridge. -/
def classicalRunList : ℕ := classicalRun (2 * classicalConfig.n) classicalInitial

set_option exponentiation.threshold 4096 in
/-- The shared semantic recurrence is the named Classical range fold. -/
theorem classicalRun_eq_shared : run classicalConfig = classicalRunList := by
  rfl

/-- The semantic Classical range fold matches the arithmetic core run. -/
theorem classicalRunList_eq_core :
    classicalRunList =
      Frodo2016.Certificate.Arithmetic.Classical.packedRun 1184
        Frodo2016.Certificate.Arithmetic.Classical.initial := by
  unfold classicalRunList
  rw [classicalRun_eq_core, classicalInitial_eq_core]
  rfl


end

end lweCKA.Frodo2016.Certificate

namespace lweCKA.Frodo2016.Certificate

/-- Center of the semantic Classical certificate window. -/
def classicalCenter : ℕ := center classicalConfig

/-- Semantic reversed weight pack for the Classical bridge. -/
def classicalWeightPack : ℕ :=
  weightPack classicalConfig

/-- The semantic Classical weight pack matches the arithmetic core. -/
theorem classicalWeightPack_eq_core :
    classicalWeightPack = Frodo2016.Certificate.Arithmetic.Classical.weightPack := by
  rfl

/-- Semantic endpoint extraction for the Classical bridge. -/
def classicalValuePair (x : ℕ) : ℕ × ℕ :=
  (((x * classicalExtraPack * classicalWeightPack) >>>
      (classicalBits * (2 * classicalCenter))) % classicalRadix,
    2 ^ 128 - x % (classicalRadix - 1))

/-- Semantic Classical extraction matches arithmetic-core extraction. -/
theorem classicalValuePair_eq_core :
    classicalValuePair = Frodo2016.Certificate.Arithmetic.Classical.valuePair := by
  funext x
  unfold classicalValuePair Frodo2016.Certificate.Arithmetic.Classical.valuePair
  rw [classicalExtraPack_eq_core, classicalWeightPack_eq_core, classicalRadix_eq_core]
  rfl

set_option maxRecDepth 65536 in
set_option exponentiation.threshold 4096 in
/-- Unfold the shared Classical certificate into the semantic packed recurrence. -/
theorem classical_certificateValues_eq_runList :
    certificateValues classicalConfig = classicalValuePair classicalRunList := by
  rw [certificateValues_eq_components, classicalRun_eq_shared]
  rfl

end lweCKA.Frodo2016.Certificate

namespace lweCKA.Frodo2016.Certificate

/-- The semantic Classical certificate equals the closed arithmetic recurrence. -/
theorem classical_certificateValues_eq_core :
    certificateValues classicalConfig =
      Frodo2016.Certificate.Arithmetic.Classical.valuePair
        (Frodo2016.Certificate.Arithmetic.Classical.packedRun 1184
          Frodo2016.Certificate.Arithmetic.Classical.initial) := by
  rw [classical_certificateValues_eq_runList, classicalValuePair_eq_core,
    classicalRunList_eq_core]

end lweCKA.Frodo2016.Certificate

/-! # Assembled exact arithmetic for the historical Frodo Classical certificate -/

namespace lweCKA.Frodo2016.Certificate.Arithmetic.Classical

/-- The kernel-checked endpoint for the historical Frodo Classical row. -/
theorem certificateValues_eq :
    valuePair (packedRun 1184 initial) =
      (69032097099755389459452237865466, 2128885962681258) := by
  change valuePair (packedRun (640 + 544) initial) = _
  rw [packedRun_add, packedRun_eq_checkpointPack]
  exact checkpointSuffix_values

end lweCKA.Frodo2016.Certificate.Arithmetic.Classical

/-! # Exact arithmetic certificate for the historical Frodo Classical row -/

namespace lweCKA.Frodo2016.Certificate

/-- The kernel-checked values for the historical Frodo Classical certificate. -/
theorem classical_certificateValues :
    certificateValues classicalConfig =
      (69032097099755389459452237865466, 2128885962681258) :=
  classical_certificateValues_eq_core.trans
    Frodo2016.Certificate.Arithmetic.Classical.certificateValues_eq

end lweCKA.Frodo2016.Certificate
