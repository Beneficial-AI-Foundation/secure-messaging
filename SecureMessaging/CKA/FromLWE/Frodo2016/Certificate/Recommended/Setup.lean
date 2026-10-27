/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Model
import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Recommended.Suffix
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

namespace lweCKA.Frodo2016.Certificate

set_option Elab.async false in
section

/-- Semantic initial state for the Recommended bridge. -/
def recommendedInitial : ℕ :=
  2 ^ 128 * recommendedRadix ^ recommendedConfig.window

/-- The semantic Recommended initial state matches the arithmetic core. -/
theorem recommendedInitial_eq_core :
    recommendedInitial = Frodo2016.Certificate.Arithmetic.Recommended.initial := by
  unfold recommendedInitial
    Frodo2016.Certificate.Arithmetic.Recommended.initial
  rw [recommendedRadix_eq_core]
  rw [show recommendedConfig.window = 768 by rfl]

/-- A symbolic semantic recurrence for the Recommended bridge. -/
def recommendedRun (n x : ℕ) : ℕ :=
  (List.range n).foldl (fun y _ => recommendedStep y) x

/-- The symbolic Recommended recurrence matches the arithmetic core. -/
theorem recommendedRun_eq_core (n x : ℕ) :
    recommendedRun n x =
      Frodo2016.Certificate.Arithmetic.Recommended.packedRun n x := by
  unfold recommendedRun Frodo2016.Certificate.Arithmetic.Recommended.packedRun
  rw [recommendedStep_eq_core]
  exact Frodo2016.Certificate.Arithmetic.foldl_range_eq_rightIterate _ _ _

/-- Semantic folded recurrence for the Recommended bridge. -/
def recommendedRunList : ℕ := recommendedRun (2 * recommendedConfig.n) recommendedInitial

set_option exponentiation.threshold 4096 in
/-- The shared semantic recurrence is the named Recommended range fold. -/
theorem recommendedRun_eq_shared : run recommendedConfig = recommendedRunList := by
  rfl

/-- The semantic Recommended range fold matches the arithmetic core run. -/
theorem recommendedRunList_eq_core :
    recommendedRunList =
      Frodo2016.Certificate.Arithmetic.Recommended.packedRun 1504
        Frodo2016.Certificate.Arithmetic.Recommended.initial := by
  unfold recommendedRunList
  rw [recommendedRun_eq_core, recommendedInitial_eq_core]
  rfl


end

end lweCKA.Frodo2016.Certificate

namespace lweCKA.Frodo2016.Certificate

/-- Center of the semantic Recommended certificate window. -/
def recommendedCenter : ℕ := center recommendedConfig

/-- Semantic reversed weight pack for the Recommended bridge. -/
def recommendedWeightPack : ℕ :=
  weightPack recommendedConfig

/-- The semantic Recommended weight pack matches the arithmetic core. -/
theorem recommendedWeightPack_eq_core :
    recommendedWeightPack = Frodo2016.Certificate.Arithmetic.Recommended.weightPack := by
  rfl

end lweCKA.Frodo2016.Certificate

namespace lweCKA.Frodo2016.Certificate

/-- Semantic endpoint extraction for the Recommended bridge. -/
def recommendedValuePair (x : ℕ) : ℕ × ℕ :=
  (((x * recommendedExtraPack * recommendedWeightPack) >>>
      (recommendedBits * (2 * recommendedCenter))) % recommendedRadix,
    2 ^ 128 - x % (recommendedRadix - 1))

/-- Semantic Recommended extraction matches arithmetic-core extraction. -/
theorem recommendedValuePair_eq_core :
    recommendedValuePair = Frodo2016.Certificate.Arithmetic.Recommended.valuePair := by
  funext x
  unfold recommendedValuePair Frodo2016.Certificate.Arithmetic.Recommended.valuePair
  rw [recommendedExtraPack_eq_core, recommendedWeightPack_eq_core, recommendedRadix_eq_core]
  rfl

end lweCKA.Frodo2016.Certificate

namespace lweCKA.Frodo2016.Certificate

set_option maxRecDepth 65536 in
set_option exponentiation.threshold 4096 in
/-- Unfold the shared Recommended certificate into the semantic packed recurrence. -/
theorem recommended_certificateValues_eq_runList :
    certificateValues recommendedConfig = recommendedValuePair recommendedRunList := by
  rw [certificateValues_eq_components, recommendedRun_eq_shared]
  simp only [recommendedValuePair, recommendedExtraPack, recommendedWeightPack,
    recommendedBits, recommendedCenter, recommendedRadix]

end lweCKA.Frodo2016.Certificate

namespace lweCKA.Frodo2016.Certificate

/-- The semantic Recommended certificate equals the closed arithmetic recurrence. -/
theorem recommended_certificateValues_eq_core :
    certificateValues recommendedConfig =
      Frodo2016.Certificate.Arithmetic.Recommended.valuePair
        (Frodo2016.Certificate.Arithmetic.Recommended.packedRun 1504
          Frodo2016.Certificate.Arithmetic.Recommended.initial) := by
  rw [recommended_certificateValues_eq_runList, recommendedValuePair_eq_core,
    recommendedRunList_eq_core]

end lweCKA.Frodo2016.Certificate

/-! # Assembled arithmetic for the historical Frodo Recommended row -/

namespace lweCKA.Frodo2016.Certificate.Arithmetic.Recommended

/-- Kernel-checked endpoint for the historical Frodo Recommended row. -/
theorem certificateValues_eq :
    valuePair (packedRun 1504 initial) =
      (10543492551966859497706958378128, 8988175038920) := by
  change valuePair (packedRun (768 + 736) initial) = _
  rw [packedRun_add, packedRun_eq_checkpointPack]
  exact checkpointSuffix_values

end lweCKA.Frodo2016.Certificate.Arithmetic.Recommended

/-! # Exact arithmetic certificate for the historical Frodo Recommended row -/

namespace lweCKA.Frodo2016.Certificate

/-- The kernel-checked values for the historical Frodo Recommended certificate. -/
theorem recommended_certificateValues :
    certificateValues recommendedConfig =
      (10543492551966859497706958378128, 8988175038920) :=
  recommended_certificateValues_eq_core.trans
    Frodo2016.Certificate.Arithmetic.Recommended.certificateValues_eq

end lweCKA.Frodo2016.Certificate
