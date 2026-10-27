/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Model
import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Paranoid.Suffix
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

namespace lweCKA.Frodo2016.Certificate

set_option Elab.async false in
section

/-- Semantic initial state for the Paranoid bridge. -/
def paranoidInitial : ℕ :=
  2 ^ 128 * paranoidRadix ^ paranoidConfig.window

/-- The semantic Paranoid initial state matches the arithmetic core. -/
theorem paranoidInitial_eq_core :
    paranoidInitial = Frodo2016.Certificate.Arithmetic.Paranoid.initial := by
  unfold paranoidInitial
    Frodo2016.Certificate.Arithmetic.Paranoid.initial
  rw [paranoidRadix_eq_core]
  rw [show paranoidConfig.window = 768 by rfl]

/-- A symbolic semantic recurrence for the Paranoid bridge. -/
def paranoidRun (n x : ℕ) : ℕ :=
  (List.range n).foldl (fun y _ => paranoidStep y) x

/-- The symbolic Paranoid recurrence matches the arithmetic core. -/
theorem paranoidRun_eq_core (n x : ℕ) :
    paranoidRun n x =
      Frodo2016.Certificate.Arithmetic.Paranoid.packedRun n x := by
  unfold paranoidRun Frodo2016.Certificate.Arithmetic.Paranoid.packedRun
  rw [paranoidStep_eq_core]
  exact Frodo2016.Certificate.Arithmetic.foldl_range_eq_rightIterate _ _ _

/-- Semantic folded recurrence for the Paranoid bridge. -/
def paranoidRunList : ℕ := paranoidRun (2 * paranoidConfig.n) paranoidInitial

set_option exponentiation.threshold 4096 in
/-- The shared semantic recurrence is the named Paranoid range fold. -/
theorem paranoidRun_eq_shared : run paranoidConfig = paranoidRunList := by
  rfl

/-- The semantic Paranoid range fold matches the arithmetic core run. -/
theorem paranoidRunList_eq_core :
    paranoidRunList =
      Frodo2016.Certificate.Arithmetic.Paranoid.packedRun 1728
        Frodo2016.Certificate.Arithmetic.Paranoid.initial := by
  unfold paranoidRunList
  rw [paranoidRun_eq_core, paranoidInitial_eq_core]
  rfl


end

end lweCKA.Frodo2016.Certificate

namespace lweCKA.Frodo2016.Certificate

/-- Center of the semantic Paranoid certificate window. -/
def paranoidCenter : ℕ := center paranoidConfig

/-- Semantic reversed weight pack for the Paranoid bridge. -/
def paranoidWeightPack : ℕ :=
  weightPack paranoidConfig

/-- Semantic endpoint extraction for the Paranoid bridge. -/
def paranoidValuePair (x : ℕ) : ℕ × ℕ :=
  (((x * paranoidExtraPack * paranoidWeightPack) >>>
      (paranoidBits * (2 * paranoidCenter))) % paranoidRadix,
    2 ^ 128 - x % (paranoidRadix - 1))

/-- The named Paranoid extraction is the shared component tuple. -/
theorem paranoidValuePair_eq_components (x : ℕ) :
    paranoidValuePair x =
      (((x * extraPack paranoidConfig * weightPack paranoidConfig) >>>
          (bits paranoidConfig * (2 * center paranoidConfig))) % radix paranoidConfig,
        2 ^ 128 - x % (radix paranoidConfig - 1)) := by
  simp only [paranoidValuePair, paranoidExtraPack, paranoidWeightPack,
    paranoidBits, paranoidCenter, paranoidRadix]

end lweCKA.Frodo2016.Certificate

namespace lweCKA.Frodo2016.Certificate

/-- The semantic Paranoid weight pack matches the arithmetic core. -/
theorem paranoidWeightPack_eq_core :
    paranoidWeightPack = Frodo2016.Certificate.Arithmetic.Paranoid.weightPack := by
  rfl

/-- Semantic Paranoid extraction matches arithmetic-core extraction. -/
theorem paranoidValuePair_eq_core :
    paranoidValuePair = Frodo2016.Certificate.Arithmetic.Paranoid.valuePair := by
  funext x
  unfold paranoidValuePair Frodo2016.Certificate.Arithmetic.Paranoid.valuePair
  rw [paranoidExtraPack_eq_core, paranoidWeightPack_eq_core, paranoidRadix_eq_core]
  rfl

end lweCKA.Frodo2016.Certificate

namespace lweCKA.Frodo2016.Certificate

/-- Unfold the shared Paranoid certificate into the semantic packed recurrence. -/
theorem paranoid_certificateValues_eq_runList :
    certificateValues paranoidConfig = paranoidValuePair paranoidRunList :=
  (certificateValues_eq_components paranoidConfig).trans
    ((paranoidValuePair_eq_components (run paranoidConfig)).symm.trans
      (congrArg paranoidValuePair paranoidRun_eq_shared))

end lweCKA.Frodo2016.Certificate

namespace lweCKA.Frodo2016.Certificate

/-- The semantic Paranoid certificate equals the closed arithmetic recurrence. -/
theorem paranoid_certificateValues_eq_core :
    certificateValues paranoidConfig =
      Frodo2016.Certificate.Arithmetic.Paranoid.valuePair
        (Frodo2016.Certificate.Arithmetic.Paranoid.packedRun 1728
          Frodo2016.Certificate.Arithmetic.Paranoid.initial) := by
  rw [paranoid_certificateValues_eq_runList, paranoidValuePair_eq_core,
    paranoidRunList_eq_core]

end lweCKA.Frodo2016.Certificate

/-! # Assembled arithmetic for the historical Frodo Paranoid row -/

namespace lweCKA.Frodo2016.Certificate.Arithmetic.Paranoid

/-- Kernel-checked endpoint for the historical Frodo Paranoid row. -/
theorem certificateValues_eq :
    valuePair (packedRun 1728 initial) =
      (6030337663305705867094998372466972, 14272300219351570) := by
  change valuePair (packedRun (896 + 832) initial) = _
  rw [packedRun_add, packedRun_eq_checkpointPack]
  exact checkpointSuffix_values

end lweCKA.Frodo2016.Certificate.Arithmetic.Paranoid

/-! # Exact arithmetic certificate for the historical Frodo Paranoid row -/

namespace lweCKA.Frodo2016.Certificate

/-- The kernel-checked values for the historical Frodo Paranoid certificate. -/
theorem paranoid_certificateValues :
    certificateValues paranoidConfig =
      (6030337663305705867094998372466972, 14272300219351570) :=
  paranoid_certificateValues_eq_core.trans
    Frodo2016.Certificate.Arithmetic.Paranoid.certificateValues_eq

end lweCKA.Frodo2016.Certificate
