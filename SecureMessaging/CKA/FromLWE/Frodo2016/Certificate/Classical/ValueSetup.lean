/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Classical.RunBridge

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
