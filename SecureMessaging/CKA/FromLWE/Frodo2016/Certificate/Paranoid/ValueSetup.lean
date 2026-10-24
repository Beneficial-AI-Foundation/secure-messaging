/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Paranoid.WeightSetup

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
