/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Paranoid.RunBridge

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
