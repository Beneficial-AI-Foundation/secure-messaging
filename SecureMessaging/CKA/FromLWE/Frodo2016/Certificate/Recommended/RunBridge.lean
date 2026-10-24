/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.Frodo2016.Certificate.Recommended.Setup

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
