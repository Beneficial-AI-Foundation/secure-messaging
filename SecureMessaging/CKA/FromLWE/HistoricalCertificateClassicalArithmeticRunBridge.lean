/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.HistoricalCertificateClassicalArithmeticSetup

namespace lweCKA.HistoricalCertificate

set_option Elab.async false in
section

/-- Semantic initial state for the Classical bridge. -/
def classicalInitial : ℕ :=
  2 ^ 128 * classicalRadix ^ classicalConfig.window

/-- The semantic Classical initial state matches the arithmetic core. -/
theorem classicalInitial_eq_core :
    classicalInitial = HistoricalCertificateArithmeticCore.Classical.initial := by
  unfold classicalInitial
    HistoricalCertificateArithmeticCore.Classical.initial
  rw [classicalRadix_eq_core]
  rw [show classicalConfig.window = 384 by rfl]

/-- A symbolic semantic recurrence for the Classical bridge. -/
def classicalRun (n x : ℕ) : ℕ :=
  (List.range n).foldl (fun y _ => classicalStep y) x

/-- The symbolic Classical recurrence matches the arithmetic core. -/
theorem classicalRun_eq_core (n x : ℕ) :
    classicalRun n x =
      HistoricalCertificateArithmeticCore.Classical.packedRun n x := by
  unfold classicalRun HistoricalCertificateArithmeticCore.Classical.packedRun
  rw [classicalStep_eq_core]
  exact HistoricalCertificateArithmeticCore.foldl_range_eq_rightIterate _ _ _

/-- Semantic folded recurrence for the Classical bridge. -/
def classicalRunList : ℕ := classicalRun (2 * classicalConfig.n) classicalInitial

set_option exponentiation.threshold 4096 in
/-- The shared semantic recurrence is the named Classical range fold. -/
theorem classicalRun_eq_shared : run classicalConfig = classicalRunList := by
  rfl

/-- The semantic Classical range fold matches the arithmetic core run. -/
theorem classicalRunList_eq_core :
    classicalRunList =
      HistoricalCertificateArithmeticCore.Classical.packedRun 1184
        HistoricalCertificateArithmeticCore.Classical.initial := by
  unfold classicalRunList
  rw [classicalRun_eq_core, classicalInitial_eq_core]
  rfl


end

end lweCKA.HistoricalCertificate
