/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.CKA.FromLWE.HistoricalCertificateParanoidArithmeticSetup

namespace lweCKA.HistoricalCertificate

set_option Elab.async false in
section

/-- Semantic initial state for the Paranoid bridge. -/
def paranoidInitial : ℕ :=
  2 ^ 128 * paranoidRadix ^ paranoidConfig.window

/-- The semantic Paranoid initial state matches the arithmetic core. -/
theorem paranoidInitial_eq_core :
    paranoidInitial = HistoricalCertificateArithmeticCore.Paranoid.initial := by
  unfold paranoidInitial
    HistoricalCertificateArithmeticCore.Paranoid.initial
  rw [paranoidRadix_eq_core]
  rw [show paranoidConfig.window = 768 by rfl]

/-- A symbolic semantic recurrence for the Paranoid bridge. -/
def paranoidRun (n x : ℕ) : ℕ :=
  (List.range n).foldl (fun y _ => paranoidStep y) x

/-- The symbolic Paranoid recurrence matches the arithmetic core. -/
theorem paranoidRun_eq_core (n x : ℕ) :
    paranoidRun n x =
      HistoricalCertificateArithmeticCore.Paranoid.packedRun n x := by
  unfold paranoidRun HistoricalCertificateArithmeticCore.Paranoid.packedRun
  rw [paranoidStep_eq_core]
  exact HistoricalCertificateArithmeticCore.foldl_range_eq_rightIterate _ _ _

/-- Semantic folded recurrence for the Paranoid bridge. -/
def paranoidRunList : ℕ := paranoidRun (2 * paranoidConfig.n) paranoidInitial

set_option exponentiation.threshold 4096 in
/-- The shared semantic recurrence is the named Paranoid range fold. -/
theorem paranoidRun_eq_shared : run paranoidConfig = paranoidRunList := by
  rfl

/-- The semantic Paranoid range fold matches the arithmetic core run. -/
theorem paranoidRunList_eq_core :
    paranoidRunList =
      HistoricalCertificateArithmeticCore.Paranoid.packedRun 1728
        HistoricalCertificateArithmeticCore.Paranoid.initial := by
  unfold paranoidRunList
  rw [paranoidRun_eq_core, paranoidInitial_eq_core]
  rfl


end

end lweCKA.HistoricalCertificate
