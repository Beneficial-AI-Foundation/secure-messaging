/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.BadEvent
import SecureMessaging.SCKA.MLKEMBraid.Security.Reduction.KEM
import SecureMessaging.SCKA.MLKEMBraid.Security.Reduction.KDF

/-!
# Compatibility imports for the explicit KEM and KDF reductions

The executable masked simulator is below analytical bad-event bounds. Its correspondence,
installed-sample arguments and primitive-game comparisons are implemented in their respective
modules. This façade retains the historical transitive import interface and supported names.
-/
