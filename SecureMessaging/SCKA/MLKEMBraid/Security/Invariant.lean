/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.Invariant.Basic
import SecureMessaging.SCKA.MLKEMBraid.Security.Invariant.Send
import SecureMessaging.SCKA.MLKEMBraid.Security.Invariant.Receive

/-!
# Repaired transcript invariants of the no-authentication trace games

This module collects the repaired transcript invariant and its preservation by sends and
receives. Agreement of the actual decapsulation with the recorded key is a separate condition.
The repaired completion of an epoch follows from the hypotheses of the repaired invariant.
-/
