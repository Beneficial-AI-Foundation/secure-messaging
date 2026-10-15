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

This compatibility import exposes the invariant, its send and receive preservation arguments,
and the shared joint sampling facts. Actual decapsulation agreement remains a separate condition;
repaired completion is proved from the repaired invariant's own hypotheses.
-/
