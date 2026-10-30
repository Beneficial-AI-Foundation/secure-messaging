/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.SCKA.MLKEMBraid.Security.Reduction.KEM
import SecureMessaging.SCKA.MLKEMBraid.Security.Reduction.KDF
import SecureMessaging.SCKA.MLKEMBraid.Security.Reduction.Average

/-!
# The KEM and key-derivation reductions

`Reduction.KEM` and `Reduction.KDF` relate the reductions for one fixed epoch to adjacent hybrids.
`Reduction.Average` builds the reductions that draw the epoch uniformly from `{1, …, q}` and
telescopes their gaps over the hybrids.
-/
