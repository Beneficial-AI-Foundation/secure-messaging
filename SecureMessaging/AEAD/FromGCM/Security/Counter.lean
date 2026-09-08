/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.GCM

/-!
# GCM — inc32 and counter-block distinctness

Arithmetic of `GCM.inc32` and pairwise distinctness of the counter blocks
`counterChain` produces from `J₀` (Phase 1 criterion 2), the input-freshness fact
behind idealizing the cipher calls.
-/
