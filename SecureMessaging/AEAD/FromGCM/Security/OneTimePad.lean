/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.GCM
import ToVCVio.OracleComp.Constructions.BitVec

/-!
# GCM — one-time-pad composition for gctr

The rewrite of `GCM.gctr` on distinct counter blocks under an ideal cipher into an
XOR with a uniform keystream, giving one-time-pad confidentiality of the GCTR layer
(Phase 1 criterion 3, GCM-specific half).
-/
