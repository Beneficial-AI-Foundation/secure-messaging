/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromGCM.Construction

/-!
# GCM — cipher-call profile

The exact multiset of cipher inputs made by one-time GCM encryption (Phase 1
criterion 1): the hash-key call `CIPH_K(0¹²⁸)`, the pre-tag call on `J₀`, and the
GCTR counter chain starting at `inc₃₂(J₀)`, all as a function of the message and
AAD lengths.
-/
