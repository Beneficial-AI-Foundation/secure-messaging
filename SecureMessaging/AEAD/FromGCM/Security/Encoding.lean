/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.GCM

/-!
# GCM — GHASH encoding domain and injectivity

The block-sequence encoding `A ‖ 0ᵛ ‖ C ‖ 0ᵘ ‖ len(A) ‖ len(C)` that GCM feeds to
GHASH, and its injectivity on valid (AAD, ciphertext) pairs (Phase 1 criterion 4).
-/
