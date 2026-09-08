/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.FromGCM.Security.Encoding
import ToVCVio.CryptoFoundations.UniversalHash

/-!
# GCM — GHASH AXU statement over the encoding domain

Instantiation of the generic almost-XOR-universal predicate for `GCM.ghash` over
the GHASH encoding domain, with the concrete `⌈len/128⌉`-style bound (Phase 1
criteria 5–6, GCM-specific half).
-/
