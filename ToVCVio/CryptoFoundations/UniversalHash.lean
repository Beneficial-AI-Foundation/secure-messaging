/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.CryptoFoundations.UniversalHash

/-!
# Almost-XOR-universal hash families

The `ε`-almost-XOR-universal (AXU) predicate, its lower bound `1/|T| ≤ ε` and the counting
criterion are upstream in VCVio: `UniversalHash.IsAlmostXorUniversal`,
`UniversalHash.IsAlmostXorUniversal.card_inv_le` and
`UniversalHash.isAlmostXorUniversal_of_card_le`. This module re-exports them.
-/
