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

`keystream_eq_blocksToBitVec` bridges `GCM.keystream` to the generic
`blocksToBitVec` map, so `gctr_eq_xor` restates `GCM.gctr` as an XOR with a
truncated block concatenation and all downstream reasoning happens through the
generic uniformity brick `probOutput_blocksToBitVec_uniform`.
-/

open OracleSpec OracleComp ENNReal

namespace GCM

/-! ## Bridging `keystream` to the generic concatenation map -/

/-- `GCM.keystream` is the generic truncated big-endian block concatenation
`blocksToBitVec` (the two definitions agree verbatim). Downstream files rewrite
through this bridge instead of unfolding `keystream`. -/
theorem keystream_eq_blocksToBitVec (blocks : List (BitVec 128)) (p : ℕ) :
    keystream blocks p = blocksToBitVec blocks p :=
  rfl

/-- `GCM.gctr` as an XOR with the truncated concatenation of the enciphered
counter blocks: `gctr ciph k icb x = x ^^^ MSB_p(CIPH_K(CB₁) ‖ CIPH_K(CB₂) ‖ …)`,
stated through the generic `blocksToBitVec` map. -/
theorem gctr_eq_xor {K : Type} (ciph : K → BitVec 128 → BitVec 128) (k : K)
    (icb : BitVec 128) {p : ℕ} (x : BitVec p) :
    gctr ciph k icb x =
      x ^^^ blocksToBitVec ((counterChain icb ((p + 127) / 128)).map (ciph k)) p := by
  simp only [gctr, keystream_eq_blocksToBitVec]

end GCM
