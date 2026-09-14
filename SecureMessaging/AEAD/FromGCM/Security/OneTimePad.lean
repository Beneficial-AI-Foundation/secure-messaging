/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import SecureMessaging.AEAD.GCM
import ToVCVio.OracleComp.Constructions.BitVec

/-!
# GCM — GCTR as a one-time pad

`GCM.keystream` coincides with the generic truncated block concatenation
`ToVCVio.blocksToBitVec`, so `gctr` is the message XORed with the concatenated enciphered
counter blocks. The uniformity lemmas about `blocksToBitVec`
(`ToVCVio/OracleComp/Constructions/BitVec.lean`) then make the GCM keystream a one-time pad
in the game hops.
-/

open OracleSpec OracleComp ENNReal ToVCVio

namespace GCM

theorem keystream_eq_blocksToBitVec (blocks : List (BitVec 128)) (p : ℕ) :
    keystream blocks p = blocksToBitVec blocks p :=
  rfl

/-- `gctr ciph k icb x = x ⊕ MSB_p(CIPH_K(CB₁) ‖ CIPH_K(CB₂) ‖ …)` (NIST SP 800-38D §6.5). -/
theorem gctr_eq_xor {K : Type} (ciph : K → BitVec 128 → BitVec 128) (k : K)
    (icb : BitVec 128) {p : ℕ} (x : BitVec p) :
    gctr ciph k icb x =
      x ^^^ blocksToBitVec ((counterChain icb ((p + 127) / 128)).map (ciph k)) p := by
  simp only [gctr, keystream_eq_blocksToBitVec]

end GCM
