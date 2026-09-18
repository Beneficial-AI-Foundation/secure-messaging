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

`GCM.keystream` is a verbatim copy of `blocksToBitVec` bridged here by `rfl` rather than an
`abbrev` for it, so that `AEAD/GCM.lean`, the specification, does not import the `OracleComp`
constructions module.
-/

open OracleSpec OracleComp ENNReal ToVCVio

namespace GCM

theorem keystream_eq_blocksToBitVec (blocks : List (BitVec 128)) (p : ℕ) :
    keystream blocks p = blocksToBitVec blocks p :=
  rfl

end GCM
