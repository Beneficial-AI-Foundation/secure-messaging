/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv

/-!
# Invariant preservation for sums and lifted computations

The backports of [VCVio PR #656](https://github.com/Verified-zkEVM/VCVio/pull/656)
(`QueryImpl.PreservesInv.add`, `StateT.statePreserving_monadLift`,
`StateT.preservesInv_monadLift`) are now upstream in
`VCVio.OracleComp.SimSemantics.StateT.PreservesInv`, which this module re-exports.
-/
